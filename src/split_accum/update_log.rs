//! Sample update log implementation for the split bilinear accumulator.

use std::fs::{File, OpenOptions};
use std::io::{BufReader, BufWriter, Read, Write};
use std::path::Path;

use bls12_381_plus::{G1Affine, G2Affine};

use crate::batch_update::BatchRemoval;
use crate::{AccumulatorError, EpochType, IndexType};

use super::{PartitionPrivate, PartitionSignature, SignedMembershipWitness, SplitRegistryPublic};

const UPDATE_EPOCH: u8 = 1;
const UPDATE_REMOVE: u8 = 2;
const REMOVE_ENTRY_LEN: usize = 52;
const SIGNATURE_LEN: usize = 148;

/// This structure implements a basic update log, which serializes epoch
/// updates and batch removal operations in a compressed binary format.
///
/// NB: This could be optimized by only outputting 'g2accum' when a
/// partition has actually been updated.
pub struct SplitRegistryUpdateLog(BufWriter<File>);

impl SplitRegistryUpdateLog {
    /// Initialize a new update log.
    pub fn create(
        path: impl AsRef<Path>,
        registry: &SplitRegistryPublic,
        partitions: &[PartitionPrivate],
    ) -> Result<Self, AccumulatorError> {
        let outfile = BufWriter::new(File::create(path)?);
        let mut slf = Self(outfile);
        slf.write_epoch(registry, partitions)?;
        Ok(slf)
    }

    /// Start appending to an update log.
    pub fn append(path: impl AsRef<Path>) -> Result<Self, AccumulatorError> {
        let outfile = BufWriter::new(OpenOptions::new().append(true).open(path)?);
        Ok(Self(outfile))
    }

    /// Write an epoch update record.
    pub fn write_epoch(
        &mut self,
        registry: &SplitRegistryPublic,
        partitions: &[PartitionPrivate],
    ) -> Result<(), AccumulatorError> {
        let epoch = registry.epoch;
        assert!(epoch as usize <= u32::MAX as usize);
        let count = partitions
            .iter()
            .filter(|p| p.signature.epoch == epoch)
            .count();
        assert!(count as usize <= u32::MAX as usize);
        // FIXME return an error if an invalid epoch is written
        self.0.write(&[UPDATE_EPOCH])?;
        self.0.write(&(epoch as u32).to_le_bytes())?;
        self.0.write(&(count as u32).to_le_bytes())?;
        for part in partitions {
            let sig = &part.signature;
            if sig.epoch != epoch {
                continue;
            }
            let index = sig.index as usize;
            assert!(index <= u32::MAX as usize);
            // FIXME check signature epoch matches registry epoch
            self.0.write(&(index as u32).to_le_bytes())?;
            self.0.write(&sig.g2accum.to_compressed())?;
            self.0.write(&sig.signature.to_compressed())?;
        }
        Ok(())
    }

    /// Write a batch removal record.
    pub fn write_removals(&mut self, updates: &[BatchRemoval]) -> Result<(), AccumulatorError> {
        assert!(updates.len() <= u32::MAX as usize);
        self.0.write(&[UPDATE_REMOVE])?;
        self.0.write(&(updates.len() as u32).to_le_bytes())?;
        for update in updates {
            let index = update.partition as usize;
            assert!(index <= u32::MAX as usize);
            assert!(update.values.len() <= u32::MAX as usize);
            self.0.write(&(index as u32).to_le_bytes())?;
            self.0.write(&(update.values.len() as u32).to_le_bytes())?;
            for (idx, pt) in update.values.iter().copied() {
                assert!(idx as usize <= u32::MAX as usize);
                self.0.write(&pt.to_compressed())?;
                self.0.write(&(idx as u32).to_le_bytes())?;
            }
        }
        Ok(())
    }

    /// Finalize a log update, flushing to the disk.
    pub fn finalize(mut self) -> Result<(), AccumulatorError> {
        self.0.flush()?;
        Ok(())
    }

    /// Update a membership witness from the log file.
    pub fn update_membership_witness(
        path: impl AsRef<Path>,
        registry: &SplitRegistryPublic,
        witness: &SignedMembershipWitness,
    ) -> Result<SignedMembershipWitness, AccumulatorError> {
        let mut infile = BufReader::new(File::open(path)?);
        let mut ver = [0u8];
        let mut len_buf = [0u8; 4];
        let mut g1_buf = [0u8; 48];
        let mut sig_buf = [0u8; SIGNATURE_LEN];
        let mut latest_epoch: Option<(u32, [u8; SIGNATURE_LEN])> = None;
        let mut update = witness.begin_update();
        let mut batch = BatchRemoval {
            values: vec![],
            partition: 0,
        };
        loop {
            let len = infile.read(&mut ver)?;
            if len == 0 {
                // acceptable EOF
                break;
            }
            match ver[0] {
                UPDATE_EPOCH => {
                    infile.read_exact(&mut len_buf)?;
                    let epoch = u32::from_le_bytes(len_buf) as EpochType;
                    infile.read_exact(&mut len_buf)?;
                    let count = u32::from_le_bytes(len_buf) as usize;
                    let mut next_epoch = None;
                    for _ in 0..count {
                        infile.read_exact(&mut sig_buf)?;
                        len_buf.copy_from_slice(&sig_buf[..4]);
                        if u32::from_le_bytes(len_buf) as IndexType == update.partition() {
                            next_epoch = Some((epoch, sig_buf));
                        }
                    }
                    let Some(epoch) = next_epoch else {
                        return Err(AccumulatorError::MemberRemoved);
                    };
                    if latest_epoch.map(|prev| epoch.0 <= prev.0).unwrap_or(false) {
                        // epoch must be increasing
                        return Err(AccumulatorError::InvalidLog);
                    }
                    latest_epoch = Some(epoch);
                }
                UPDATE_REMOVE => {
                    infile.read_exact(&mut len_buf)?;
                    let updates = u32::from_le_bytes(len_buf) as usize;
                    for _ in 0..updates {
                        infile.read_exact(&mut len_buf)?;
                        let index = u32::from_le_bytes(len_buf) as IndexType;
                        infile.read_exact(&mut len_buf)?;
                        let count = u32::from_le_bytes(len_buf) as usize;
                        if index == update.partition()
                            && latest_epoch
                                .map(|e| e.0 >= update.start_epoch())
                                .unwrap_or(false)
                        {
                            // parse and apply if from a later epoch
                            batch.values.clear();
                            for _ in 0..count {
                                infile.read_exact(&mut g1_buf)?;
                                infile.read_exact(&mut len_buf)?;
                                let Some(pt) = G1Affine::from_compressed(&g1_buf).into_option()
                                else {
                                    return Err(AccumulatorError::InvalidLog);
                                };
                                let idx = u32::from_le_bytes(len_buf);
                                batch.values.push((idx as IndexType, pt));
                            }
                            update.apply_batch_removal(&batch)?;
                        } else {
                            infile.seek_relative((count * REMOVE_ENTRY_LEN) as i64)?;
                        }
                    }
                }
                _ => {
                    return Err(AccumulatorError::InvalidLog);
                }
            }
        }
        let Some((epoch, sig)) = latest_epoch else {
            return Err(AccumulatorError::MemberRemoved);
        };
        // FIXME update only as far as the registry epoch?
        let mut reg = registry.clone();
        reg.epoch = epoch;
        let sig = {
            let mut g2_buf = [0u8; 96];
            g2_buf.copy_from_slice(&sig[4..100]);
            g1_buf.copy_from_slice(&sig[100..]);
            let Some(g2accum) = G2Affine::from_compressed(&g2_buf).into_option() else {
                return Err(AccumulatorError::InvalidLog);
            };
            let Some(signature) = G1Affine::from_compressed(&g1_buf).into_option() else {
                return Err(AccumulatorError::InvalidLog);
            };
            let accum = if batch.is_empty() {
                witness.partition.accum
            } else {
                batch.accumulator()
            };
            PartitionSignature {
                accum,
                g2accum,
                signature,
                epoch,
                index: update.partition(),
            }
        };
        let witness = update.finalize_signed(&reg, sig)?;
        Ok(witness)
    }
}

#[cfg(test)]
mod tests {
    use super::SplitRegistryUpdateLog;
    use crate::split_accum::new_split_registry;

    #[test]
    fn update_log() {
        let mut rng = rand::thread_rng();
        let capacity = 16384;
        let partition_size = 1024;
        let epoch0 = 0;
        let (sk, pk, mut accums) = new_split_registry(capacity, partition_size, epoch0, &mut rng);
        let witness1 = sk.create_membership_witness(&accums[0], 1).unwrap();
        let witness2 = sk.create_membership_witness(&accums[0], 2).unwrap();
        pk.verify_membership_witness(&witness1)
            .expect("Error verifying witness");

        let temp_dir = tempfile::TempDir::new().unwrap();
        let mut temp_file = temp_dir.into_path();
        temp_file.push("update_log");
        SplitRegistryUpdateLog::create(&temp_file, &pk, &accums)
            .unwrap()
            .finalize()
            .unwrap();

        // remove a batch
        let epoch1 = 1;
        let mut sk1 = sk.clone();
        let batch1 = sk1
            .remove_partition_members(&mut accums[0], [2, 3])
            .expect("Error removing members");
        sk1.set_epoch(epoch1);
        sk1.batch_sign_partitions(&mut accums);
        let pk1 = sk1.to_public();
        // should not be valid against new state
        assert!(witness1
            .begin_update()
            .finalize_signed(&pk1, accums[0].signature())
            .is_err());
        // update the log
        let mut upd1 = SplitRegistryUpdateLog::append(&temp_file).unwrap();
        upd1.write_removals(&[batch1]).unwrap();
        upd1.write_epoch(&pk1, &accums).unwrap();
        upd1.finalize().unwrap();

        // update witness for non-removed member
        let upd_witness1 =
            SplitRegistryUpdateLog::update_membership_witness(&temp_file, &pk1, &witness1).unwrap();
        assert!(pk1.verify_membership_witness(&upd_witness1).is_ok());
        // check a removed witness is not updated
        let res_upd =
            SplitRegistryUpdateLog::update_membership_witness(&temp_file, &pk1, &witness2);
        assert!(res_upd.is_err(), "update should fail");

        // remove another batch
        let epoch2 = 2;
        let mut sk2 = sk1.clone();
        // ^ FIXME no error raised if starting from the wrong accumulator
        let batch2 = sk2
            .remove_partition_members(&mut accums[0], [4, 5, 6])
            .expect("Error removing members");
        sk2.set_epoch(epoch2);
        sk2.batch_sign_partitions(&mut accums);
        let pk2 = sk2.to_public();
        // update the log
        let mut upd2 = SplitRegistryUpdateLog::append(&temp_file).unwrap();
        upd2.write_removals(&[batch2]).unwrap();
        upd2.write_epoch(&pk2, &accums).unwrap();
        upd2.finalize().unwrap();

        // update previously-updated witness
        let upd_witness2 =
            SplitRegistryUpdateLog::update_membership_witness(&temp_file, &pk2, &upd_witness1)
                .unwrap();
        assert!(pk2.verify_membership_witness(&upd_witness2).is_ok());
        // update original witness
        let upd_witness2 =
            SplitRegistryUpdateLog::update_membership_witness(&temp_file, &pk2, &witness1).unwrap();
        assert!(pk2.verify_membership_witness(&upd_witness2).is_ok());
        // update again from the same log
        let upd_witness3 =
            SplitRegistryUpdateLog::update_membership_witness(&temp_file, &pk2, &upd_witness2)
                .unwrap();
        assert!(pk2.verify_membership_witness(&upd_witness3).is_ok());
    }
}
