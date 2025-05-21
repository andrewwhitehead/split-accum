//! Sample update log implementation for the bilinear accumulator.

use std::fs::{File, OpenOptions};
use std::io::{BufReader, BufWriter, Read, Write};
use std::path::Path;

use bls12_381_plus::G1Affine;

use crate::batch_update::BatchRemoval;
use crate::{AccumulatorError, EpochType, IndexType};

use super::{MembershipWitness, RegistryPublic};

const UPDATE_EPOCH: u8 = 1;
const UPDATE_REMOVE: u8 = 2;
const REMOVE_ENTRY_LEN: usize = 52;

/// This structure implements a basic update log, which serializes epoch
/// updates and batch removal operations in a compressed binary format.
pub struct RegistryUpdateLog(BufWriter<File>);

impl RegistryUpdateLog {
    /// Initialize a new update log.
    pub fn create(
        path: impl AsRef<Path>,
        registry: &RegistryPublic,
    ) -> Result<Self, AccumulatorError> {
        let outfile = BufWriter::new(File::create(path)?);
        let mut slf = Self(outfile);
        slf.write_epoch(registry)?;
        Ok(slf)
    }

    /// Start appending to an update log.
    pub fn append(path: impl AsRef<Path>) -> Result<Self, AccumulatorError> {
        let outfile = BufWriter::new(OpenOptions::new().append(true).open(path)?);
        Ok(Self(outfile))
    }

    /// Write an epoch update record.
    pub fn write_epoch(&mut self, registry: &RegistryPublic) -> Result<(), AccumulatorError> {
        let epoch = registry.epoch;
        assert!(epoch as usize <= u32::MAX as usize);
        // FIXME return an error if an invalid epoch is written
        self.0.write(&[UPDATE_EPOCH])?;
        self.0.write(&(epoch as u32).to_le_bytes())?;
        Ok(())
    }

    /// Write a batch removal record.
    pub fn write_removal(&mut self, update: &BatchRemoval) -> Result<(), AccumulatorError> {
        assert!(update.values.len() <= u32::MAX as usize);
        let count = update.values.len() as u32;
        self.0.write(&[UPDATE_REMOVE])?;
        self.0.write(&count.to_le_bytes())?;
        for (idx, pt) in update.values.iter().copied() {
            assert!(idx as usize <= u32::MAX as usize);
            self.0.write(&pt.to_compressed())?;
            self.0.write(&(idx as u32).to_le_bytes())?;
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
        registry: &RegistryPublic,
        witness: &MembershipWitness,
    ) -> Result<MembershipWitness, AccumulatorError> {
        let mut infile = BufReader::new(File::open(path)?);
        let mut ver = [0u8];
        let mut len_buf = [0u8; 4];
        let mut pt_buf = [0u8; 48];
        let mut latest_epoch = None;
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
                    if latest_epoch.map(|prev| epoch <= prev).unwrap_or(false) {
                        // epoch must be increasing
                        return Err(AccumulatorError::InvalidLog);
                    }
                    latest_epoch = Some(epoch);
                }
                UPDATE_REMOVE => {
                    infile.read_exact(&mut len_buf)?;
                    let count = u32::from_le_bytes(len_buf) as usize;
                    if latest_epoch.map(|e| e >= witness.epoch).unwrap_or(false) {
                        // parse and apply if from a later epoch
                        batch.values.clear();
                        for _ in 0..count {
                            infile.read_exact(&mut pt_buf)?;
                            infile.read_exact(&mut len_buf)?;
                            let Some(pt) = G1Affine::from_compressed(&pt_buf).into_option() else {
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
                _ => {
                    return Err(AccumulatorError::InvalidLog);
                }
            }
        }
        let Some(epoch) = latest_epoch else {
            return Err(AccumulatorError::InvalidLog);
        };
        let mut reg = registry.clone();
        reg.epoch = epoch;
        let witness = update.finalize_unsigned(&reg)?;
        Ok(witness)
    }
}

#[cfg(test)]
mod tests {
    use super::RegistryUpdateLog;
    use crate::accum::new_registry;

    #[test]
    fn update_log() {
        let mut rng = rand::thread_rng();
        let capacity = 16384;
        let epoch0 = 0;
        let (sk, pk) = new_registry(capacity, epoch0, &mut rng);
        let witness1 = sk.create_membership_witness(1).unwrap();
        let witness2 = sk.create_membership_witness(2).unwrap();
        pk.verify_membership_witness(&witness1)
            .expect("Error verifying witness");

        let temp_dir = tempfile::TempDir::new().unwrap();
        let mut temp_file = temp_dir.into_path();
        temp_file.push("update_log");
        RegistryUpdateLog::create(&temp_file, &pk)
            .unwrap()
            .finalize()
            .unwrap();

        // remove a batch
        let epoch1 = 1;
        let mut accum1 = sk.clone();
        let batch1 = accum1
            .remove_members([2, 3])
            .expect("Error removing members");
        accum1.set_epoch(epoch1);
        let pk1 = accum1.to_public();
        // should not be valid against new state
        assert!(witness1.begin_update().finalize_unsigned(&pk1).is_err());
        // update the log
        let mut upd1 = RegistryUpdateLog::append(&temp_file).unwrap();
        upd1.write_removal(&batch1).unwrap();
        upd1.write_epoch(&pk1).unwrap();
        upd1.finalize().unwrap();

        // update witness for non-removed member
        let upd_witness1 =
            RegistryUpdateLog::update_membership_witness(&temp_file, &pk1, &witness1).unwrap();
        assert!(pk1.verify_membership_witness(&upd_witness1).is_ok());
        // check a removed witness is not updated
        let res_upd = RegistryUpdateLog::update_membership_witness(&temp_file, &pk1, &witness2);
        assert!(res_upd.is_err(), "update should fail");

        // remove another batch
        let epoch2 = 2;
        let mut accum2 = accum1.clone();
        // ^ FIXME no error raised if starting from the wrong accumulator
        let batch2 = accum2
            .remove_members([4, 5, 6])
            .expect("Error removing members");
        accum2.set_epoch(epoch2);
        let pk2 = accum2.to_public();
        // update the log
        let mut upd2 = RegistryUpdateLog::append(&temp_file).unwrap();
        upd2.write_removal(&batch2).unwrap();
        upd2.write_epoch(&pk2).unwrap();
        upd2.finalize().unwrap();

        // update previously-updated witness
        let upd_witness2 =
            RegistryUpdateLog::update_membership_witness(&temp_file, &pk2, &upd_witness1).unwrap();
        assert!(pk2.verify_membership_witness(&upd_witness2).is_ok());
        // update original witness
        let upd_witness2 =
            RegistryUpdateLog::update_membership_witness(&temp_file, &pk2, &witness1).unwrap();
        assert!(pk2.verify_membership_witness(&upd_witness2).is_ok());
        // update again from the same log
        let upd_witness3 =
            RegistryUpdateLog::update_membership_witness(&temp_file, &pk2, &upd_witness2).unwrap();
        assert!(pk2.verify_membership_witness(&upd_witness3).is_ok());
    }
}
