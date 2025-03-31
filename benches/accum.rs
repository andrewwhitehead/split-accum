use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::thread_rng;

const SAMPLES: usize = 50;
const BATCHES: &[u32] = &[10, 100, 1000];

fn bench_accum(c: &mut Criterion) {
    let mut group = c.benchmark_group("accumulator");

    let capacity = 1000_000;
    let epoch0 = 0;
    let (sk, pk) = split_accum::new_registry(capacity, epoch0, &mut thread_rng());

    for count in BATCHES.iter().copied() {
        group.bench_function(BenchmarkId::new("remove members", count), |b| {
            b.iter_batched(
                || sk.clone(),
                |mut accum| {
                    let update = accum
                        .remove_members(1..=count)
                        .expect("Error removing members");
                    black_box(update)
                },
                criterion::BatchSize::SmallInput,
            )
        });
    }

    group.bench_function("create membership witness", |b| {
        b.iter(|| {
            let witness = sk.create_membership_witness(1);
            black_box(witness)
        })
    });

    let witness = sk.create_membership_witness(1000).unwrap();
    for count in BATCHES.iter().copied() {
        let mut accum = sk.clone();
        let batch = accum
            .remove_members(1..count)
            .expect("Error removing members");
        let pk2 = accum.to_public();
        group.bench_function(
            BenchmarkId::new("apply batch removal to membership witness", count),
            |b| {
                b.iter(|| {
                    let mut update = witness.begin_update();
                    update.apply_batch_removal(&batch).unwrap();
                    black_box(update.finalize_unsigned(&pk2).unwrap());
                })
            },
        );
    }

    group.bench_function("create membership proof", |b| {
        b.iter(|| {
            let prepare = witness.prepare_proof(&pk, &mut thread_rng()).unwrap();
            let challenge = prepare.compute_challenge();
            black_box(prepare.finalize(&challenge));
        })
    });

    let prepare = witness.prepare_proof(&pk, &mut thread_rng()).unwrap();
    let challenge = prepare.compute_challenge();
    let proof = prepare.finalize(&challenge);
    group.bench_function("verify membership proof", |b| {
        b.iter(|| proof.verify(&pk, &challenge).unwrap())
    });
}

fn bench_split_accum(c: &mut Criterion) {
    let mut group = c.benchmark_group("split accumulator");

    let capacity = 1000_000;
    let partition_size = 1000;
    let epoch0 = 0;
    let epoch1 = 1;
    let (sk, pk, accums) =
        split_accum::new_split_registry(capacity, partition_size, epoch0, &mut thread_rng());

    for count in BATCHES.iter().copied() {
        group.bench_function(BenchmarkId::new("remove partition members", count), |b| {
            b.iter_batched(
                || accums[0].clone(),
                |mut accum| {
                    let update = sk
                        .remove_partition_members(&mut accum, 1..=count)
                        .expect("Error removing members");
                    black_box(update)
                },
                criterion::BatchSize::SmallInput,
            )
        });
    }

    for count in BATCHES.iter().copied() {
        group.bench_function(BenchmarkId::new("batch sign partitions", count), |b| {
            b.iter_batched(
                || accums.clone(),
                |mut accs| {
                    let sigs = sk.batch_sign_partitions(&mut accs[..(count as usize)], epoch0);
                    black_box(sigs)
                },
                criterion::BatchSize::LargeInput,
            )
        });
    }

    group.bench_function("create membership witness", |b| {
        b.iter(|| {
            let witness = sk.create_membership_witness(&accums[0], 1);
            black_box(witness)
        })
    });

    let witness = sk.create_membership_witness(&accums[0], 1000).unwrap();
    for count in BATCHES.iter().copied() {
        let mut accum = accums[0].clone();
        let batch = sk
            .remove_partition_members(&mut accum, 1..count)
            .expect("Error removing members");
        sk.sign_partition(&mut accum, epoch1);
        group.bench_function(
            BenchmarkId::new("apply batch removal to membership witness", count),
            |b| {
                b.iter(|| {
                    let mut update = witness.begin_update();
                    update.apply_batch_removal(&batch).unwrap();
                    black_box(update.finalize_signed(&pk, accum.signature()).unwrap());
                })
            },
        );
    }

    group.bench_function("create membership proof", |b| {
        b.iter(|| {
            let prepare = witness.prepare_proof(&pk, &mut thread_rng()).unwrap();
            let challenge = prepare.compute_challenge();
            black_box(prepare.finalize(&challenge));
        })
    });

    let prepare = witness.prepare_proof(&pk, &mut thread_rng()).unwrap();
    let challenge = prepare.compute_challenge();
    let proof = prepare.finalize(&challenge);
    group.bench_function("verify membership proof", |b| {
        b.iter(|| proof.verify(&pk, &challenge).unwrap())
    });
}

criterion_group!(
    name=benches;
    config=Criterion::default().sample_size(SAMPLES);
    targets=bench_accum,bench_split_accum
);
criterion_main!(benches);
