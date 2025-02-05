use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::thread_rng;

use split_accum::common;
use split_accum::manager;

const SAMPLES: usize = 50;
const BATCHES: &[u32] = &[10, 100, 1000];

fn bench_accum(c: &mut Criterion) {
    let mut group = c.benchmark_group("accumulator");

    let config = manager::Config {
        partition_size: 1000,
        capacity: 1000_000,
    };
    let (sk, pk) = manager::create_keys(&config, thread_rng());
    let accums = manager::initialize(&config, &sk);
    let epoch0 = 0;
    let epoch1 = 1;

    for count in BATCHES.iter().copied() {
        group.bench_function(BenchmarkId::new("remove partition members", count), |b| {
            b.iter(|| {
                let (_accum, update) = sk
                    .remove_partition_members(
                        &accums[0],
                        (1..=count).map(|index| {
                            common::MemberHandle::compute_for_index(&config, index).unwrap()
                        }),
                    )
                    .expect("Error removing members");
                black_box(update)
            })
        });
    }

    for count in BATCHES.iter().copied() {
        group.bench_function(BenchmarkId::new("batch sign partitions", count), |b| {
            b.iter(|| {
                let sigs = sk.batch_sign_partitions(&accums[..(count as usize)], epoch0);
                black_box(sigs)
            })
        });
    }

    let signed1 = sk.sign_partition(&accums[0], epoch0);
    let member1 = common::MemberHandle::compute_for_index(&config, 1).unwrap();
    group.bench_function("create membership witness", |b| {
        b.iter(|| {
            let witness = sk.create_membership_witness(&signed1, member1);
            black_box(witness)
        })
    });

    let witness = sk
        .create_membership_witness(
            &signed1,
            common::MemberHandle::compute_for_index(&config, 1000).unwrap(),
        )
        .unwrap();
    for count in BATCHES.iter().copied() {
        let (accum2, batch) = sk
            .remove_partition_members(
                &accums[0],
                (1..count)
                    .map(|index| common::MemberHandle::compute_for_index(&config, index).unwrap()),
            )
            .expect("Error removing members");
        let signed2 = sk.sign_partition(&accum2, epoch1);
        group.bench_function(
            BenchmarkId::new("apply batch removal to membership witness", count),
            |b| {
                b.iter(|| {
                    let mut update = witness.begin_update();
                    update.apply_batch_removal(&batch).unwrap();
                    black_box(update.finalize_with_signature(&pk, &signed2).unwrap());
                })
            },
        );
    }

    group.bench_function("create membership proof", |b| {
        b.iter(|| {
            let prepare = witness.prepare_proof(&pk, thread_rng()).unwrap();
            let challenge = prepare.compute_challenge();
            black_box(prepare.finalize(&challenge));
        })
    });

    let prepare = witness.prepare_proof(&pk, thread_rng()).unwrap();
    let challenge = prepare.compute_challenge();
    let proof = prepare.finalize(&challenge);
    group.bench_function("verify membership proof", |b| {
        b.iter(|| proof.verify(&pk, &challenge).unwrap())
    });
}

criterion_group!(
    name=benches;
    config=Criterion::default().sample_size(SAMPLES);
    targets=bench_accum
);
criterion_main!(benches);
