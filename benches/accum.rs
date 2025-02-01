use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::thread_rng;

use split_accum::accum;

const SAMPLES: usize = 50;

fn bench_accum(c: &mut Criterion) {
    let mut group = c.benchmark_group("accumulator");

    let rng = thread_rng();
    let config = accum::Config {
        partition_size: 1024,
        capacity: 1024,
    };
    let (sk, _pk) = accum::setup(&config, rng);
    let accums = accum::init(&config, &sk);

    for count in [10, 100, 1000] {
        group.bench_function(BenchmarkId::new("batch update accumulator", count), |b| {
            b.iter(|| {
                let (_accum, update) = accums[0].batch_remove(
                    &sk,
                    (0..count).map(|index| accum::MemberHandle::compute_for_index(&config, index)),
                );
                black_box(update)
            })
        });
    }

    let witness =
        accums[0].create_witness(&sk, accum::MemberHandle::compute_for_index(&config, 1023));
    for count in [10, 100, 1000] {
        group.bench_function(BenchmarkId::new("batch update witness", count), |b| {
            b.iter_batched(
                || {
                    let (_accum, update) = accums[0].batch_remove(
                        &sk,
                        (0..count)
                            .map(|index| accum::MemberHandle::compute_for_index(&config, index)),
                    );
                    update
                },
                |batch| black_box(witness.update_batch_removal(&batch)),
                criterion::BatchSize::SmallInput,
            )
        });
    }
}

criterion_group!(
    name=benches;
    config=Criterion::default().sample_size(SAMPLES);
    targets=bench_accum
);
criterion_main!(benches);
