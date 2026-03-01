// SPDX-FileCopyrightText: 2025 László Vaskó <opensource@vlaci.email>
// SPDX-License-Identifier: EUPL-1.2

use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("fnmatch", |b| {
        b.iter(|| {
            globlin::glob_match(
                black_box("foo/**/{*a,*b}/foo/**/{*a,*b}/foo/**/{*a,*b}/foo/**/{*a,*b}/foo/**/{*a,*b}/foo/**/{*a,*b}/foo/**/{*a,*b}/foo/**/{*a,*b}/foo/**/{*a,*b}/foo/**/{*a,*b}/foo/**/{*a,*b}"),
                black_box("foo/b/c/d/a/foo/b/c/d/a/foo/b/c/d/a/foo/b/c/d/a/foo/b/c/d/a/foo/b/c/d/a/foo/b/c/d/a/foo/b/c/d/a/foo/b/c/d/a/foo/b/c/d/a/foo/b/c/d/a"),
                globlin::flags::DEFAULT,
            )
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
