use codspeed_criterion_compat::{criterion_group, criterion_main, Criterion};
use glob_match::*;

fn simple_expansion(c: &mut Criterion) {
  let mut group = c.benchmark_group("simple_expansion");

  const GLOB: &'static str = "some/**/n*d[k-m]e?txt";
  const PATH: &'static str = "some/a/bigger/path/to/the/crazy/needle.txt";

  group.bench_function("mine", |b| {
    let pattern = Pattern::new(GLOB);
    b.iter(|| assert!(pattern.matches(PATH)))
  });

  group.bench_function("fast-glob normal", |b| {
    b.iter(|| assert!(fast_glob::glob_match(GLOB, PATH)))
  });

  group.bench_function("fast-glob", |b| {
    b.iter(|| assert!(fast_glob::glob_match_with_brace(GLOB, PATH)))
  });

  group.bench_function("glob-match", |b| {
    b.iter(|| assert!(origin_glob_match::glob_match(GLOB, PATH)))
  });

  group.finish();
}

fn brace_expansion(c: &mut Criterion) {
  let mut group = c.benchmark_group("brace_expansion");

  const GLOB: &'static str = "some/**/{tob,crazy}/?*.{png,txt}";
  const PATH: &'static str = "some/a/bigger/path/to/the/crazy/needle.txt";

  group.bench_function("mine", |b| {
    let pattern = Pattern::new(GLOB);
    b.iter(|| assert!(pattern.matches(PATH)))
  });

  group.bench_function("fast-glob", |b| {
    b.iter(|| assert!(fast_glob::glob_match_with_brace(GLOB, PATH)));
  });

  group.bench_function("glob-match", |b| {
    b.iter(|| assert!(origin_glob_match::glob_match(GLOB, PATH)))
  });

  group.finish();
}

criterion_group!(benches, simple_expansion, brace_expansion);
criterion_main!(benches);
