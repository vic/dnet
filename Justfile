help:
  @just -l

fmt:
  @cargo fmt

ci:
  @cargo fmt --check
  @cargo clippy
  @just test
  @just oracle

docs:
  cd docs && pnpm run dev

docs-build:
  cd docs && pnpm run build

test:
  @cargo test

oracle:
  @cargo test --test oracle -- --include-ignored
  @cargo test -p dnx-sched --test parallel_equiv -- --include-ignored
  @cargo test -p dnx-sched --test whnf_oracle -- --include-ignored
  @cargo test -p dnx-read --test oracle -- --include-ignored

# The import-tree gate: run a nix-unit-style suite through dnx's PARALLEL runner.
# Defaults to the runnable slice (the upstream ~/hk/import-tree/tests.nix needs
# features outside the eval subset — see vic/notes/import-tree-gate-results.md).
test-nix FILE='crates/dnx-test/tests/fixtures/import-tree-slice.nix':
  @cargo run -q -p dnx -- test {{FILE}}

# The speedup + never-recompute demo: sequential baseline, then parallel, then a
# re-run where every case is a 0-interaction cache HIT (design §9).
test-nix-demo FILE='crates/dnx-test/tests/fixtures/import-tree-slice.nix':
  @cargo run -q -p dnx -- test --jobs 1 {{FILE}}
  @cargo run -q -p dnx -- test {{FILE}}
  @cargo run -q -p dnx -- test {{FILE}}

gpu-oracle:
  @cargo test -p dnx-gpu --test oracle -- --include-ignored

gpu-bench:
  @cargo bench -p dnx-gpu --bench reduction

