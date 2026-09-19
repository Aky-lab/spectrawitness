# Benchmarks

Performance measurements are experiments, not proof evidence. Native execution,
Lean startup, import work, elaboration, and kernel checking have different costs;
reports must identify which costs they include.

The package contains bounded experiments for graph enumeration and exact
certificate checking. They use deterministic inputs and explicit time caps. A
successful bounded run establishes only the measured workload on its recorded
environment; it does not establish asymptotic complexity, peak-memory bounds,
or performance on other graphs or matrices.

Run a benchmark only with explicit paths to the intended Lean executable and
existing dependency packages, for example:

```text
python tools/benchmark.py --lean PATH_TO_LEAN --packages PATH_TO_EXISTING_LAKE_PACKAGES
```

Keep raw host-specific results outside a source distribution. A portable summary
must state its input family, method, caps, source identity, and limitations.
Certificate producers remain untrusted even when their output is fast: the
compiled Lean acceptance theorem is the mathematical boundary.
