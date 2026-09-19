# Roadmap

## Implemented foundations

- Real quadratic-form inertia, congruence, restriction, Schur, and shifted-Gram
  interfaces.
- Exact rational and integer certificate checkers, strict JSON producers, and
  kernel-checked rejection cases.
- Spectral interval, interlacing, partition, graph-cut, Hoffman, and
  independent-set consequences.
- Degree-bounded graph generation, checked isomorphism reductions, and exact
  batch-coverage interfaces.

## Engineering and research priorities

1. Obtain external mathematical review of assumptions and overlap with mathlib.
2. Measure broader certificate and sparse-input workloads while retaining exact
   inputs, failures, and environment limits.
3. Improve exhaustive-search workflows only with explicit coverage proofs and
   clearly bounded resource claims.
4. Develop additional independently useful graph applications.
5. Preserve license, third-party notice, and provenance coverage as the public
   API and dependency set evolve.

The package remains pre-release. Performance measurements do not prove scalable
behavior, and existing validation evidence is not a substitute for a fresh
exported-source validation run.
