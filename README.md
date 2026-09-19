# SpectraWitness

*Exact matrix certificates and verified spectral graph theory in Lean.*

SpectraWitness is an Apache-2.0-licensed Lean 4/mathlib library for exact,
computer-assisted spectral graph theory. It combines real matrix inertia, exact
certificate checkers, graph operations, and finite enumeration results.

The repository is [Aky-lab/spectrawitness](https://github.com/Aky-lab/spectrawitness).
The Lake package name remains `spectral_graph`; Lean imports retain the
`SpectralGraph` namespace. Import `SpectralGraph` for the public library,
or import a narrower module. The principal namespaces are `SpectralGraph`, `SpectralGraph.Inertia`,
`SpectralGraph.Certificate`, `SpectralGraph.Graph`, and `SpectralGraph.Search`.

Start with the [triangle certificate tutorial](examples/tutorial/README.md):
build the package, prove two eigenvalue counts, and see an incorrect claim rejected.

## Main interfaces

- Exact inertia: `Certificate.Basic`, `ProductInertia`, and
  `DenseIntMatrix.checkNormalizedInertia` check rational or integer data and
  prove the corresponding real-matrix inertia.
- Spectral consequences: `Inertia.Spectrum`, `Graph.IntegerSpectrum`,
  `Graph.Independence`, `Graph.PartitionSpectrum`, and `Graph.InducedSpectrum`
  connect checked inertia to eigenvalue, independent-set, compression, and
  interlacing statements.
- Shifted adjacency: `Graph.CliqueUnion` characterizes disjoint unions of
  cliques by positive semidefiniteness of `I + A(G)`. See the
  [six-vertex example](examples/clique_union/README.md).
- Graph reports: [`tools/certify_graph.py`](tools/certify_graph.py) produces
  Lean candidates from strict packed-row JSON; compiling the generated theorem
  is the acceptance step. See [graph reports](examples/graph_reports/README.md).
- Exact graph examples: [cuts](examples/cuts/README.md),
  [Dirichlet response](examples/dirichlet/README.md),
  [Hoffman bounds](examples/hoffman/README.md), and
  [certificate production](examples/producer/README.md).

## Exact certificates

```lean
import SpectralGraph.Certificate.Basic
open SpectralGraph SpectralGraph.Certificate

def A : Matrix (Fin 2) (Fin 2) â„š := !![0, 1; 1, 0]
def cert : InertiaCertificate (Fin 2) where
  change := !![1, 1; 1, -1]
  inverse := !![1 / 2, 1 / 2; 1 / 2, -1 / 2]
  target := âŸ¨1, 0, 1âŸ©

example : matrixInertia (ratCastMatrix A) = âŸ¨1, 0, 1âŸ© :=
  cert.sound A (by decide +kernel)
```

The producer supplies untrusted rational data. Lean checks the matrix identities,
diagonal signs, and declared inertia before applying a soundness theorem. Exact
integer checkers similarly reject malformed storage and certify rational shifts.

## Build and validation

The checked metadata pins Lean `4.30.0` and mathlib revision
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.

From the package root, obtain the dependencies specified by `lake-manifest.json`
and use the ordinary Lake commands:

```text
lake exe cache get
lake build
```

For a controlled local compilation, provide explicit Lean and dependency paths:

```text
python validate_local.py --lean PATH_TO_LEAN --packages PATH_TO_EXISTING_LAKE_PACKAGES --output-dir .validation-run
```

The validator and Python tools require only the standard library. Python 3.12.10
on Windows was used for the recorded local tool checks. `VALIDATION.md` describes the
current validation boundary; `BENCHMARKS.md` describes performance experiments.

The ordinary commands above were also checked on Windows with the installed
Lean/Lake 4.30.0 toolchain in a fresh package directory. Lake cloned all nine
dependencies at the revisions in `lake-manifest.json`, downloaded mathlib's
precompiled cache, and built both default targets (`SpectralGraph` and
`SpectralGraphTests`). A separate `lake env lean` consumer then compiled the
two-by-two certificate shown above and imported the public clique-union
characterization. This checks the fixed-manifest package route; it is not a
fresh toolchain installation or a source build of all dependencies.

## Trust and release status

Library proofs and regression checks use kernel checking without added axioms or
proof holes; standard Lean and mathlib axioms remain part of the trusted base.
Native benchmark execution and Python generation are not proofs. Matrix spectral
interpretations require the symmetry hypotheses stated by each theorem.

This is pre-release software. The distributed Lean declarations and proofs
match the checked source snapshot; the current Trust inspection module has
identical commands and differs only in comment text. That direct source build
used the existing pinned dependency cache. A later isolated ordinary Lake run
verified fresh fixed-revision dependency checkout, downloaded dependency-cache
use, both default targets, and a user import consumer on Windows.

## License and attribution

Copyright 2026 Aky-lab. The package is licensed under the Apache License 2.0;
see [LICENSE](LICENSE) and [NOTICE](NOTICE).
`RIGHTS.md` describes the package licensing scope and the factual development
disclosure. `THIRD_PARTY_NOTICES.md` lists pinned dependencies and explains the
source-export boundary. The `PROVENANCE*.json` records retain documentary source
identities and adaptation scopes.
