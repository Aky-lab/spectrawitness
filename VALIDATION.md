# Validation and trust guide

Validation has three separate roles: Lean compilation checks declarations and
proofs against the pinned environment; `Validation/Axioms.lean` inspects the
public declaration environment; and Python tools validate portable input,
report, and source-identity contracts. None establishes performance, license
compliance, or publication readiness.

## Reproduce a local check

Use Lean `4.30.0`, the checked `lake-manifest.json`, and explicit existing
dependency and executable paths:

```text
python validate_local.py --lean PATH_TO_LEAN --packages PATH_TO_EXISTING_LAKE_PACKAGES --output-dir .validation-run
python tools/audit.py --trust-log .validation-run/SpectralGraphTests.Trust.log --report .validation-run/report.json
python -m unittest discover -s tools -p "test_*.py"
```

The output directory must be fresh and package-local. The validator records
source identity and direct exits; a nonzero exit, timeout, crash, or relevant
proof error is a failure. Python 3.12.10 on Windows was used for the recorded
local tool checks. The tools use the Python standard library.

## Current checked source snapshot

The explicit source export contains 249 allowlisted files plus its generated
SHA-256 manifest. The distributed Lean declarations and proofs match the
checked source snapshot: the direct validator compiled all 164 modules to a
fresh package-object directory using Lean 4.30.0 and the nine existing
dependencies recorded by `lake-manifest.json`. No package object was reused.
The current Trust inspection module differs from that snapshot only in comment
text; its imports, commands, and `#print` targets are identical. The source and
axiom audit covered 159 library/test source modules and 221 named theorem
inspections, with only `propext`, `Classical.choice`, and `Quot.sound` reported.
The current exported Python suite ran 52 tests successfully. A generated matrix
product certificate and the labelled graph-report acceptance/rejection suite
also passed in that accepted build.

This establishes a source-bound direct build using the existing pinned
dependency cache. Separately, an isolated Windows run with the installed
Lean/Lake 4.30.0 toolchain cloned all nine fixed manifest revisions, downloaded
and decompressed mathlib's precompiled cache, and completed the ordinary
`lake build` default target graph (3,393 Lake jobs). The resulting root package
contained 159 library/test `.olean` files: 83 for `SpectralGraph` including its
root module and 76 for `SpectralGraphTests` including its root module. No new
dependency `.olean` appeared after cache retrieval. A private `lake env lean`
consumer also compiled the README's two-by-two inertia certificate and checked
`one_add_adjMatrix_posSemidef_iff_compl_isCompleteMultipartite` through the
generated Lake environment.

The ordinary route used fresh dependency checkouts and downloaded precompiled
dependency artifacts; it did not install a fresh toolchain or compile all
dependencies from source. Hosted CI for this snapshot, performance, license
compliance, and publication decisions remain outside this validation.

## Public clone and tutorial check

On 2026-09-19, a fresh clone of the public SpectraWitness repository at
`fde02294625fe7273af0674dc3692b42754fb9ed` passed `lake exe cache get` and
`lake build` on Windows with the installed Lean 4.30.0 toolchain. Dependency
checkouts and the mathlib download-cache directory were fresh. Cache setup took
289.64 seconds (8,459 artifacts); the build passed all 3,393 jobs in 497.48
seconds. Existing style-linter warnings did not prevent compilation.

The [triangle tutorial](examples/tutorial/README.md) was then exercised in that
clone. Its generated named-graph report compiled successfully. Changing the
first eigenvalue count from 2 to 3 produced the expected Lean `decide` failure:
the count equality is false. This verifies both the successful example and a
specific incorrect-answer rejection. The tutorial and documentation additions
do not change the compiled library sources. This check uses an existing
toolchain; it is not a fresh toolchain installation or hosted CI result.

## Trust boundary

Certificate JSON and generated Lean source are untrusted inputs. A generated
certificate becomes evidence only when its Lean theorem compiles. Native
evaluation and benchmark measurements are not kernel proof checks. Theorems
about eigenvalues require their stated Hermitian or symmetry assumptions;
quadratic-form inertia of an arbitrary nonsymmetric matrix has a narrower
meaning.

The package uses standard Lean and mathlib axioms. Current validation evidence
is limited to the exact source snapshot and environment checked; it does not
establish a fresh toolchain installation, source compilation of all
dependencies, or validation of a future edit. See `BENCHMARKS.md` for
performance limits, `RIGHTS.md` for the package licensing scope, and
`THIRD_PARTY_NOTICES.md` for the pinned dependency inventory.
