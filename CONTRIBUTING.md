# Contributing

Contributions are welcome. Useful starting points include a small graph example,
a sharper theorem using an existing certificate interface, a documentation
improvement, or a focused regression test. Open an issue or discussion before a
substantial public-API change so its mathematical statement and intended users
can be agreed before implementation.

Keep changes focused and explain the mathematical or verification task they
address. Use mathlib objects where appropriate. Separate untrusted data
producers, Boolean acceptance predicates, and theorems proving those predicates
sound. State finiteness, symmetry, and non-emptiness assumptions explicitly.

Proofs should use exact arithmetic and remain kernel checked. Do not add proof
holes, extra axioms, or native evaluation to library proofs or regression tests.
For the code you touch, add meaningful coverage for applicable empty, singular,
malformed, equality, strictness, and other boundary cases. Prefer narrow imports
and include a small example when it makes the API easier to understand.

## Local checks

Run focused modules while developing, then the applicable library and test
umbrellas. With dependencies from `lake-manifest.json` available, the ordinary
package checks are:

```text
lake build SpectralGraph
lake build SpectralGraphTests
python -m unittest discover -s tools -p "test_*.py"
```

For a controlled from-source check, use a fresh package-local output directory:

```text
python validate_local.py --lean PATH_TO_LEAN --packages PATH_TO_EXISTING_LAKE_PACKAGES --output-dir .validation-run
python tools/audit.py --trust-log .validation-run/SpectralGraphTests.Trust.log --report .validation-run/report.json
```

`Validation/Axioms.lean` and the Python audit complement compilation; neither
replaces kernel checking. Benchmark output is performance evidence, not proof
evidence.

By submitting a contribution for inclusion, you agree that it is provided under
the Apache License 2.0, as described in section 5 of `LICENSE`. Do not submit
material you are not authorized to contribute, and preserve applicable
third-party notices and provenance.
