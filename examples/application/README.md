# Weighted endpoint-edge fixtures

These exact-rational fixtures exercise endpoint rank-one updates on paths of
orders 6, 8, and 12. They include a negative-subspace witness and a supplied
image. The supplied-image checker verifies both `A * U = W` and the negative
Gram identity; it does not trust fixture generation.

Prepare and measure in fresh, package-local directories with explicit paths:

```text
python tools/measure_application_lean.py prepare --lean PATH_TO_LEAN --packages PATH_TO_EXISTING_LAKE_PACKAGES --artifact-dir .measurement/prepared --cap 180
python tools/measure_application_lean.py measure --lean PATH_TO_LEAN --artifact-dir .measurement/prepared --output .measurement/report.json --trials 3 --pilot 1 --native-cap 30 --kernel-cap 180 --skip-kernel
```

`--skip-kernel` records that kernel measurement was not run. The nested-Gram and
supplied-image routes are distinct predicates; comparisons must retain input,
calibration, cap, and source-identity details and are not general speed claims.
