# External exact-matrix certificate producer

`tools/certify_matrix.py` accepts one strict JSON matrix and writes a new Lean
certificate candidate. Entries are exact integers or fraction strings; malformed
JSON, floating-point values, duplicate keys, nonsquare matrices, and asymmetric
input are rejected.

```text
python tools/certify_matrix.py input.json fresh-output.lean --format product
```

Use `--matrix-module` and `--matrix-name` to bind the check to an independently
defined Lean matrix. The generated file must be compiled: hashes and producer
diagnostics are provenance, not mathematical premises. The product format checks
the supplied image as well as the inverse, diagonal identity, and sign counts.

Fast schema tests can be run with:

```text
python -m unittest discover -s tools -p test_certify_matrix.py -v
```
