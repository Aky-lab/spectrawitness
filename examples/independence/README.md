# Certificate-backed independence bounds

The independence interfaces bound a finite graph's independent sets from exact
inertia. A supported matrix must vanish on every nonedge, including diagonal
entries; signed edge weights are permitted. The nullity term in the general bound
cannot generally be removed.

```text
python tools/certify_matrix.py --format product --matrix-module SpectralGraphTests.Independence.Definitions --matrix-name SpectralGraphTests.Independence.Definitions.signedC4 --namespace SpectralGraphTests.Independence.SignedC4Certificate examples/independence/signed_c4.json .validation-independence/SignedC4.lean
python tools/certify_graph.py --graph-module SpectralGraphTests.Independence.Definitions --graph-name SpectralGraphTests.Independence.Definitions.petersen --namespace SpectralGraphTests.Independence.PetersenReport examples/independence/petersen.json .validation-independence/PetersenReport.lean
```

Compile generated files before use. The JSON inputs guide certificate discovery;
the Lean checker establishes the matrix and graph conclusions.
