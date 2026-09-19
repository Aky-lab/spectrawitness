# Certified Hoffman bound for a 3×3 rook graph

The Hoffman interface combines a constant-degree graph, a negative cutoff, and
zero negative index for shifted adjacency to bound every independent set. A
singular cutoff and repeated eigenvalues are allowed. The rook-graph example
proves the sharp bound three at cutoff `-2`.

```text
python tools/certify_graph.py --namespace SpectralGraphTests.Hoffman.RookReport --graph-module SpectralGraphTests.Hoffman.Definitions --graph-name SpectralGraphTests.Hoffman.Definitions.rook3 examples/hoffman/rook3.json .validation-hoffman/RookReport.lean
```

Compile the fresh generated theorem in the pinned package environment. The JSON
digest identifies input bytes but is not a proof of parsing or graph equality.
