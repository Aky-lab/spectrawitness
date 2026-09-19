# Exact graph spectral reports

The graph-report producer accepts strict packed-row JSON and emits a Lean module.
Generation is untrusted; compile the output to check graph validity, named-graph
binding when requested, endpoint inertias, and final spectral statements.

```text
python tools/certify_graph.py examples/graph_reports/p5.json .validation-report/FreshP5Report.lean --namespace Example.P5
python tools/certify_graph.py examples/graph_reports/k3.json .validation-report/FreshK3Report.lean --namespace SpectralGraphTests.GraphReports.K3Report --graph-module SpectralGraphTests.GraphReports.IndependentGraphs --graph-name SpectralGraphTests.GraphReports.IndependentGraphs.completeThree
```

The destination must be new. Queries use `(a,b]`, descending zero-based indices,
and exact integer or fraction endpoints. Packed rows reject loops, high bits,
negative values, and malformed shapes.
