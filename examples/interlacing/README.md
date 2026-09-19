# Induced adjacency interlacing

`SpectralGraph.Graph.InducedSpectrum` identifies an induced adjacency matrix
with the corresponding principal submatrix and proves descending,
multiplicity-safe Cauchy interlacing. If `n` and `m` are ambient and retained
vertex counts, then `λ(G)[k + (n-m)] ≤ λ(G.induce S)[k] ≤ λ(G)[k]`.

The interface is adjacency-specific: induced Laplacians are not principal
submatrices because vertex deletion changes degrees. Empty retained types make
the indexed statement vacuous rather than creating an artificial endpoint.
