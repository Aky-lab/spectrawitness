# Vertex-cell spectral workflows

For a surjective vertex-to-cell map `p`, `Graph.PartitionSpectrum` compresses
adjacency by the cell indicators. Its shifted pencil is `B - tD`, where `D`
contains the actual cell sizes; replacing `D` with the identity is unsound for
unequal cells. These bounds do not require equitability.

`Graph.EquitableSpectrum` separately lifts an eigenpair of a supplied equitable
count matrix to an occurrence in the adjacency spectrum. The count matrix need
not itself be symmetric.
