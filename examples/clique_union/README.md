# Shifted adjacency and clique unions

For a finite simple graph `G`, `SpectralGraph.Graph.one_add_adjMatrix_posSemidef_iff_compl_isCompleteMultipartite` states

```text
I + A(G) is positive semidefinite  ↔  the complement of G is complete multipartite.
```

Thus an exact adjacency-inertia certificate at the cutoff `-1` can prove that `G` is a disjoint union of cliques. `SpectralGraphTests.CliqueUnionCertificate` defines the six-vertex graph `K₃ ⊔ K₂ ⊔ K₁` and kernel-checks the shifted inertia `(3, 3, 0)`. The three zero directions make this a genuinely semidefinite, not positive-definite, example. `SpectralGraphTests.Applications.CliqueUnionSix` imports that checked fact, proves the exact identity `A - (-1)I = I + A`, and concludes that the complement is complete multipartite without repeating the checker computation.

From the package root, check the example with the pinned Lean toolchain and dependencies:

```sh
lake env lean SpectralGraphTests/CliqueUnionCertificate.lean
lake env lean SpectralGraphTests/Applications/CliqueUnionSix.lean
lake env lean SpectralGraphTests/CliqueUnion.lean
```

The checker validates exact integer/rational data inside Lean. The structural theorem and its consumer are ordinary kernel-checked proofs. The Python producers elsewhere in the package are untrusted conveniences; no producer output is accepted without the corresponding Lean checks. The regression module also shows that `P₃` fails the structural property and that the vector `[1,-1,1]` gives quadratic value `-1` for `I + A(P₃)`.
