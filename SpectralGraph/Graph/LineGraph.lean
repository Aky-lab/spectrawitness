import SpectralGraph.GraphMatrix
import SpectralGraph.Inertia.ShiftedGram

/-!
# Line-graph inertia transfer

The incidence Gram identities transfer all three inertia indices from the
shifted signless Laplacian to line-graph adjacency, with the exact dimension
correction. No connectedness or order bound is required.
-/

namespace SpectralGraph.Graph
open GraphMatrix Inertia

/-- Adjacency signature of a finite simple graph. -/
noncomputable def graphSignature {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Int :=
  matrixSignature (G.adjMatrix ℝ)

/-- The row-side shifted Gram matrix of the edge-indexed incidence matrix is
the shifted signless Laplacian `M(G) = Q(G) - 2I`. -/
theorem shiftedRowGram_edgeIncMatrix
    {V : Type _} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    shiftedRowGram (edgeIncMatrix ℝ G) = shiftedSignless G := by
  simp only [shiftedRowGram, shiftedSignless,
    edgeIncMatrix_mul_transpose_eq_signlessLapMatrix]

/-- The column-side shifted Gram matrix of the edge-indexed incidence matrix
is the adjacency matrix of the line graph. -/
theorem shiftedColGram_edgeIncMatrix
    {V : Type _} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel G.lineGraph.Adj] :
    shiftedColGram (edgeIncMatrix ℝ G) = G.lineGraph.adjMatrix ℝ := by
  rw [shiftedColGram, edgeIncMatrix_transpose_mul_eq_lineGraphAdj_add_two]
  abel

/-- Graph-specialized shifted-Gram inertia relations.  In particular, if
`r` is the negative index of `M(G)`, then the additive relation reads
`r + m = n₋(A(L(G))) + n`. -/
theorem lineGraph_inertia_relations
    {V : Type _} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel G.lineGraph.Adj] :
    (matrixInertia (shiftedSignless G)).pos =
        (matrixInertia (G.lineGraph.adjMatrix ℝ)).pos ∧
      (matrixInertia (shiftedSignless G)).zero =
        (matrixInertia (G.lineGraph.adjMatrix ℝ)).zero ∧
      (matrixInertia (shiftedSignless G)).neg + Fintype.card G.edgeSet =
        (matrixInertia (G.lineGraph.adjMatrix ℝ)).neg + Fintype.card V := by
  simpa [shiftedRowGram_edgeIncMatrix G, shiftedColGram_edgeIncMatrix G] using
    shiftedGram_inertia_relations (edgeIncMatrix ℝ G)

/-- The line-graph signature differs from the shifted signless-Laplacian
signature by the exact vertex-minus-edge correction. This form is especially
convenient for pendant-tree deletion and replacement, where that correction
is unchanged. -/
theorem lineGraph_signature_eq_shiftedSignless_signature_add_card
    {V : Type _} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel G.lineGraph.Adj] :
    graphSignature G.lineGraph =
      matrixSignature (shiftedSignless G) +
        (Fintype.card V : Int) - (Fintype.card G.edgeSet : Int) := by
  have hrel := lineGraph_inertia_relations G
  simp only [graphSignature, matrixSignature, Inertia.signature] at hrel ⊢
  omega

/-- With the same vertex-minus-edge correction (equivalently, for connected
graphs, the same cyclomatic number), comparison of line-graph signatures is
exactly comparison of shifted signless-Laplacian signatures. -/
theorem lineGraph_signature_le_iff_shiftedSignless_signature_le_of_card_correction
    {V W : Type _}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel G.lineGraph.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    [DecidableRel H.lineGraph.Adj]
    (hcorr : (Fintype.card V : Int) - (Fintype.card G.edgeSet : Int) =
      (Fintype.card W : Int) - (Fintype.card H.edgeSet : Int)) :
    graphSignature G.lineGraph ≤ graphSignature H.lineGraph ↔
      matrixSignature (shiftedSignless G) ≤
        matrixSignature (shiftedSignless H) := by
  rw [lineGraph_signature_eq_shiftedSignless_signature_add_card G,
    lineGraph_signature_eq_shiftedSignless_signature_add_card H]
  omega

/-- Equality version of the same cyclomatic-invariance transfer. -/
theorem lineGraph_signature_eq_iff_shiftedSignless_signature_eq_of_card_correction
    {V W : Type _}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel G.lineGraph.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    [DecidableRel H.lineGraph.Adj]
    (hcorr : (Fintype.card V : Int) - (Fintype.card G.edgeSet : Int) =
      (Fintype.card W : Int) - (Fintype.card H.edgeSet : Int)) :
    graphSignature G.lineGraph = graphSignature H.lineGraph ↔
      matrixSignature (shiftedSignless G) =
        matrixSignature (shiftedSignless H) := by
  rw [lineGraph_signature_eq_shiftedSignless_signature_add_card G,
    lineGraph_signature_eq_shiftedSignless_signature_add_card H]
  omega


end SpectralGraph.Graph
