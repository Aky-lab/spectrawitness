import SpectralGraph.Graph.Threshold
import SpectralGraph.Inertia.Restriction
import Mathlib.Combinatorics.SimpleGraph.Maps

/-! # Isomorphism invariance of threshold inertia -/

namespace SpectralGraph.Graph

/-- Relabeling preserves all three inertia indices at every real threshold.
The vertex types may differ. This supplies spectral property transport for
isomorphism-certified exhaustive searches. -/
theorem inertia_shift_eq_of_iso
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : G ≃g H) (t : ℝ) :
    matrixInertia (G.adjMatrix ℝ - t • (1 : Matrix V V ℝ)) =
      matrixInertia (H.adjMatrix ℝ - t • (1 : Matrix W W ℝ)) := by
  have h : (H.adjMatrix ℝ - t • (1 : Matrix W W ℝ)).submatrix e e =
      G.adjMatrix ℝ - t • (1 : Matrix V V ℝ) := by
    ext i j
    simp [Matrix.submatrix, Matrix.one_apply, SimpleGraph.adjMatrix,
      e.map_rel_iff, e.injective.eq_iff]
  rw [← h]
  exact Inertia.matrixInertia_submatrix_equiv _ e.toEquiv

end SpectralGraph.Graph
