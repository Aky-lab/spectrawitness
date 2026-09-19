import SpectralGraph.Inertia.ZeroPrincipal
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

/-!
# Independence bounds from zero principal blocks

Any real matrix supported on the edges of a finite simple graph vanishes on
the principal block of an independent set. Inertia here is the inertia of the
associated quadratic form. For a nonsymmetric matrix it refers to its
symmetric part, rather than eigenvalue signs or ordinary matrix nullity.
The adjacency matrix and the named certificate consumers are symmetric.
-/

namespace SpectralGraph.Graph

open SpectralGraph SpectralGraph.Inertia

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A matrix with zero entries on every nonedge, including the diagonal,
bounds every independent set through its semantic inertia. Edge weights may
be zero or signed. -/
theorem indepSet_card_le_inertia_of_supported
    (G : SimpleGraph V) (A : Matrix V V ℝ)
    (hsupport : ∀ u v, ¬G.Adj u v → A u v = 0)
    (s : Finset V) (hs : G.IsIndepSet (↑s : Set V)) :
    s.card ≤ (matrixInertia A).zero +
      min (matrixInertia A).pos (matrixInertia A).neg := by
  classical
  let e : (↥s) ↪ V := Function.Embedding.subtype _
  have hblock : A.submatrix e e = 0 := by
    ext u v
    have hnot : ¬ G.Adj (u : V) (v : V) := by
      by_cases huv : (u : V) = (v : V)
      · rw [huv]
        exact G.loopless.irrefl _
      · exact hs u.property v.property huv
    simpa [e] using hsupport (u : V) (v : V) hnot
  simpa [e, Fintype.card_coe] using
    card_le_matrixInertia_zero_add_min_of_submatrix_eq_zero A e hblock

/-- The same supported-matrix bound for mathlib's maximum independent-set
cardinality. -/
theorem indepNum_le_inertia_of_supported
    (G : SimpleGraph V) (A : Matrix V V ℝ)
    (hsupport : ∀ u v, ¬G.Adj u v → A u v = 0) :
    G.indepNum ≤ (matrixInertia A).zero +
      min (matrixInertia A).pos (matrixInertia A).neg := by
  classical
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  simpa [hs.card_eq] using
    indepSet_card_le_inertia_of_supported G A hsupport s hs.isIndepSet

/-- The ordinary adjacency-matrix specialization for an independent set. -/
theorem indepSet_card_le_adjacency_inertia
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) (hs : G.IsIndepSet (↑s : Set V)) :
    s.card ≤ (matrixInertia (G.adjMatrix ℝ)).zero +
      min (matrixInertia (G.adjMatrix ℝ)).pos
          (matrixInertia (G.adjMatrix ℝ)).neg := by
  apply indepSet_card_le_inertia_of_supported G (G.adjMatrix ℝ)
  · intro u v h
    simp [SimpleGraph.adjMatrix_apply, h]
  · exact hs

/-- The ordinary adjacency-matrix specialization for `indepNum`. -/
theorem indepNum_le_adjacency_inertia
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.indepNum ≤ (matrixInertia (G.adjMatrix ℝ)).zero +
      min (matrixInertia (G.adjMatrix ℝ)).pos
          (matrixInertia (G.adjMatrix ℝ)).neg := by
  apply indepNum_le_inertia_of_supported G (G.adjMatrix ℝ)
  intro u v h
  simp [SimpleGraph.adjMatrix_apply, h]

end SpectralGraph.Graph
