import SpectralGraph.Inertia.RegularSupportBound
import SpectralGraph.Inertia.PosSemidefinite
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Clique

/-! Certificate-backed Hoffman ratio bounds for finite regular graphs. -/

namespace SpectralGraph.Graph

open SpectralGraph SpectralGraph.Inertia Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every independent set is bounded using any strictly negative lower adjacency
cutoff, including an attained or repeated eigenvalue. -/
theorem indepSet_card_le_hoffman_of_inertia
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (hreg : G.IsRegularOfDegree d) (τ : ℝ) (hτ : τ < 0)
    (hneg : (matrixInertia (G.adjMatrix ℝ - τ • 1)).neg = 0)
    (s : Finset V) (hs : G.IsIndepSet (↑s : Set V)) :
    (s.card : ℝ) ≤ (Fintype.card V : ℝ) * (-τ) / ((d : ℝ) - τ) := by
  classical
  have hA : (G.adjMatrix ℝ).IsSymm := G.isSymm_adjMatrix
  have hshift : (G.adjMatrix ℝ - τ • 1).IsSymm :=
    hA.sub (Matrix.isSymm_one.smul _)
  have hpsd : (G.adjMatrix ℝ - τ • 1).PosSemidef :=
    matrix_posSemidef_of_matrixInertia_neg_eq_zero _ hshift hneg
  have hrow : (G.adjMatrix ℝ) *ᵥ (fun _ : V => (1 : ℝ)) =
      (d : ℝ) • (fun _ : V => (1 : ℝ)) := by
    funext v
    simpa using (G.adjMatrix_mulVec_const_apply_of_regular (α := ℝ)
      (a := (1 : ℝ)) hreg (v := v))
  have hzero : ∀ i ∈ s, ∀ j ∈ s, G.adjMatrix ℝ i j = 0 := by
    intro i hi j hj
    have hnot : ¬ G.Adj i j := by
      by_cases hij : i = j
      · subst j
        exact G.loopless.irrefl i
      · exact hs hi hj hij
    simp [SimpleGraph.adjMatrix_apply, hnot]
  have hcore := card_mul_sub_le_of_zero_principal_of_posSemidef
    (G.adjMatrix ℝ) hA (d : ℝ) τ hrow hτ hpsd s hzero
  have hden : 0 < (d : ℝ) - τ := by
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  apply (le_div_iff₀ hden).2
  nlinarith [hcore]

/-- The same certified lower-cutoff bound for mathlib's maximum independent
set cardinality. -/
theorem indepNum_le_hoffman_of_inertia
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (hreg : G.IsRegularOfDegree d) (τ : ℝ) (hτ : τ < 0)
    (hneg : (matrixInertia (G.adjMatrix ℝ - τ • 1)).neg = 0) :
    (G.indepNum : ℝ) ≤ (Fintype.card V : ℝ) * (-τ) / ((d : ℝ) - τ) := by
  classical
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  simpa [hs.card_eq] using
    indepSet_card_le_hoffman_of_inertia G d hreg τ hτ hneg s hs.isIndepSet

end SpectralGraph.Graph
