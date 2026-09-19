import SpectralGraph.Inertia.CenteredBound
import SpectralGraph.Inertia.PosSemidefinite
import SpectralGraph.Graph.Cut

/-! Certified division-free lower bound for a once-counted graph cut. -/

namespace SpectralGraph.Graph

open SpectralGraph SpectralGraph.Inertia Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A zero negative index for the centered scaled Laplacian bounds every cut. -/
theorem gap_mul_card_mul_compl_le_card_mul_cut_of_inertia
    (G : SimpleGraph V) [DecidableRel G.Adj] (γ : ℝ)
    (hneg : (matrixInertia (Inertia.centeredShift (G.lapMatrix ℝ) γ)).neg = 0)
    (s : Finset V) :
    γ * (s.card : ℝ) * ((Fintype.card V : ℝ) - (s.card : ℝ)) ≤
      (Fintype.card V : ℝ) * ((G.interedges s sᶜ).card : ℝ) := by
  classical
  let x : V → ℝ := fun i => if i ∈ s then 1 else 0
  have hpsd : (Inertia.centeredShift (G.lapMatrix ℝ) γ).PosSemidef :=
    matrix_posSemidef_of_matrixInertia_neg_eq_zero _
      (Inertia.centeredShift_isSymm _ _ (G.isSymm_lapMatrix ℝ)) hneg
  have hxsum : (∑ i, x i) = (s.card : ℝ) := by
    simp [x, Finset.sum_ite_mem]
  have hxnorm : dotProduct x x = (s.card : ℝ) := by
    simp [dotProduct, x, Finset.sum_ite_mem]
  have henergy : dotProduct x (G.lapMatrix ℝ *ᵥ x) =
      ((G.interedges s sᶜ).card : ℝ) :=
    lapMatrix_indicator_eq_card_interedges G s
  have hcore := Inertia.variance_le_of_centeredShift_posSemidef
    (G.lapMatrix ℝ) γ hpsd x
  rw [hxsum, hxnorm, henergy] at hcore
  nlinarith

end SpectralGraph.Graph
