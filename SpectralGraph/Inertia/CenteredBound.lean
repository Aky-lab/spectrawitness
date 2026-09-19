import Mathlib.LinearAlgebra.Matrix.PosDef

/-! A scaled centered matrix and its quadratic variance estimate. -/

namespace SpectralGraph.Inertia

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The scale avoids division by the number of vertices, including for an empty type. -/
def centeredShift (A : Matrix V V ℝ) (γ : ℝ) : Matrix V V ℝ :=
  (Fintype.card V : ℝ) • A -
    γ • ((Fintype.card V : ℝ) • (1 : Matrix V V ℝ) -
      Matrix.of (fun (_ : V) (_ : V) => (1 : ℝ)))

theorem centeredShift_isSymm (A : Matrix V V ℝ) (γ : ℝ)
    (hA : A.IsSymm) : (centeredShift A γ).IsSymm := by
  apply Matrix.IsSymm.sub
  · exact hA.smul _
  · apply Matrix.IsSymm.smul
    apply Matrix.IsSymm.sub
    · exact Matrix.isSymm_one.smul _
    · apply Matrix.IsSymm.ext
      intro i j
      rfl

/-- A PSD centered shift gives the division-free variance estimate. -/
theorem variance_le_of_centeredShift_posSemidef
    (A : Matrix V V ℝ) (γ : ℝ)
    (hpsd : (centeredShift A γ).PosSemidef) (x : V → ℝ) :
    γ * ((Fintype.card V : ℝ) * dotProduct x x - (∑ i, x i)^2) ≤
      (Fintype.card V : ℝ) * dotProduct x (A *ᵥ x) := by
  have hJ :
      (Matrix.of (fun (_ : V) (_ : V) => (1 : ℝ))) *ᵥ x =
        (fun _ => ∑ i, x i) := by
    funext i
    simp [Matrix.mulVec, dotProduct]
  have hquad : dotProduct x (centeredShift A γ *ᵥ x) =
      (Fintype.card V : ℝ) * dotProduct x (A *ᵥ x) -
        γ * ((Fintype.card V : ℝ) * dotProduct x x - (∑ i, x i)^2) := by
    simp only [centeredShift, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, hJ]
    simp [dotProduct, Finset.mul_sum, smul_eq_mul]
    rw [← Fintype.sum_mul_sum x x]
    simp [pow_two]
  have hnonneg := hpsd.dotProduct_mulVec_nonneg x
  rw [star_trivial] at hnonneg
  rw [hquad] at hnonneg
  linarith

end SpectralGraph.Inertia
