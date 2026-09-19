import SpectralGraph.Inertia.SchurComplement
import SpectralGraph.Inertia.Diagonal

/-!
# Exact inertia changes under a rank-one update

For invertible symmetric `A`, the inverse quadratic value `uᵀ A⁻¹ u`
determines the complete inertia change. A bordered matrix is eliminated in
two different orders. The additive formula includes the singular transition
and avoids subtraction of natural-number indices.
-/

namespace SpectralGraph.Inertia
open Matrix

/-- Inertia contributed by a scalar pivot, including the zero pivot. -/
noncomputable def scalarInertia (x : ℝ) : Inertia := by
  classical
  exact ⟨if 0 < x then 1 else 0, if x = 0 then 1 else 0, if x < 0 then 1 else 0⟩

/-- A singleton matrix contributes the signs of its one entry. -/
theorem matrixInertia_singleton (x : ℝ) :
    matrixInertia (fun _ _ : Unit ↦ x) = scalarInertia x := by
  classical
  have he : (fun _ _ : Unit ↦ x) = Matrix.diagonal (fun _ : Unit ↦ x) := by
    ext i j
    simp
  rw [he, SpectralGraph.matrixInertia_diagonal]
  simp only [scalarInertia, Finset.univ_unique, Finset.filter_singleton]
  split_ifs <;> simp_all

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact rank-one inertia balance. The correction scalar is
`-c⁻¹ - uᵀ A⁻¹ u`; no invertibility of the updated matrix is assumed. -/
theorem rankOne_inertia_balance (A : Matrix ι ι ℝ) (hA : A.IsSymm)
    [Invertible A] (u : ι → ℝ) (c : ℝ) (hc : c ≠ 0) :
    let updated := matrixInertia (A + c • vecMulVec u u)
    let pivot := scalarInertia (-c⁻¹)
    let correction := scalarInertia (-c⁻¹ - u ⬝ᵥ (A⁻¹ *ᵥ u))
    updated.pos + pivot.pos = correction.pos + (matrixInertia A).pos ∧
    updated.zero + pivot.zero = correction.zero + (matrixInertia A).zero ∧
    updated.neg + pivot.neg = correction.neg + (matrixInertia A).neg := by
  let B : Matrix ι Unit ℝ := fun i _ ↦ u i
  let D : Matrix Unit Unit ℝ := fun _ _ ↦ -c⁻¹
  let E : Matrix Unit Unit ℝ := fun _ _ ↦ -c
  have he : E * D = 1 := by
    ext i j
    simp [E, D, Matrix.mul_apply, hc]
  letI : Invertible D := invertibleOfLeftInverse D E he
  have hinv : ⅟ D = E := invOf_eq_left_inv he
  have hD : D.IsSymm := by ext i j; rfl
  have hupdate : A - B * ⅟ D * B.transpose = A + c • vecMulVec u u := by
    rw [hinv]
    ext i j
    simp [B, E, Matrix.mul_apply, Matrix.transpose_apply, vecMulVec_apply]
    ring
  have hcorrection : D - B.transpose * ⅟ A * B =
      (fun _ _ : Unit ↦ -c⁻¹ - u ⬝ᵥ (A⁻¹ *ᵥ u)) := by
    ext i j
    simp only [Matrix.sub_apply, D, Matrix.mul_apply, B, Matrix.transpose_apply,
      Matrix.invOf_eq_nonsing_inv, dotProduct, Matrix.mulVec]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    ring
  have hbottom := matrixInertia_fromBlocks_schur₂₂ A B D hD
  have htop := matrixInertia_fromBlocks_schur₁₁ A B D hA
  rw [hupdate, show matrixInertia D = scalarInertia (-c⁻¹) from matrixInertia_singleton _] at hbottom
  rw [hcorrection, matrixInertia_singleton] at htop
  have heq := hbottom.symm.trans htop
  exact ⟨congrArg Inertia.pos heq, congrArg Inertia.zero heq, congrArg Inertia.neg heq⟩

end SpectralGraph.Inertia
