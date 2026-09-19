import SpectralGraph.Inertia.RankOne

/-!
# Arbitrary-vector rank-one perturbations

Sharp index bounds for `A + c • vecMulVec u u`, including singular matrices
and zero update vectors. The proof restricts forms to the kernel of the linear
functional `x ↦ u ⬝ᵥ x`, whose codimension is at most one.
-/

namespace SpectralGraph.Inertia
open QuadraticForm Matrix

section Forms
variable {M : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]

/-- Forms agreeing on the kernel of a functional differ in positive index by
at most one. This includes the zero functional without a separate hypothesis. -/
theorem sigPos_le_add_one_of_eq_on_ker (Q R : QuadraticForm ℝ M)
    (f : M →ₗ[ℝ] ℝ) (h : ∀ x, f x = 0 → Q x = R x) :
    sigPos Q ≤ sigPos R + 1 := by
  let K := LinearMap.ker f
  have heq : Q.comp K.subtype = R.comp K.subtype := by
    ext x
    exact h x.1 x.2
  have hdim := f.finrank_range_add_finrank_ker
  have hrange : Module.finrank ℝ (LinearMap.range f) ≤ 1 := by
    simpa using (Submodule.finrank_le (LinearMap.range f))
  have hupper := sigPos_le_comp_add_codim Q K.subtype K.subtype_injective
    (Module.finrank ℝ (LinearMap.range f)) (by dsimp [K]; omega)
  rw [heq] at hupper
  have hlower := sigPos_comp_le R K.subtype K.subtype_injective
  omega

/-- Negative-index companion of the kernel-agreement bound. -/
theorem sigNeg_le_add_one_of_eq_on_ker (Q R : QuadraticForm ℝ M)
    (f : M →ₗ[ℝ] ℝ) (h : ∀ x, f x = 0 → Q x = R x) :
    sigNeg Q ≤ sigNeg R + 1 := by
  apply sigPos_le_add_one_of_eq_on_ker (-Q) (-R) f
  intro x hx
  simp only [QuadraticMap.neg_apply, h x hx]

end Forms

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Evaluation of an arbitrary rank-one update as a scalar square. -/
theorem rankOne_toQuadraticForm_apply (A : Matrix ι ι ℝ) (u x : ι → ℝ) (c : ℝ) :
    (A + c • vecMulVec u u).toQuadraticForm' x =
      A.toQuadraticForm' x + c * (u ⬝ᵥ x) ^ 2 := by
  simp only [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply,
    LinearMap.BilinMap.toQuadraticMap_apply, Matrix.add_apply,
    Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  congr 1
  simp only [dotProduct, pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private def dotFunctional (u : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun x := u ⬝ᵥ x
  map_add' x y := dotProduct_add u x y
  map_smul' c x := by simp [dotProduct_smul]

/-- An arbitrary rank-one perturbation changes the positive index by at most
one, independently of the sign or size of either coefficient. -/
theorem rankOne_pos_interlaces (A : Matrix ι ι ℝ) (u : ι → ℝ) (a b : ℝ) :
    (matrixInertia (A + a • vecMulVec u u)).pos ≤
        (matrixInertia (A + b • vecMulVec u u)).pos + 1 ∧
    (matrixInertia (A + b • vecMulVec u u)).pos ≤
        (matrixInertia (A + a • vecMulVec u u)).pos + 1 := by
  have h (a b : ℝ) := sigPos_le_add_one_of_eq_on_ker
    (A + a • vecMulVec u u).toQuadraticForm'
    (A + b • vecMulVec u u).toQuadraticForm' (dotFunctional u)
    (by intro x hx; change u ⬝ᵥ x = 0 at hx; simp [rankOne_toQuadraticForm_apply, hx])
  exact ⟨h a b, h b a⟩

/-- An arbitrary rank-one perturbation changes the negative index by at most one. -/
theorem rankOne_neg_interlaces (A : Matrix ι ι ℝ) (u : ι → ℝ) (a b : ℝ) :
    (matrixInertia (A + a • vecMulVec u u)).neg ≤
        (matrixInertia (A + b • vecMulVec u u)).neg + 1 ∧
    (matrixInertia (A + b • vecMulVec u u)).neg ≤
        (matrixInertia (A + a • vecMulVec u u)).neg + 1 := by
  have h (a b : ℝ) := sigNeg_le_add_one_of_eq_on_ker
    (A + a • vecMulVec u u).toQuadraticForm'
    (A + b • vecMulVec u u).toQuadraticForm' (dotFunctional u)
    (by intro x hx; change u ⬝ᵥ x = 0 at hx; simp [rankOne_toQuadraticForm_apply, hx])
  exact ⟨h a b, h b a⟩

/-- Increasing the coefficient makes the positive index increase and the
negative index decrease, each by at most one. -/
theorem rankOne_inertia_mono (A : Matrix ι ι ℝ) (u : ι → ℝ) {a b : ℝ} (hab : a ≤ b) :
    (matrixInertia (A + a • vecMulVec u u)).pos ≤
        (matrixInertia (A + b • vecMulVec u u)).pos ∧
    (matrixInertia (A + b • vecMulVec u u)).pos ≤
        (matrixInertia (A + a • vecMulVec u u)).pos + 1 ∧
    (matrixInertia (A + b • vecMulVec u u)).neg ≤
        (matrixInertia (A + a • vecMulVec u u)).neg ∧
    (matrixInertia (A + a • vecMulVec u u)).neg ≤
        (matrixInertia (A + b • vecMulVec u u)).neg + 1 := by
  have hform : ∀ x, (A + a • vecMulVec u u).toQuadraticForm' x ≤
      (A + b • vecMulVec u u).toQuadraticForm' x := by
    intro x
    rw [rankOne_toQuadraticForm_apply, rankOne_toQuadraticForm_apply]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hab (sq_nonneg _))
  exact ⟨sigPos_le_of_forall_le _ _ hform, (rankOne_pos_interlaces A u a b).2,
    sigNeg_le_of_forall_le _ _ hform, (rankOne_neg_interlaces A u a b).1⟩

/-- A rank-one update changes signature by at most two. -/
theorem rankOne_signature_interlaces (A : Matrix ι ι ℝ) (u : ι → ℝ) (a b : ℝ) :
    matrixSignature (A + a • vecMulVec u u) ≤
        matrixSignature (A + b • vecMulVec u u) + 2 ∧
    matrixSignature (A + b • vecMulVec u u) ≤
        matrixSignature (A + a • vecMulVec u u) + 2 := by
  have hp := rankOne_pos_interlaces A u a b
  have hn := rankOne_neg_interlaces A u a b
  simp only [matrixSignature, Inertia.signature]
  omega

/-- Increasing the rank-one coefficient increases signature by between zero
and two, including singular transition points. -/
theorem rankOne_signature_mono (A : Matrix ι ι ℝ) (u : ι → ℝ) {a b : ℝ} (hab : a ≤ b) :
    matrixSignature (A + a • vecMulVec u u) ≤
        matrixSignature (A + b • vecMulVec u u) ∧
    matrixSignature (A + b • vecMulVec u u) ≤
        matrixSignature (A + a • vecMulVec u u) + 2 := by
  have h := rankOne_inertia_mono A u hab
  simp only [matrixSignature, Inertia.signature]
  omega

/-- Nullity changes by at most one under an arbitrary rank-one update. -/
theorem rankOne_zero_interlaces (A : Matrix ι ι ℝ) (u : ι → ℝ) (a b : ℝ) :
    (matrixInertia (A + a • vecMulVec u u)).zero ≤
        (matrixInertia (A + b • vecMulVec u u)).zero + 1 ∧
    (matrixInertia (A + b • vecMulVec u u)).zero ≤
        (matrixInertia (A + a • vecMulVec u u)).zero + 1 := by
  have ha := matrixInertia_order (A + a • vecMulVec u u)
  have hb := matrixInertia_order (A + b • vecMulVec u u)
  simp only [Inertia.order] at ha hb
  rcases le_total a b with hab | hba
  · have h := rankOne_inertia_mono A u hab
    omega
  · have h := rankOne_inertia_mono A u hba
    omega

end SpectralGraph.Inertia
