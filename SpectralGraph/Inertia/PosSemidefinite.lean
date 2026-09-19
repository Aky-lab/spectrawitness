import SpectralGraph.Inertia.Matrix
import SpectralGraph.Inertia.Restriction
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Positive semidefiniteness from semantic inertia

This file connects the quadratic-form definition of `matrixInertia` to
mathlib's matrix `PosSemidef` predicate.  The bridge is generic and lets
spectral graph arguments consume exact-inertia results without choosing an
eigenvalue implementation.
-/

namespace SpectralGraph

open QuadraticForm

/-- A symmetric real matrix with no negative inertia direction is positive
semidefinite. -/
theorem matrix_posSemidef_of_matrixInertia_neg_eq_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (hA : A.IsSymm)
    (hneg : (matrixInertia A).neg = 0) :
    A.PosSemidef := by
  let Q : QuadraticForm ℝ (I → ℝ) := A.toQuadraticForm'
  obtain ⟨w, hequiv⟩ := Q.equivalent_weightedSumSquares
  obtain ⟨e⟩ := hequiv
  have hnegativeCard : {i | w i < 0}.ncard = 0 := by
    rw [← sigNeg_of_equiv_weightedSumSquares (Nonempty.intro e)]
    exact hneg
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    apply le_of_not_gt
    intro hi
    have hnonempty : Set.Nonempty {j | w j < 0} := ⟨i, hi⟩
    have hpositive : 0 < {j | w j < 0}.ncard :=
      (Set.ncard_pos).mpr hnonempty
    omega
  have hQnonneg : ∀ x, 0 ≤ Q x := by
    intro x
    rw [← e.map_app]
    rw [QuadraticMap.weightedSumSquares_apply]
    exact Finset.sum_nonneg fun i _ ↦
      mul_nonneg (hw i) (mul_self_nonneg _)
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · simpa [Matrix.IsHermitian, Matrix.conjTranspose] using hA
  · intro x
    simpa only [Q, Matrix.toQuadraticForm',
      LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply'] using hQnonneg x

/-- In a positive-semidefinite symmetric matrix, an isotropic vector lies in
the matrix kernel.  This is the equality case of Cauchy--Schwarz, connected
to `mulVec` through the generic quadratic-form radical interface. -/
theorem matrix_mulVec_eq_zero_of_posSemidef_isotropic
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (hA : A.IsSymm) (hpsd : A.PosSemidef)
    (x : I → ℝ) (hx : dotProduct x (Matrix.mulVec A x) = 0) :
    Matrix.mulVec A x = 0 := by
  let Q := A.toQuadraticForm'
  let B : LinearMap.BilinForm ℝ (I → ℝ) := QuadraticMap.associated Q
  have hnonneg : ∀ y, 0 ≤ B y y := by
    intro y
    rw [QuadraticMap.associated_eq_self_apply]
    simpa [Q, Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply'] using
      hpsd.dotProduct_mulVec_nonneg y
  have hBsymm : LinearMap.IsSymm B :=
    QuadraticForm.associated_isSymm ℝ Q
  have hxB : B x x = 0 := by
    rw [QuadraticMap.associated_eq_self_apply]
    simpa [Q, Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply'] using hx
  have hxker := (LinearMap.BilinForm.apply_apply_same_eq_zero_iff
    B hnonneg hBsymm).mp hxB
  have hxrad : x ∈ QuadraticMap.radical Q := by
    rw [QuadraticMap.radical_eq_ker_associated]
    exact hxker
  have hxkerA : x ∈ LinearMap.ker A.mulVecLin := by
    rw [← Inertia.radical_toQuadraticForm'_eq_ker_mulVecLin A hA]
    exact hxrad
  simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hxkerA

/-- A symmetric real matrix with neither negative directions nor nullity is
positive definite. -/
theorem matrix_posDef_of_matrixInertia_neg_zero_eq_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (hA : A.IsSymm)
    (hneg : (matrixInertia A).neg = 0)
    (hzero : (matrixInertia A).zero = 0) : A.PosDef := by
  let Q : QuadraticForm ℝ (I → ℝ) := A.toQuadraticForm'
  obtain ⟨w, hequiv⟩ := Q.equivalent_weightedSumSquares
  obtain ⟨e⟩ := hequiv
  have hnegativeCard : {i | w i < 0}.ncard = 0 := by
    rw [← sigNeg_of_equiv_weightedSumSquares (Nonempty.intro e)]
    exact hneg
  have hzeroCard : {i | w i = 0}.ncard = 0 := by
    rw [← QuadraticForm.finrank_radical_of_equiv_weightedSumSquares
      (Nonempty.intro e)]
    exact hzero
  have hw : ∀ i, 0 < w i := by
    intro i
    have hnneg : 0 ≤ w i := by
      apply le_of_not_gt
      intro hi
      have : 0 < {j | w j < 0}.ncard :=
        (Set.ncard_pos).mpr ⟨i, hi⟩
      omega
    have hne : w i ≠ 0 := by
      intro hi
      have : 0 < {j | w j = 0}.ncard :=
        (Set.ncard_pos).mpr ⟨i, hi⟩
      omega
    exact lt_of_le_of_ne hnneg (Ne.symm hne)
  have hWpos : (QuadraticMap.weightedSumSquares ℝ w).PosDef := by
    intro x hx
    rw [QuadraticMap.weightedSumSquares_apply]
    have hxi : ∃ i, x i ≠ 0 := by
      simpa [funext_iff] using hx
    obtain ⟨i, hi⟩ := hxi
    apply Finset.sum_pos'
    · intro j _
      exact mul_nonneg (le_of_lt (hw j)) (mul_self_nonneg _)
    · exact ⟨i, Finset.mem_univ i,
        mul_pos (hw i) (mul_self_pos.mpr hi)⟩
  have hQpos : Q.PosDef := by
    intro x hx
    rw [← e.map_app]
    exact hWpos (e x) (by simpa using e.injective.ne hx)
  exact Matrix.PosDef.of_toQuadraticForm' hA hQpos

end SpectralGraph
