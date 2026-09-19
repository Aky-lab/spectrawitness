import SpectralGraph.Inertia.Restriction
import SpectralGraph.Inertia.BlockDiagonal
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Sparse negative-subspace witnesses

Reusable semantic bridges from one- and two-vector exact witnesses to lower
bounds on the negative inertia index.  Certificate discovery may be
specialized and untrusted; these small verification theorems are generic.
-/

namespace SpectralGraph.Inertia

open Matrix QuadraticForm

/-- A vector of negative value is already a one-dimensional negative
subspace for an arbitrary finite-dimensional quadratic form. -/
theorem one_le_sigNeg_of_negative
    {M : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
    (Q : QuadraticForm ℝ M) (x : M) (hx : Q x < 0) :
    1 ≤ sigNeg Q := by
  let W : Submodule ℝ M := Submodule.span ℝ {x}
  have hxne : x ≠ 0 := by
    intro hzero
    simp [hzero] at hx
  have hWdim : Module.finrank ℝ W = 1 :=
    finrank_span_singleton hxne
  have hWneg : ((-Q).restrict W).PosDef := by
    intro y hy
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp y.property
    change 0 < -Q y.1
    rw [← ha, QuadraticMap.map_smul]
    have ha : a ≠ 0 := by
      intro haZero
      apply hy
      apply Subtype.ext
      rw [← ha]
      simp [haZero]
    simpa [smul_eq_mul] using
      mul_pos (mul_self_pos.mpr ha) (neg_pos.mpr hx)
  have hbound := le_sigNeg_of_negDef Q hWneg
  simpa [hWdim] using hbound

/-- A nonradical isotropic vector forces a negative direction.  This is the
coordinate-free hyperbolic-plane witness used by route elimination. -/
theorem one_le_sigNeg_of_isotropic_not_radical
    {M : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
    (Q : QuadraticForm ℝ M) (p : M)
    (hQp : Q p = 0) (hp : p ∉ QuadraticMap.radical Q) :
    1 ≤ sigNeg Q := by
  let B := QuadraticMap.associated Q
  have hBp : B p ≠ 0 := by
    intro hzero
    apply hp
    rw [QuadraticMap.radical_eq_ker_associated]
    simpa only [LinearMap.mem_ker] using hzero
  obtain ⟨q, hb⟩ : ∃ q, B p q ≠ 0 := by
    by_contra h
    push Not at h
    apply hBp
    ext q
    exact h q
  let a : ℝ := (Q q + 1) / (2 * B p q)
  let x := q - a • p
  have hsymm : B q p = B p q := by
    exact QuadraticMap.associated_isSymm ℝ Q q p
  have hx : Q x = -1 := by
    rw [← QuadraticMap.associated_eq_self_apply ℝ Q]
    simp only [x, map_sub, LinearMap.sub_apply, LinearMap.map_smul,
      LinearMap.smul_apply, smul_eq_mul]
    rw [QuadraticMap.associated_eq_self_apply,
      QuadraticMap.associated_eq_self_apply, hQp, hsymm]
    simp only [mul_zero, sub_zero]
    dsimp only [a]
    field_simp [hb]
    ring
  apply one_le_sigNeg_of_negative Q x
  rw [hx]
  norm_num

/-- Expansion of a matrix quadratic form on a two-vector span. -/
theorem matrix_quadratic_pair_expansion
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (u v : ι → ℝ) (a b : ℝ) :
    A.toQuadraticForm' (a • u + b • v) =
      a * a * A.toQuadraticForm' u +
        a * b * (dotProduct u (Matrix.mulVec A v)) +
        a * b * (dotProduct v (Matrix.mulVec A u)) +
        b * b * A.toQuadraticForm' v := by
  simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', Matrix.mulVec_add, Matrix.mulVec_smul,
    add_dotProduct, dotProduct_add, dotProduct_smul, smul_dotProduct]
  ring

/-- Coordinate map from a two-dimensional coefficient space to the span of
two ambient vectors. -/
def pairLinearMap {ι : Type*} (u v : ι → ℝ) :
    (Fin 2 → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun z := z 0 • u + z 1 • v
  map_add' x y := by
    ext i
    simp
    ring
  map_smul' a x := by
    ext i
    simp
    ring

@[simp] theorem pairLinearMap_apply {ι : Type*} (u v : ι → ℝ)
    (z : Fin 2 → ℝ) :
    pairLinearMap u v z = z 0 • u + z 1 • v := rfl

/-- A negative-definite checked two-vector Gram matrix forces at least two
negative directions in the ambient symmetric matrix. -/
theorem two_le_matrixInertia_neg_of_negative_pair
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsSymm) (u v : ι → ℝ)
    (hqu : A.toQuadraticForm' u < 0)
    (hdet : 0 < A.toQuadraticForm' u * A.toQuadraticForm' v -
      (dotProduct u (Matrix.mulVec A v)) ^ 2) :
    2 ≤ (matrixInertia A).neg := by
  let f := pairLinearMap u v
  have hcross : dotProduct v (Matrix.mulVec A u) =
      dotProduct u (Matrix.mulVec A v) := by
    rw [dotProduct_mulVec, ← vecMul_transpose, hA.eq, dotProduct_comm]
  have hneg : ∀ z : Fin 2 → ℝ, z ≠ 0 → A.toQuadraticForm' (f z) < 0 := by
    intro z hz
    have hzcoord : z 0 ≠ 0 ∨ z 1 ≠ 0 := by
      by_contra h
      push Not at h
      apply hz
      funext i
      fin_cases i <;> simp [h.1, h.2]
    rw [show f z = z 0 • u + z 1 • v by rfl,
      matrix_quadratic_pair_expansion, hcross]
    have hid :
        A.toQuadraticForm' u *
            (z 0 * z 0 * A.toQuadraticForm' u +
              z 0 * z 1 * dotProduct u (Matrix.mulVec A v) +
              z 0 * z 1 * dotProduct u (Matrix.mulVec A v) +
              z 1 * z 1 * A.toQuadraticForm' v) =
          (A.toQuadraticForm' u * z 0 +
              dotProduct u (Matrix.mulVec A v) * z 1) ^ 2 +
            (A.toQuadraticForm' u * A.toQuadraticForm' v -
              (dotProduct u (Matrix.mulVec A v)) ^ 2) * (z 1) ^ 2 := by
      ring
    have hprod : 0 < A.toQuadraticForm' u *
        (z 0 * z 0 * A.toQuadraticForm' u +
          z 0 * z 1 * dotProduct u (Matrix.mulVec A v) +
          z 0 * z 1 * dotProduct u (Matrix.mulVec A v) +
          z 1 * z 1 * A.toQuadraticForm' v) := by
      rw [hid]
      rcases hzcoord with hz0 | hz1
      · by_cases hz1' : z 1 = 0
        · rw [hz1']
          simp only [mul_zero, add_zero]
          have hsquare : 0 < (A.toQuadraticForm' u * z 0) ^ 2 :=
            sq_pos_of_ne_zero (mul_ne_zero (ne_of_lt hqu) hz0)
          nlinarith
        · have hsquare : 0 < (z 1) ^ 2 := sq_pos_of_ne_zero hz1'
          nlinarith [sq_nonneg
            (A.toQuadraticForm' u * z 0 +
              dotProduct u (Matrix.mulVec A v) * z 1)]
      · have hsquare : 0 < (z 1) ^ 2 := sq_pos_of_ne_zero hz1
        nlinarith [sq_nonneg
          (A.toQuadraticForm' u * z 0 +
            dotProduct u (Matrix.mulVec A v) * z 1)]
    nlinarith
  have hf : Function.Injective f := by
    intro x y hxy
    by_contra hne
    have hsub : x - y ≠ 0 := sub_ne_zero.mpr hne
    have hfsub : f (x - y) = 0 := by simp [hxy]
    have hbad := hneg (x - y) hsub
    rw [hfsub] at hbad
    simp at hbad
  have hnegDef :
      ((-(A.toQuadraticForm'.comp f)).restrict
        (⊤ : Submodule ℝ (Fin 2 → ℝ))).PosDef := by
    intro z hz
    change 0 < -A.toQuadraticForm' (f z.1)
    exact neg_pos.mpr (hneg z.1 (fun hz0 ↦ hz (Subtype.ext hz0)))
  calc
    2 = Module.finrank ℝ (⊤ : Submodule ℝ (Fin 2 → ℝ)) := by simp
    _ ≤ sigNeg (A.toQuadraticForm'.comp f) :=
      le_sigNeg_of_negDef (A.toQuadraticForm'.comp f) hnegDef
    _ ≤ sigNeg A.toQuadraticForm' := by
      have hcomp : (-A.toQuadraticForm').comp f =
          -(A.toQuadraticForm'.comp f) := by
        ext z
        simp [QuadraticMap.comp_apply]
      change sigPos (-(A.toQuadraticForm'.comp f)) ≤
        sigPos (-A.toQuadraticForm')
      rw [← hcomp]
      exact sigPos_comp_le (-A.toQuadraticForm') f hf

/-- Coordinate map from a one-dimensional coefficient space to a line. -/
def lineLinearMap {ι : Type*} (u : ι → ℝ) :
    (Fin 1 → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun z := z 0 • u
  map_add' x y := by
    ext i
    simp
    ring
  map_smul' a x := by
    ext i
    simp
    ring

/-- A vector of negative quadratic value forces at least one negative
direction. -/
theorem one_le_matrixInertia_neg_of_negative
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (u : ι → ℝ)
    (hu : A.toQuadraticForm' u < 0) :
    1 ≤ (matrixInertia A).neg := by
  let f := lineLinearMap u
  have hneg : ∀ z : Fin 1 → ℝ, z ≠ 0 → A.toQuadraticForm' (f z) < 0 := by
    intro z hz
    have hz0 : z 0 ≠ 0 := by
      intro hz0
      apply hz
      funext i
      fin_cases i
      exact hz0
    change A.toQuadraticForm' (z 0 • u) < 0
    rw [QuadraticMap.map_smul]
    simpa [smul_eq_mul] using
      mul_neg_of_pos_of_neg (mul_self_pos.mpr hz0) hu
  have hf : Function.Injective f := by
    intro x y hxy
    by_contra hne
    have hsub : x - y ≠ 0 := sub_ne_zero.mpr hne
    have hfsub : f (x - y) = 0 := by simp [hxy]
    have hbad := hneg (x - y) hsub
    rw [hfsub] at hbad
    simp at hbad
  have hnegDef :
      ((-(A.toQuadraticForm'.comp f)).restrict
        (⊤ : Submodule ℝ (Fin 1 → ℝ))).PosDef := by
    intro z hz
    change 0 < -A.toQuadraticForm' (f z.1)
    exact neg_pos.mpr (hneg z.1 (fun hz0 ↦ hz (Subtype.ext hz0)))
  calc
    1 = Module.finrank ℝ (⊤ : Submodule ℝ (Fin 1 → ℝ)) := by simp
    _ ≤ sigNeg (A.toQuadraticForm'.comp f) :=
      le_sigNeg_of_negDef (A.toQuadraticForm'.comp f) hnegDef
    _ ≤ sigNeg A.toQuadraticForm' := by
      have hcomp : (-A.toQuadraticForm').comp f =
          -(A.toQuadraticForm'.comp f) := by
        ext z
        simp [QuadraticMap.comp_apply]
      change sigPos (-(A.toQuadraticForm'.comp f)) ≤
        sigPos (-A.toQuadraticForm')
      rw [← hcomp]
      exact sigPos_comp_le (-A.toQuadraticForm') f hf

/-- A positive-definite checked two-vector Gram matrix forces at least two
positive directions in the ambient symmetric matrix.  This is the positive
counterpart of `two_le_matrixInertia_neg_of_negative_pair`, obtained by
applying it to the negated matrix. -/
theorem two_le_matrixInertia_pos_of_positive_pair
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsSymm) (u v : ι → ℝ)
    (hqu : 0 < A.toQuadraticForm' u)
    (hdet : 0 < A.toQuadraticForm' u * A.toQuadraticForm' v -
      (dotProduct u (Matrix.mulVec A v)) ^ 2) :
    2 ≤ (matrixInertia A).pos := by
  have hneg : (-A).toQuadraticForm' u < 0 := by
    rw [toQuadraticForm'_neg]
    exact neg_lt_zero.mpr hqu
  have hquadneg (w : ι → ℝ) :
      (-A).toQuadraticForm' w = -A.toQuadraticForm' w := by
    rw [toQuadraticForm'_neg]
    rfl
  have hcrossneg : dotProduct u (Matrix.mulVec (-A) v) =
      -dotProduct u (Matrix.mulVec A v) := by
    rw [Matrix.neg_mulVec, dotProduct_neg]
  have hdetneg :
      0 < (-A).toQuadraticForm' u * (-A).toQuadraticForm' v -
        (dotProduct u (Matrix.mulVec (-A) v)) ^ 2 := by
    rw [hquadneg, hquadneg, hcrossneg]
    nlinarith [hdet]
  have h := two_le_matrixInertia_neg_of_negative_pair
    (-A) hA.neg u v hneg hdetneg
  rw [matrixInertia_neg] at h
  exact h

/-- A positive-definite `2 × 2` principal submatrix gives two positive
directions.  This coordinate form is convenient for exact graph-matrix
arguments. -/
theorem two_le_matrixInertia_pos_of_principal_pair
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsSymm) (x y : ι)
    (hxx : 0 < A x x)
    (hdet : 0 < A x x * A y y - (A x y) ^ 2) :
    2 ≤ (matrixInertia A).pos := by
  apply two_le_matrixInertia_pos_of_positive_pair A hA
    (Pi.single x 1) (Pi.single y 1)
  · simpa [Matrix.toQuadraticForm',
      LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply'] using hxx
  · simpa [Matrix.toQuadraticForm',
      LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply'] using hdet

end SpectralGraph.Inertia
