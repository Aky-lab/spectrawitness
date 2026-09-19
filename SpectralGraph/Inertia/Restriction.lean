import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Tactic
import SpectralGraph.Inertia.Congruence

/-!
# Restriction and interlacing

Monotonicity of quadratic-form indices under injective pullback, and
arbitrary-codimension principal-submatrix signature bounds.
-/

namespace SpectralGraph
namespace Inertia

open QuadraticForm

variable {M M' : Type _}
variable [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
variable [AddCommGroup M'] [Module ℝ M'] [FiniteDimensional ℝ M']

/-- Pullback along an injective linear map cannot increase the positive
signature index. -/
theorem sigPos_comp_le (Q : QuadraticForm ℝ M) (f : M' →ₗ[ℝ] M)
    (hf : Function.Injective f) :
    sigPos (Q.comp f) ≤ sigPos Q := by
  obtain ⟨W, hWdim, hWpos⟩ := exists_finrank_eq_sigPos_and_posDef (Q.comp f)
  let g : W →ₗ[ℝ] M := f.comp W.subtype
  have hg : Function.Injective g := hf.comp W.subtype_injective
  let R : Submodule ℝ M := LinearMap.range g
  have hRdim : Module.finrank ℝ R = Module.finrank ℝ W :=
    LinearMap.finrank_range_of_inj hg
  have hRpos : (Q.restrict R).PosDef := by
    intro y hy
    rcases y.property with ⟨x, hxy⟩
    have hx : x ≠ 0 := by
      intro hx0
      apply hy
      apply Subtype.ext
      simpa [hx0] using hxy.symm
    change 0 < Q y.1
    rw [← hxy]
    simpa [g, QuadraticMap.restrict_apply, QuadraticMap.comp_apply] using hWpos x hx
  calc
    sigPos (Q.comp f) = Module.finrank ℝ W := hWdim.symm
    _ = Module.finrank ℝ R := hRdim.symm
    _ ≤ sigPos Q := le_sigPos_of_posDef Q hRpos

/-- Pullback along an injective linear map cannot increase the negative
signature index. -/
theorem sigNeg_comp_le (Q : QuadraticForm ℝ M) (f : M' →ₗ[ℝ] M)
    (hf : Function.Injective f) :
    sigNeg (Q.comp f) ≤ sigNeg Q := by
  have hcomp : (-Q).comp f = -(Q.comp f) := by
    ext x
    simp [QuadraticMap.comp_apply]
  change sigPos (-(Q.comp f)) ≤ sigPos (-Q)
  rw [← hcomp]
  exact sigPos_comp_le (-Q) f hf

/-- Under an injective codimension-one pullback, the ambient positive index is
at most one larger than the restricted positive index. -/
theorem sigPos_le_comp_add_one (Q : QuadraticForm ℝ M) (f : M' →ₗ[ℝ] M)
    (hf : Function.Injective f)
    (hcodim : Module.finrank ℝ M = Module.finrank ℝ M' + 1) :
    sigPos Q ≤ sigPos (Q.comp f) + 1 := by
  obtain ⟨W, hWdim, hWpos⟩ := exists_finrank_eq_sigPos_and_posDef Q
  let U : Submodule ℝ M' := W.comap f
  have hUpos : ((Q.comp f).restrict U).PosDef := by
    intro x hx
    have hfx : f x.1 ≠ 0 := by
      intro hzero
      have hxzero : x.1 = 0 := hf (by simpa using hzero)
      exact hx (Subtype.ext hxzero)
    simpa [QuadraticMap.restrict_apply, QuadraticMap.comp_apply] using
      hWpos ⟨f x.1, x.2⟩ (by simpa using hfx)
  have hUle : Module.finrank ℝ U ≤ sigPos (Q.comp f) :=
    le_sigPos_of_posDef (Q.comp f) hUpos
  let g : U →ₗ[ℝ] M := f.comp U.subtype
  have hg : Function.Injective g := hf.comp U.subtype_injective
  have hrange : LinearMap.range g = W ⊓ LinearMap.range f := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.property, ⟨x.1, rfl⟩⟩
    · rintro ⟨hyW, x, rfl⟩
      exact ⟨⟨x, hyW⟩, rfl⟩
  have hUdim : Module.finrank ℝ U =
      Module.finrank ℝ ↑(W ⊓ LinearMap.range f) := by
    rw [← hrange]
    exact (LinearMap.finrank_range_of_inj hg).symm
  have hfrange : Module.finrank ℝ (LinearMap.range f) = Module.finrank ℝ M' :=
    LinearMap.finrank_range_of_inj hf
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq W (LinearMap.range f)
  have hsup : Module.finrank ℝ ↑(W ⊔ LinearMap.range f) ≤ Module.finrank ℝ M :=
    Submodule.finrank_le _
  rw [hWdim, hfrange, ← hUdim] at hdim
  rw [hcodim] at hsup
  omega

/-- An injective pullback of arbitrary finite codimension loses at most that
codimension from the positive index. -/
theorem sigPos_le_comp_add_codim
    (Q : QuadraticForm ℝ M) (f : M' →ₗ[ℝ] M)
    (hf : Function.Injective f) (d : Nat)
    (hcodim : Module.finrank ℝ M = Module.finrank ℝ M' + d) :
    sigPos Q ≤ sigPos (Q.comp f) + d := by
  obtain ⟨W, hWdim, hWpos⟩ := exists_finrank_eq_sigPos_and_posDef Q
  let U : Submodule ℝ M' := W.comap f
  have hUpos : ((Q.comp f).restrict U).PosDef := by
    intro x hx
    have hfx : f x.1 ≠ 0 := by
      intro hzero
      have hxzero : x.1 = 0 := hf (by simpa using hzero)
      exact hx (Subtype.ext hxzero)
    simpa [QuadraticMap.restrict_apply, QuadraticMap.comp_apply] using
      hWpos ⟨f x.1, x.2⟩ (by simpa using hfx)
  have hUle : Module.finrank ℝ U ≤ sigPos (Q.comp f) :=
    le_sigPos_of_posDef (Q.comp f) hUpos
  let g : U →ₗ[ℝ] M := f.comp U.subtype
  have hg : Function.Injective g := hf.comp U.subtype_injective
  have hrange : LinearMap.range g = W ⊓ LinearMap.range f := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.property, ⟨x.1, rfl⟩⟩
    · rintro ⟨hyW, x, rfl⟩
      exact ⟨⟨x, hyW⟩, rfl⟩
  have hUdim : Module.finrank ℝ U =
      Module.finrank ℝ ↑(W ⊓ LinearMap.range f) := by
    rw [← hrange]
    exact (LinearMap.finrank_range_of_inj hg).symm
  have hfrange : Module.finrank ℝ (LinearMap.range f) = Module.finrank ℝ M' :=
    LinearMap.finrank_range_of_inj hf
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq W (LinearMap.range f)
  have hsup : Module.finrank ℝ ↑(W ⊔ LinearMap.range f) ≤ Module.finrank ℝ M :=
    Submodule.finrank_le _
  rw [hWdim, hfrange, ← hUdim] at hdim
  rw [hcodim] at hsup
  omega

/-- Pullback along an injective linear map cannot increase the total
nonpositive index (negative index plus radical dimension). -/
theorem sigNeg_add_radical_comp_le
    (Q : QuadraticForm ℝ M) (f : M' →ₗ[ℝ] M)
    (hf : Function.Injective f) :
    sigNeg (Q.comp f) +
        Module.finrank ℝ (QuadraticMap.radical (Q.comp f)) ≤
      sigNeg Q + Module.finrank ℝ (QuadraticMap.radical Q) := by
  have hdimLe : Module.finrank ℝ M' ≤ Module.finrank ℝ M :=
    LinearMap.finrank_le_finrank_of_injective hf
  let d := Module.finrank ℝ M - Module.finrank ℝ M'
  have hdim : Module.finrank ℝ M = Module.finrank ℝ M' + d := by
    dsimp only [d]
    omega
  have hpos := sigPos_le_comp_add_codim Q f hf d hdim
  have hQdim := sigPos_add_sigNeg_add_radical (Q := Q)
  have hcompDim := sigPos_add_sigNeg_add_radical (Q := Q.comp f)
  omega

/-- Injective codimension-one pullback interlaces the positive signature
index. -/
theorem sigPos_comp_interlaces (Q : QuadraticForm ℝ M) (f : M' →ₗ[ℝ] M)
    (hf : Function.Injective f)
    (hcodim : Module.finrank ℝ M = Module.finrank ℝ M' + 1) :
    sigPos (Q.comp f) ≤ sigPos Q ∧ sigPos Q ≤ sigPos (Q.comp f) + 1 :=
  ⟨sigPos_comp_le Q f hf, sigPos_le_comp_add_one Q f hf hcodim⟩

/-- Injective codimension-one pullback interlaces the negative signature
index. -/
theorem sigNeg_comp_interlaces (Q : QuadraticForm ℝ M) (f : M' →ₗ[ℝ] M)
    (hf : Function.Injective f)
    (hcodim : Module.finrank ℝ M = Module.finrank ℝ M' + 1) :
    sigNeg (Q.comp f) ≤ sigNeg Q ∧ sigNeg Q ≤ sigNeg (Q.comp f) + 1 := by
  have hcomp : (-Q).comp f = -(Q.comp f) := by
    ext x
    simp [QuadraticMap.comp_apply]
  change sigPos (-(Q.comp f)) ≤ sigPos (-Q) ∧
    sigPos (-Q) ≤ sigPos (-(Q.comp f)) + 1
  rw [← hcomp]
  exact sigPos_comp_interlaces (-Q) f hf hcodim

/-- The integer signatures of an ambient form and an injective
codimension-one pullback differ by at most one, stated as two additive
inequalities. -/
theorem signature_comp_interlaces
    (Q : QuadraticForm ℝ M) (f : M' →ₗ[ℝ] M)
    (hf : Function.Injective f)
    (hcodim : Module.finrank ℝ M = Module.finrank ℝ M' + 1) :
    ((sigPos (Q.comp f) : Nat) : Int) - ((sigNeg (Q.comp f) : Nat) : Int) ≤
        ((sigPos Q : Nat) : Int) - ((sigNeg Q : Nat) : Int) + 1 ∧
      ((sigPos Q : Nat) : Int) - ((sigNeg Q : Nat) : Int) ≤
        ((sigPos (Q.comp f) : Nat) : Int) - ((sigNeg (Q.comp f) : Nat) : Int) + 1 := by
  have hp := sigPos_comp_interlaces Q f hf hcodim
  have hn := sigNeg_comp_interlaces Q f hf hcodim
  omega

/-- The ambient signature is at most the restricted signature plus the
codimension. -/
theorem signature_le_comp_add_codim
    (Q : QuadraticForm ℝ M) (f : M' →ₗ[ℝ] M)
    (hf : Function.Injective f) (d : Nat)
    (hcodim : Module.finrank ℝ M = Module.finrank ℝ M' + d) :
    ((sigPos Q : Nat) : Int) - ((sigNeg Q : Nat) : Int) ≤
      ((sigPos (Q.comp f) : Nat) : Int) -
        ((sigNeg (Q.comp f) : Nat) : Int) + d := by
  have hp := sigPos_le_comp_add_codim Q f hf d hcodim
  have hcomp : (-Q).comp f = -(Q.comp f) := by
    ext x
    simp [QuadraticMap.comp_apply]
  have hn : sigNeg (Q.comp f) ≤ sigNeg Q := by
    change sigPos (-(Q.comp f)) ≤ sigPos (-Q)
    rw [← hcomp]
    exact sigPos_comp_le (-Q) f hf
  omega

section Matrix

open Matrix

variable {ι κ : Type _}
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- For a symmetric real matrix, the radical of its quadratic form is the
kernel of matrix-vector multiplication.  This generic bridge belongs with
the reusable inertia API rather than any one certificate. -/
theorem radical_toQuadraticForm'_eq_ker_mulVecLin
    (A : Matrix ι ι ℝ) (hA : A.IsSymm) :
    QuadraticMap.radical A.toQuadraticForm' =
      LinearMap.ker A.mulVecLin := by
  rw [QuadraticMap.radical_eq_ker_associated]
  have hassoc : QuadraticMap.associated A.toQuadraticForm' =
      Matrix.toLinearMap₂' ℝ A := by
    apply QuadraticMap.associated_left_inverse ℝ
    intro x y
    rw [Matrix.toLinearMap₂'_apply', Matrix.toLinearMap₂'_apply',
      dotProduct_mulVec, ← vecMul_transpose, hA.eq, dotProduct_comm]
  rw [hassoc]
  ext x
  simp only [LinearMap.mem_ker]
  constructor
  · intro hx
    change A *ᵥ x = 0
    apply dotProduct_eq_zero
    intro y
    rw [← hA.eq, mulVec_transpose]
    rw [← dotProduct_mulVec]
    simpa [Matrix.toLinearMap₂'_apply'] using congrArg (fun f ↦ f y) hx
  · intro hx
    have hx' : A *ᵥ x = 0 := by simpa using hx
    apply LinearMap.ext
    intro y
    simp only [LinearMap.zero_apply]
    rw [Matrix.toLinearMap₂'_apply', dotProduct_mulVec,
      ← mulVec_transpose, hA.eq, hx', zero_dotProduct]

/-- A symmetric real matrix with zero semantic nullity is invertible. -/
theorem matrix_isUnit_of_matrixInertia_zero_eq_zero
    (A : Matrix ι ι ℝ) (hA : A.IsSymm)
    (hzero : (matrixInertia A).zero = 0) : IsUnit A := by
  have hfin : Module.finrank ℝ ↥(LinearMap.ker A.mulVecLin) = 0 := by
    rw [← radical_toQuadraticForm'_eq_ker_mulVecLin A hA]
    exact hzero
  have hker : LinearMap.ker A.mulVecLin = ⊥ :=
    Submodule.finrank_eq_zero.mp hfin
  exact Matrix.mulVec_injective_iff_isUnit.mp
    (LinearMap.ker_eq_bot.mp hker)

/-- A symmetric invertible real matrix has zero semantic nullity. -/
theorem matrixInertia_zero_eq_zero_of_isUnit
    (A : Matrix ι ι ℝ) (hA : A.IsSymm)
    (hunit : IsUnit A) : (matrixInertia A).zero = 0 := by
  have hinj : Function.Injective A.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hunit
  have hker : LinearMap.ker A.mulVecLin = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinj
  change Module.finrank ℝ ↥(QuadraticMap.radical A.toQuadraticForm') = 0
  rw [radical_toQuadraticForm'_eq_ker_mulVecLin A hA, hker]
  simp

/-- A family of exact kernel vectors with distinct private coordinates is
linearly independent, so its cardinality is bounded by matrix nullity. -/
theorem card_le_matrixInertia_zero_of_private_kernel
    {J : Type*} [Fintype J] [DecidableEq J]
    (A : Matrix ι ι ℝ) (hA : A.IsSymm)
    (privateCoord : J → ι) (relation : J → ι → ℝ)
    (hprivate : ∀ j, relation j (privateCoord j) = 1)
    (hoff : ∀ j k, k ≠ j → relation k (privateCoord j) = 0)
    (hker : ∀ j, Matrix.mulVec A (relation j) = 0) :
    Fintype.card J ≤ (matrixInertia A).zero := by
  let w : J → LinearMap.ker A.mulVecLin := fun j ↦
    ⟨relation j, by
      simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      exact hker j⟩
  have hli : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff]
    intro g hsum j
    have hcoord := congrArg
      (fun q : LinearMap.ker A.mulVecLin ↦ q.1 (privateCoord j)) hsum
    have hcoord' : ∑ i : J, g i * relation i (privateCoord j) = 0 := by
      simpa [w] using hcoord
    calc
      g j = ∑ i : J, g i * relation i (privateCoord j) := by
        symm
        calc
          (∑ i : J, g i * relation i (privateCoord j)) =
              g j * relation j (privateCoord j) := by
            apply Fintype.sum_eq_single j
            intro k hkj
            rw [hoff j k hkj, mul_zero]
          _ = g j := by rw [hprivate, mul_one]
      _ = 0 := hcoord'
  have hcard : Fintype.card J ≤
      Module.finrank ℝ (LinearMap.ker A.mulVecLin) :=
    hli.fintype_card_le_finrank
  change Fintype.card J ≤
    Module.finrank ℝ (QuadraticMap.radical A.toQuadraticForm')
  rw [radical_toQuadraticForm'_eq_ker_mulVecLin A hA]
  exact hcard

/-- Coordinate extension by zero along an embedding of finite index types. -/
noncomputable def coordinateEmbedding (e : κ ↪ ι) :
    (κ → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  Function.ExtendByZero.linearMap ℝ e

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
@[simp] theorem coordinateEmbedding_apply_image
    (e : κ ↪ ι) (x : κ → ℝ) (k : κ) :
    coordinateEmbedding e x (e k) = x k := by
  change Function.extend e x 0 (e k) = x k
  exact congr_fun (Function.extend_comp e.injective x 0) k

omit [DecidableEq κ] in
/-- A finite sum containing an extended-by-zero coordinate vector reduces to
the embedded index type. -/
private theorem sum_coordinateEmbedding_mul
    (e : κ ↪ ι) (x : κ → ℝ) (F : ι → ℝ) :
    (∑ i : ι, coordinateEmbedding e x i * F i) =
      ∑ k : κ, x k * F (e k) := by
  classical
  have hsub : Finset.univ.image e ⊆ (Finset.univ : Finset ι) := by simp
  have hout : ∀ i ∈ (Finset.univ : Finset ι), i ∉ Finset.univ.image e →
      coordinateEmbedding e x i * F i = 0 := by
    intro i hi hin
    have hn : ¬∃ k, e k = i := by simpa using hin
    rw [show coordinateEmbedding e x i = 0 by
      exact Function.extend_apply' x (0 : ι → ℝ) i hn]
    simp
  rw [← Finset.sum_subset hsub hout]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [coordinateEmbedding_apply_image]
  · exact e.injective.injOn

omit [DecidableEq κ] in
private theorem sum_const_mul_coordinateEmbedding
    (e : κ ↪ ι) (x : κ → ℝ) (c : ℝ) (F : ι → ℝ) :
    (∑ i : ι, c * (coordinateEmbedding e x i * F i)) =
      ∑ k : κ, c * (x k * F (e k)) := by
  simpa [Finset.mul_sum] using
    congrArg (fun z : ℝ ↦ c * z) (sum_coordinateEmbedding_mul e x F)

omit [DecidableEq κ] in
/-- Multiplying an extended-by-zero vector and then reading an embedded
coordinate agrees with multiplying by the corresponding principal
submatrix. -/
theorem mulVec_coordinateEmbedding_apply_image
    (A : Matrix ι ι ℝ) (e : κ ↪ ι) (x : κ → ℝ) (k : κ) :
    Matrix.mulVec A (coordinateEmbedding e x) (e k) =
      Matrix.mulVec (A.submatrix e e) x k := by
  simp only [Matrix.mulVec, Matrix.submatrix_apply]
  calc
    (∑ i : ι, A (e k) i * coordinateEmbedding e x i) =
        ∑ i : ι, coordinateEmbedding e x i * A (e k) i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact mul_comm _ _
    _ = ∑ j : κ, x j * A (e k) (e j) :=
      sum_coordinateEmbedding_mul e x (fun i ↦ A (e k) i)
    _ = ∑ j : κ, A (e k) (e j) * x j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact mul_comm _ _

/-- The quadratic form of a principal submatrix is the pullback of the full
quadratic form along coordinate extension by zero. -/
theorem submatrix_toQuadraticForm'_eq_comp
    (A : Matrix ι ι ℝ) (e : κ ↪ ι) :
    (A.submatrix e e).toQuadraticForm' =
      A.toQuadraticForm'.comp (coordinateEmbedding e) := by
  ext x
  simp only [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply,
    LinearMap.BilinMap.toQuadraticMap_apply, QuadraticMap.comp_apply,
    Matrix.submatrix_apply]
  simp only [smul_eq_mul]
  symm
  calc
    (∑ i : ι, ∑ j : ι,
        coordinateEmbedding e x i * (coordinateEmbedding e x j * A i j)) =
        ∑ i : ι, ∑ k : κ,
          coordinateEmbedding e x i * (x k * A i (e k)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact sum_const_mul_coordinateEmbedding e x
        (coordinateEmbedding e x i) (fun j ↦ A i j)
    _ = ∑ k : κ, ∑ i : ι,
        coordinateEmbedding e x i * (x k * A i (e k)) := Finset.sum_comm
    _ = ∑ k : κ, ∑ h : κ, x h * (x k * A (e h) (e k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact sum_coordinateEmbedding_mul e x (fun i ↦ x k * A i (e k))
    _ = ∑ h : κ, ∑ k : κ, x h * (x k * A (e h) (e k)) := Finset.sum_comm

/-- A principal submatrix cannot have more positive directions than the
ambient matrix. -/
theorem matrixInertia_submatrix_pos_le
    (A : Matrix ι ι ℝ) (e : κ ↪ ι) :
    (matrixInertia (A.submatrix e e)).pos ≤ (matrixInertia A).pos := by
  have hf : Function.Injective (coordinateEmbedding e) := by
    simpa [coordinateEmbedding, Function.ExtendByZero.linearMap] using
      Function.extend_injective e.injective (0 : ι → ℝ)
  change sigPos (A.submatrix e e).toQuadraticForm' ≤
    sigPos A.toQuadraticForm'
  rw [submatrix_toQuadraticForm'_eq_comp]
  exact sigPos_comp_le A.toQuadraticForm' (coordinateEmbedding e) hf

/-- A principal submatrix cannot have more negative directions than the
ambient matrix. -/
theorem matrixInertia_submatrix_neg_le
    (A : Matrix ι ι ℝ) (e : κ ↪ ι) :
    (matrixInertia (A.submatrix e e)).neg ≤ (matrixInertia A).neg := by
  have hf : Function.Injective (coordinateEmbedding e) := by
    simpa [coordinateEmbedding, Function.ExtendByZero.linearMap] using
      Function.extend_injective e.injective (0 : ι → ℝ)
  change sigNeg (A.submatrix e e).toQuadraticForm' ≤
    sigNeg A.toQuadraticForm'
  rw [submatrix_toQuadraticForm'_eq_comp]
  exact sigNeg_comp_le A.toQuadraticForm' (coordinateEmbedding e) hf

/-- The nonpositive index of a principal submatrix is at most the
nonpositive index of the ambient matrix. -/
theorem matrixInertia_submatrix_neg_add_zero_le
    (A : Matrix ι ι ℝ) (e : κ ↪ ι) :
    (matrixInertia (A.submatrix e e)).neg +
        (matrixInertia (A.submatrix e e)).zero ≤
      (matrixInertia A).neg + (matrixInertia A).zero := by
  have hcard_le : Fintype.card κ ≤ Fintype.card ι :=
    Fintype.card_le_of_injective e e.injective
  let d := Fintype.card ι - Fintype.card κ
  have hcard : Fintype.card ι = Fintype.card κ + d := by
    dsimp [d]
    omega
  have hf : Function.Injective (coordinateEmbedding e) := by
    simpa [coordinateEmbedding, Function.ExtendByZero.linearMap] using
      Function.extend_injective e.injective (0 : ι → ℝ)
  have hcodim : Module.finrank ℝ (ι → ℝ) =
      Module.finrank ℝ (κ → ℝ) + d := by
    simpa [Module.finrank_fintype_fun_eq_card] using hcard
  have hpos := sigPos_le_comp_add_codim A.toQuadraticForm'
    (coordinateEmbedding e) hf d hcodim
  rw [← submatrix_toQuadraticForm'_eq_comp] at hpos
  have hAorder := matrixInertia_order A
  have hPorder := matrixInertia_order (A.submatrix e e)
  change (matrixInertia A).pos ≤
      (matrixInertia (A.submatrix e e)).pos + d at hpos
  simp only [Inertia.order] at hAorder hPorder
  omega

/-- If the ambient matrix is nonsingular, every null direction of a
principal submatrix consumes an additional ambient negative direction. -/
theorem matrixInertia_submatrix_neg_add_zero_le_of_zero_eq_zero
    (A : Matrix ι ι ℝ) (e : κ ↪ ι)
    (hzero : (matrixInertia A).zero = 0) :
    (matrixInertia (A.submatrix e e)).neg +
        (matrixInertia (A.submatrix e e)).zero ≤
      (matrixInertia A).neg := by
  have hcard_le : Fintype.card κ ≤ Fintype.card ι :=
    Fintype.card_le_of_injective e e.injective
  let d := Fintype.card ι - Fintype.card κ
  have hcard : Fintype.card ι = Fintype.card κ + d := by
    dsimp [d]
    omega
  have hf : Function.Injective (coordinateEmbedding e) := by
    simpa [coordinateEmbedding, Function.ExtendByZero.linearMap] using
      Function.extend_injective e.injective (0 : ι → ℝ)
  have hcodim : Module.finrank ℝ (ι → ℝ) =
      Module.finrank ℝ (κ → ℝ) + d := by
    simpa [Module.finrank_fintype_fun_eq_card] using hcard
  have hpos := sigPos_le_comp_add_codim A.toQuadraticForm'
    (coordinateEmbedding e) hf d hcodim
  rw [← submatrix_toQuadraticForm'_eq_comp] at hpos
  have hAorder := matrixInertia_order A
  have hPorder := matrixInertia_order (A.submatrix e e)
  change (matrixInertia A).pos ≤
      (matrixInertia (A.submatrix e e)).pos + d at hpos
  simp only [Inertia.order] at hAorder hPorder
  omega

/-- Cauchy interlacing for matrix signature under deletion of one principal
coordinate, stated without choosing an ordering of the index types. -/
theorem matrixSignature_submatrix_interlaces
    (A : Matrix ι ι ℝ) (e : κ ↪ ι)
    (hcard : Fintype.card ι = Fintype.card κ + 1) :
    matrixSignature (A.submatrix e e) ≤ matrixSignature A + 1 ∧
      matrixSignature A ≤ matrixSignature (A.submatrix e e) + 1 := by
  have hf : Function.Injective (coordinateEmbedding e) := by
    simpa [coordinateEmbedding, Function.ExtendByZero.linearMap] using
      Function.extend_injective e.injective (0 : ι → ℝ)
  have hcodim : Module.finrank ℝ (ι → ℝ) = Module.finrank ℝ (κ → ℝ) + 1 := by
    simpa [Module.finrank_fintype_fun_eq_card] using hcard
  have h := signature_comp_interlaces A.toQuadraticForm'
    (coordinateEmbedding e) hf hcodim
  rw [← submatrix_toQuadraticForm'_eq_comp] at h
  simpa [matrixSignature_eq] using h

/-- Arbitrary-codimension principal restriction bound for matrix signature. -/
theorem matrixSignature_le_submatrix_add_codim
    (A : Matrix ι ι ℝ) (e : κ ↪ ι) (d : Nat)
    (hcard : Fintype.card ι = Fintype.card κ + d) :
    matrixSignature A ≤ matrixSignature (A.submatrix e e) + d := by
  have hf : Function.Injective (coordinateEmbedding e) := by
    simpa [coordinateEmbedding, Function.ExtendByZero.linearMap] using
      Function.extend_injective e.injective (0 : ι → ℝ)
  have hcodim : Module.finrank ℝ (ι → ℝ) = Module.finrank ℝ (κ → ℝ) + d := by
    simpa [Module.finrank_fintype_fun_eq_card] using hcard
  have h := signature_le_comp_add_codim A.toQuadraticForm'
    (coordinateEmbedding e) hf d hcodim
  rw [← submatrix_toQuadraticForm'_eq_comp] at h
  simpa [matrixSignature_eq] using h

/-- Coordinate extension along an equivalence is a linear equivalence. -/
noncomputable def coordinateLinearEquiv (e : κ ≃ ι) :
    (κ → ℝ) ≃ₗ[ℝ] (ι → ℝ) :=
  LinearEquiv.ofBijective (coordinateEmbedding e.toEmbedding) ⟨by
    simpa [coordinateEmbedding, Function.ExtendByZero.linearMap] using
      Function.extend_injective e.injective (0 : ι → ℝ), by
    intro y
    refine ⟨fun x ↦ y (e x), ?_⟩
    funext z
    obtain ⟨x, rfl⟩ := e.surjective z
    exact coordinateEmbedding_apply_image e.toEmbedding _ x⟩

/-- Reindexing both coordinates of a matrix along an equivalence preserves
its complete inertia triple. -/
theorem matrixInertia_submatrix_equiv
    (A : Matrix ι ι ℝ) (e : κ ≃ ι) :
    matrixInertia (A.submatrix e e) = matrixInertia A := by
  have hquad := submatrix_toQuadraticForm'_eq_comp A e.toEmbedding
  have hiso := QuadraticMap.isometryEquivOfCompLinearEquiv
    A.toQuadraticForm' (coordinateLinearEquiv e)
  have hequiv : QuadraticMap.Equivalent A.toQuadraticForm'
      (A.submatrix e e).toQuadraticForm' := by
    change QuadraticMap.Equivalent A.toQuadraticForm'
      (A.submatrix e.toEmbedding e.toEmbedding).toQuadraticForm'
    rw [hquad]
    exact ⟨hiso⟩
  exact (matrixInertia_eq_of_equivalent A (A.submatrix e e) hequiv).symm

/-- Reindexing both coordinates of a matrix along an equivalence preserves
its signature. -/
theorem matrixSignature_submatrix_equiv
    (A : Matrix ι ι ℝ) (e : κ ≃ ι) :
    matrixSignature (A.submatrix e e) = matrixSignature A := by
  have hquad := submatrix_toQuadraticForm'_eq_comp A e.toEmbedding
  have hiso := QuadraticMap.isometryEquivOfCompLinearEquiv
    A.toQuadraticForm' (coordinateLinearEquiv e)
  have hequiv : QuadraticMap.Equivalent A.toQuadraticForm'
      (A.submatrix e e).toQuadraticForm' := by
    change QuadraticMap.Equivalent A.toQuadraticForm'
      (A.submatrix e.toEmbedding e.toEmbedding).toQuadraticForm'
    rw [hquad]
    exact ⟨hiso⟩
  exact (matrixSignature_eq_of_equivalent A (A.submatrix e e) hequiv).symm

end Matrix

end Inertia
end SpectralGraph
