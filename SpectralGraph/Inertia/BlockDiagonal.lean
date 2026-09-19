import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic
import SpectralGraph.Inertia.Congruence

/-!
# Block-diagonal inertia infrastructure

A `2 × 2` block-diagonal matrix represents the product of the quadratic forms
represented by its two diagonal blocks.  This file packages that identification
through the canonical linear equivalence

    (ι ⊕ κ → ℝ) ≃ₗ[ℝ] (ι → ℝ) × (κ → ℝ).

It is the structural input for additivity of inertia under orthogonal direct
sums, used by the shifted-Gram theorem.
-/

open Matrix

namespace SpectralGraph
namespace Inertia

variable {ι κ : Type _}
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- A two-block diagonal matrix. -/
def twoBlockDiag (A : Matrix ι ι ℝ) (D : Matrix κ κ ℝ) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
  Matrix.fromBlocks A 0 0 D

/-- Evaluation of a block-diagonal quadratic form splits into the sum of the
quadratic forms of the two diagonal blocks. -/
theorem twoBlockDiag_toQuadraticForm_apply
    (A : Matrix ι ι ℝ) (D : Matrix κ κ ℝ) (x : ι ⊕ κ → ℝ) :
    (twoBlockDiag A D).toQuadraticForm' x =
      A.toQuadraticForm' (x ∘ Sum.inl) +
        D.toQuadraticForm' (x ∘ Sum.inr) := by
  simp [twoBlockDiag, Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply,
    Fintype.sum_sum_type]

/-- The quadratic form of a two-block diagonal matrix is isometric to the
product of the quadratic forms of its diagonal blocks. -/
noncomputable def twoBlockDiagIsometryEquiv
    (A : Matrix ι ι ℝ) (D : Matrix κ κ ℝ) :
    (twoBlockDiag A D).toQuadraticForm'.IsometryEquiv
      (A.toQuadraticForm'.prod D.toQuadraticForm') where
  toLinearEquiv := LinearEquiv.sumArrowLequivProdArrow ι κ ℝ ℝ
  map_app' := by
    intro x
    rw [QuadraticMap.prod_apply, twoBlockDiag_toQuadraticForm_apply]
    rfl

/-- Equivalent-form packaging of `twoBlockDiagIsometryEquiv`. -/
theorem twoBlockDiag_equivalent_prod
    (A : Matrix ι ι ℝ) (D : Matrix κ κ ℝ) :
    QuadraticMap.Equivalent
      (twoBlockDiag A D).toQuadraticForm'
      (A.toQuadraticForm'.prod D.toQuadraticForm') :=
  ⟨twoBlockDiagIsometryEquiv A D⟩

omit [DecidableEq ι] [DecidableEq κ] in
/-- The cardinality of a predicate on a sum type is the sum of its
cardinalities on the two summands. -/
theorem ncard_sum_predicate (p : ι ⊕ κ → Prop) :
    {x | p x}.ncard =
      {i | p (Sum.inl i)}.ncard + {k | p (Sum.inr k)}.ncard := by
  have hset : {x | p x} =
      Set.sumEquiv.symm ({i | p (Sum.inl i)}, {k | p (Sum.inr k)}) := by
    ext x
    cases x <;> simp [Set.sumEquiv_symm_apply]
  rw [hset, Set.sumEquiv_symm_apply,
    Set.ncard_union_eq Set.disjoint_image_inl_image_inr]
  rw [Set.ncard_image_of_injective _ Sum.inl_injective,
    Set.ncard_image_of_injective _ Sum.inr_injective]

/-- A product of weighted sums of squares is isometric to the single
weighted sum indexed by the sum type. -/
private noncomputable def weightedSumSquaresProdIsometryEquiv
    {a b : Type _} [Fintype a] [Fintype b]
    (wa : a → ℝ) (wb : b → ℝ) :
    ((QuadraticMap.weightedSumSquares ℝ wa).prod
      (QuadraticMap.weightedSumSquares ℝ wb)).IsometryEquiv
      (QuadraticMap.weightedSumSquares ℝ (Sum.elim wa wb)) where
  toLinearEquiv := (LinearEquiv.sumArrowLequivProdArrow a b ℝ ℝ).symm
  map_app' := by
    rintro ⟨x, y⟩
    simp [QuadraticMap.weightedSumSquares_apply, Fintype.sum_sum_type]

omit [DecidableEq ι] [DecidableEq κ] in
/-- Positive signature is additive under products of finite-dimensional real
quadratic forms on coordinate spaces. -/
theorem sigPos_prod
    (Qι : QuadraticForm ℝ (ι → ℝ)) (Qκ : QuadraticForm ℝ (κ → ℝ)) :
    sigPos (Qι.prod Qκ) = sigPos Qι + sigPos Qκ := by
  obtain ⟨wι, hι⟩ := Qι.equivalent_weightedSumSquares
  obtain ⟨wκ, hκ⟩ := Qκ.equivalent_weightedSumSquares
  rw [(hι.prod hκ).sigPos_eq,
    (show QuadraticMap.Equivalent
      ((QuadraticMap.weightedSumSquares ℝ wι).prod
        (QuadraticMap.weightedSumSquares ℝ wκ))
      (QuadraticMap.weightedSumSquares ℝ (Sum.elim wι wκ)) from
        ⟨weightedSumSquaresProdIsometryEquiv wι wκ⟩).sigPos_eq,
    hι.sigPos_eq, hκ.sigPos_eq,
    QuadraticForm.sigPos_weightedSumSquares,
    QuadraticForm.sigPos_weightedSumSquares,
    QuadraticForm.sigPos_weightedSumSquares]
  exact ncard_sum_predicate (fun x ↦ 0 < Sum.elim wι wκ x)

omit [DecidableEq ι] [DecidableEq κ] in
/-- Negative signature is additive under products of finite-dimensional real
quadratic forms on coordinate spaces. -/
theorem sigNeg_prod
    (Qι : QuadraticForm ℝ (ι → ℝ)) (Qκ : QuadraticForm ℝ (κ → ℝ)) :
    sigNeg (Qι.prod Qκ) = sigNeg Qι + sigNeg Qκ := by
  obtain ⟨wι, hι⟩ := Qι.equivalent_weightedSumSquares
  obtain ⟨wκ, hκ⟩ := Qκ.equivalent_weightedSumSquares
  rw [(hι.prod hκ).sigNeg_eq,
    (show QuadraticMap.Equivalent
      ((QuadraticMap.weightedSumSquares ℝ wι).prod
        (QuadraticMap.weightedSumSquares ℝ wκ))
      (QuadraticMap.weightedSumSquares ℝ (Sum.elim wι wκ)) from
        ⟨weightedSumSquaresProdIsometryEquiv wι wκ⟩).sigNeg_eq,
    hι.sigNeg_eq, hκ.sigNeg_eq,
    QuadraticForm.sigNeg_weightedSumSquares,
    QuadraticForm.sigNeg_weightedSumSquares,
    QuadraticForm.sigNeg_weightedSumSquares]
  exact ncard_sum_predicate (fun x ↦ Sum.elim wι wκ x < 0)

/-- Semantic inertia is additive over a two-block diagonal matrix. -/
theorem matrixInertia_twoBlockDiag
    (A : Matrix ι ι ℝ) (D : Matrix κ κ ℝ) :
    matrixInertia (twoBlockDiag A D) =
      { pos := (matrixInertia A).pos + (matrixInertia D).pos
        zero := (matrixInertia A).zero + (matrixInertia D).zero
        neg := (matrixInertia A).neg + (matrixInertia D).neg } := by
  have hpos :
      (matrixInertia (twoBlockDiag A D)).pos =
        (matrixInertia A).pos + (matrixInertia D).pos := by
    change sigPos (twoBlockDiag A D).toQuadraticForm' =
      sigPos A.toQuadraticForm' + sigPos D.toQuadraticForm'
    rw [(twoBlockDiag_equivalent_prod A D).sigPos_eq, sigPos_prod]
  have hneg :
      (matrixInertia (twoBlockDiag A D)).neg =
        (matrixInertia A).neg + (matrixInertia D).neg := by
    change sigNeg (twoBlockDiag A D).toQuadraticForm' =
      sigNeg A.toQuadraticForm' + sigNeg D.toQuadraticForm'
    rw [(twoBlockDiag_equivalent_prod A D).sigNeg_eq, sigNeg_prod]
  have hblock := matrixInertia_order (twoBlockDiag A D)
  have hA := matrixInertia_order A
  have hD := matrixInertia_order D
  have hzero :
      (matrixInertia (twoBlockDiag A D)).zero =
        (matrixInertia A).zero + (matrixInertia D).zero := by
    simp only [Inertia.order] at hblock hA hD
    rw [Fintype.card_sum] at hblock
    omega
  rcases hI : matrixInertia (twoBlockDiag A D) with ⟨p, z, n⟩
  simp only [hI] at hpos hzero hneg
  cases hpos
  cases hzero
  cases hneg
  rfl

/-- Multiplication of a real matrix by a positive scalar preserves semantic
inertia.  The congruence uses the scalar matrix `sqrt(c) I`. -/
theorem matrixInertia_pos_smul (A : Matrix ι ι ℝ) {c : ℝ} (hc : 0 < c) :
    matrixInertia (c • A) = matrixInertia A := by
  let s : ℝ := Real.sqrt c
  let P : Matrix ι ι ℝ := s • (1 : Matrix ι ι ℝ)
  have hs : s ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hc)
  letI : Invertible P := by
    apply invertibleOfLeftInverse P ((s⁻¹) • (1 : Matrix ι ι ℝ))
    ext i j
    simp [P, hs]
  symm
  apply matrixInertia_eq_of_congr A (c • A) P
  rw [show c = s * s by simpa [s, pow_two] using (Real.sq_sqrt hc.le).symm]
  simpa [P] using (smul_smul s s A).symm

/-- The identity matrix represents the positive definite sum of coordinate
squares. -/
private theorem one_toQuadraticForm_eq_weightedSumSquares :
    (1 : Matrix ι ι ℝ).toQuadraticForm' =
      QuadraticMap.weightedSumSquares ℝ (fun _ : ι ↦ (1 : ℝ)) := by
  ext x
  simp [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply,
    QuadraticMap.weightedSumSquares_apply, Matrix.one_apply]

/-- The identity matrix has inertia `(card ι, 0, 0)`. -/
theorem matrixInertia_one :
    matrixInertia (1 : Matrix ι ι ℝ) =
      { pos := Fintype.card ι, zero := 0, neg := 0 } := by
  have hpos : (matrixInertia (1 : Matrix ι ι ℝ)).pos = Fintype.card ι := by
    change sigPos (1 : Matrix ι ι ℝ).toQuadraticForm' = Fintype.card ι
    rw [one_toQuadraticForm_eq_weightedSumSquares,
      QuadraticForm.sigPos_weightedSumSquares]
    norm_num
  have hneg : (matrixInertia (1 : Matrix ι ι ℝ)).neg = 0 := by
    change sigNeg (1 : Matrix ι ι ℝ).toQuadraticForm' = 0
    rw [one_toQuadraticForm_eq_weightedSumSquares,
      QuadraticForm.sigNeg_weightedSumSquares]
    have hset : {i : ι | (1 : ℝ) < 0} = ∅ := by ext i; norm_num
    rw [hset, Set.ncard_empty]
  have horder := matrixInertia_order (1 : Matrix ι ι ℝ)
  rcases hI : matrixInertia (1 : Matrix ι ι ℝ) with ⟨p, z, n⟩
  simp only [hI] at hpos hneg
  simp only [hI, Inertia.order] at horder
  have hzero : z = 0 := by omega
  cases hpos
  cases hzero
  cases hneg
  rfl

/-- Negating a real matrix negates its associated quadratic form. -/
@[simp] theorem toQuadraticForm'_neg (A : Matrix ι ι ℝ) :
    (-A).toQuadraticForm' = -A.toQuadraticForm' := by
  unfold Matrix.toQuadraticForm'
  simp

/-- Negation does not change the radical of a real quadratic form. -/
theorem radical_neg_toQuadraticForm (A : Matrix ι ι ℝ) :
    QuadraticMap.radical (-A.toQuadraticForm') =
      QuadraticMap.radical A.toQuadraticForm' := by
  ext x
  simp [QuadraticMap.mem_radical_iff']

/-- Negating a real matrix swaps the positive and negative inertia indices and
leaves the nullity unchanged. -/
theorem matrixInertia_neg (A : Matrix ι ι ℝ) :
    matrixInertia (-A) =
      { pos := (matrixInertia A).neg
        zero := (matrixInertia A).zero
        neg := (matrixInertia A).pos } := by
  open QuadraticForm in
    change Inertia.mk
        (sigPos ((-A).toQuadraticForm'))
        (Module.finrank ℝ ↥(QuadraticMap.radical ((-A).toQuadraticForm')))
        (sigNeg ((-A).toQuadraticForm')) =
      Inertia.mk
        (sigNeg A.toQuadraticForm')
        (Module.finrank ℝ ↥(QuadraticMap.radical A.toQuadraticForm'))
        (sigPos A.toQuadraticForm')
  rw [toQuadraticForm'_neg, radical_neg_toQuadraticForm]
  simp only [sigPos_neg, sigNeg_neg]

end Inertia
end SpectralGraph
