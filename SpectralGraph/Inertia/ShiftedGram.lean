import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import SpectralGraph.Inertia.BlockDiagonal

/-!
# Shifted rectangular Gram matrices

For a rectangular real matrix `N : Matrix ι κ ℝ`, this module compares

* `N * Nᵀ - 2I` on the row space, and
* `Nᵀ * N - 2I` on the column space.

The reusable bridge is the symmetric block matrix

    [ I   N  ]
    [ Nᵀ  2I ]

Its two Schur complements are the negatives (up to a positive factor) of the
shifted Gram matrices.  Exact block algebra and congruence invariance then give
equality of the positive and zero indices, together with the additive
dimension correction for the negative indices.
-/

open Matrix

namespace SpectralGraph
namespace Inertia

variable {ι κ : Type _}
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Row-side shifted Gram matrix `NNᵀ - 2I`. -/
def shiftedRowGram (N : Matrix ι κ ℝ) : Matrix ι ι ℝ :=
  N * N.transpose - (2 : ℝ) • (1 : Matrix ι ι ℝ)

/-- Column-side shifted Gram matrix `NᵀN - 2I`. -/
def shiftedColGram (N : Matrix ι κ ℝ) : Matrix κ κ ℝ :=
  N.transpose * N - (2 : ℝ) • (1 : Matrix κ κ ℝ)

/-- Symmetric block matrix whose two Schur complements compare the shifted
row and column Gram matrices. -/
def gramBridge (N : Matrix ι κ ℝ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
  Matrix.fromBlocks
    (1 : Matrix ι ι ℝ)
    N
    N.transpose
    ((2 : ℝ) • (1 : Matrix κ κ ℝ))

/-- The Schur complement of the identity block in `gramBridge` is exactly the
negative of the column-side shifted Gram matrix. -/
theorem gramBridge_schur_left
    {ι κ : Type _} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (N : Matrix ι κ ℝ) :
    (2 : ℝ) • (1 : Matrix κ κ ℝ) -
        N.transpose * (1 : Matrix ι ι ℝ) * N =
      -(shiftedColGram N) := by
  simp [shiftedColGram, sub_eq_add_neg, add_comm]

/-- LDU factorisation of the bridge around its top-left identity block.
This is the exact completion-of-squares step used later for inertia. -/
theorem gramBridge_ldu_left (N : Matrix ι κ ℝ) :
    gramBridge N =
      Matrix.fromBlocks
          (1 : Matrix ι ι ℝ) 0 N.transpose (1 : Matrix κ κ ℝ) *
        Matrix.fromBlocks
          (1 : Matrix ι ι ℝ) 0 0 (-(shiftedColGram N)) *
        Matrix.fromBlocks
          (1 : Matrix ι ι ℝ) N 0 (1 : Matrix κ κ ℝ) := by
  letI : Invertible (1 : Matrix ι ι ℝ) := invertibleOne
  have h := Matrix.fromBlocks_eq_of_invertible₁₁
    (A := (1 : Matrix ι ι ℝ))
    (B := N)
    (C := N.transpose)
    (D := (2 : ℝ) • (1 : Matrix κ κ ℝ))
  simpa [gramBridge, shiftedColGram, sub_eq_add_neg, add_comm] using h

/-- The two triangular factors in `gramBridge_ldu_left` are transposes of one
another, so the factorisation is a genuine matrix congruence. -/
theorem gramBridge_ldu_left_is_congruence
    {ι κ : Type _} [DecidableEq ι] [DecidableEq κ]
    (N : Matrix ι κ ℝ) :
    (Matrix.fromBlocks
        (1 : Matrix ι ι ℝ) N 0 (1 : Matrix κ κ ℝ)).transpose =
      Matrix.fromBlocks
        (1 : Matrix ι ι ℝ) 0 N.transpose (1 : Matrix κ κ ℝ) := by
  simp [Matrix.fromBlocks_transpose]

/-- Upper triangular change-of-variables matrix occurring in the left Schur
factorisation of `gramBridge`. -/
def gramBridgeUpper (N : Matrix ι κ ℝ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
  Matrix.fromBlocks
    (1 : Matrix ι ι ℝ) N 0 (1 : Matrix κ κ ℝ)

/-- Block diagonal form obtained from the left Schur complement of
`gramBridge`. -/
def gramBridgeDiagLeft (N : Matrix ι κ ℝ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
  Matrix.fromBlocks
    (1 : Matrix ι ι ℝ) 0 0 (-(shiftedColGram N))

/-- The bridge matrix is congruent to the block diagonal form
`diag(I, -(NᵀN-2I))`.  This is the first semantic-inertia consequence of the
compiled LDU factorisation. -/
theorem matrixInertia_gramBridgeDiagLeft_eq_gramBridge (N : Matrix ι κ ℝ) :
    matrixInertia (gramBridgeDiagLeft N) = matrixInertia (gramBridge N) := by
  letI : Invertible (1 : Matrix ι ι ℝ) := invertibleOne
  letI : Invertible (1 : Matrix κ κ ℝ) := invertibleOne
  letI : Invertible (gramBridgeUpper N) :=
    Matrix.fromBlocksZero₂₁Invertible
      (1 : Matrix ι ι ℝ) N (1 : Matrix κ κ ℝ)
  apply matrixInertia_eq_of_congr
    (gramBridgeDiagLeft N) (gramBridge N) (gramBridgeUpper N)
  simpa [gramBridgeUpper, gramBridgeDiagLeft, Matrix.fromBlocks_transpose] using
    (gramBridge_ldu_left N)

/-- The same congruence preserves matrix signature. -/
theorem matrixSignature_gramBridgeDiagLeft_eq_gramBridge (N : Matrix ι κ ℝ) :
    matrixSignature (gramBridgeDiagLeft N) = matrixSignature (gramBridge N) := by
  rw [matrixSignature, matrixSignature,
    matrixInertia_gramBridgeDiagLeft_eq_gramBridge]


/-- The bottom-right Schur complement of the bridge is `-1/2` times the
row-side shifted Gram matrix. -/
theorem gramBridge_schur_right
    {ι κ : Type _} [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (N : Matrix ι κ ℝ) :
    (1 : Matrix ι ι ℝ) -
        N * (((1 / 2 : ℝ)) • (1 : Matrix κ κ ℝ)) * N.transpose =
      -(((1 / 2 : ℝ)) • shiftedRowGram N) := by
  ext i j
  simp [shiftedRowGram, sub_eq_add_neg, Matrix.mul_apply]

/-- LDU factorisation of the bridge around its bottom-right `2I` block.
The inverse of `2I` is constructed locally, so no noncomputable global
`Invertible` instance is introduced. -/
theorem gramBridge_ldu_right (N : Matrix ι κ ℝ) :
    gramBridge N =
      Matrix.fromBlocks
          (1 : Matrix ι ι ℝ) (((1 / 2 : ℝ)) • N) 0 (1 : Matrix κ κ ℝ) *
        Matrix.fromBlocks
          (-(((1 / 2 : ℝ)) • shiftedRowGram N)) 0 0
          ((2 : ℝ) • (1 : Matrix κ κ ℝ)) *
        Matrix.fromBlocks
          (1 : Matrix ι ι ℝ) 0 (((1 / 2 : ℝ)) • N.transpose)
          (1 : Matrix κ κ ℝ) := by
  letI : Invertible ((2 : ℝ) • (1 : Matrix κ κ ℝ)) := by
    apply invertibleOfLeftInverse
      ((2 : ℝ) • (1 : Matrix κ κ ℝ))
      (((1 / 2 : ℝ)) • (1 : Matrix κ κ ℝ))
    ext i j
    simp
  have hinv :
      ⅟((2 : ℝ) • (1 : Matrix κ κ ℝ)) =
        ((1 / 2 : ℝ)) • (1 : Matrix κ κ ℝ) := by
    rfl
  have h := Matrix.fromBlocks_eq_of_invertible₂₂
    (A := (1 : Matrix ι ι ℝ))
    (B := N)
    (C := N.transpose)
    (D := (2 : ℝ) • (1 : Matrix κ κ ℝ))
  rw [hinv] at h
  rw [gramBridge_schur_right N] at h
  simpa [gramBridge] using h


/-- Lower triangular change-of-variables matrix in the bottom-right Schur
factorisation of `gramBridge`. -/
noncomputable def gramBridgeLowerRight (N : Matrix ι κ ℝ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
  Matrix.fromBlocks
    (1 : Matrix ι ι ℝ) 0 (((1 / 2 : ℝ)) • N.transpose)
    (1 : Matrix κ κ ℝ)

/-- Block diagonal form obtained from the bottom-right Schur complement of
`gramBridge`. -/
noncomputable def gramBridgeDiagRight (N : Matrix ι κ ℝ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
  Matrix.fromBlocks
    (-(((1 / 2 : ℝ)) • shiftedRowGram N)) 0 0
    ((2 : ℝ) • (1 : Matrix κ κ ℝ))

-- The upper factor in `gramBridge_ldu_right` is the transpose of the lower
-- factor, so the factorisation is a genuine congruence.
omit [Fintype ι] [Fintype κ] in
theorem gramBridge_ldu_right_is_congruence (N : Matrix ι κ ℝ) :
    (gramBridgeLowerRight N).transpose =
      Matrix.fromBlocks
        (1 : Matrix ι ι ℝ) (((1 / 2 : ℝ)) • N) 0
        (1 : Matrix κ κ ℝ) := by
  simp [gramBridgeLowerRight, Matrix.fromBlocks_transpose]

/-- The bridge matrix is congruent to the row-side block diagonal form
`diag(-(1/2)(NNᵀ-2I), 2I)`. -/
theorem matrixInertia_gramBridgeDiagRight_eq_gramBridge (N : Matrix ι κ ℝ) :
    matrixInertia (gramBridgeDiagRight N) = matrixInertia (gramBridge N) := by
  letI : Invertible (1 : Matrix ι ι ℝ) := invertibleOne
  letI : Invertible (1 : Matrix κ κ ℝ) := invertibleOne
  letI : Invertible (gramBridgeLowerRight N) :=
    Matrix.fromBlocksZero₁₂Invertible
      (1 : Matrix ι ι ℝ) (((1 / 2 : ℝ)) • N.transpose)
      (1 : Matrix κ κ ℝ)
  apply matrixInertia_eq_of_congr
    (gramBridgeDiagRight N) (gramBridge N) (gramBridgeLowerRight N)
  simpa [gramBridgeLowerRight, gramBridgeDiagRight, Matrix.fromBlocks_transpose] using
    (gramBridge_ldu_right N)

/-- The row-side Schur congruence also preserves matrix signature. -/
theorem matrixSignature_gramBridgeDiagRight_eq_gramBridge (N : Matrix ι κ ℝ) :
    matrixSignature (gramBridgeDiagRight N) = matrixSignature (gramBridge N) := by
  rw [matrixSignature, matrixSignature,
    matrixInertia_gramBridgeDiagRight_eq_gramBridge]

/-- Explicit inertia of the left Schur block diagonal form. -/
theorem matrixInertia_gramBridgeDiagLeft (N : Matrix ι κ ℝ) :
    matrixInertia (gramBridgeDiagLeft N) =
      { pos := Fintype.card ι + (matrixInertia (shiftedColGram N)).neg
        zero := (matrixInertia (shiftedColGram N)).zero
        neg := (matrixInertia (shiftedColGram N)).pos } := by
  change matrixInertia
      (twoBlockDiag (1 : Matrix ι ι ℝ) (-(shiftedColGram N))) = _
  rw [matrixInertia_twoBlockDiag, matrixInertia_one, matrixInertia_neg]
  simp

/-- Explicit inertia of the right Schur block diagonal form. -/
theorem matrixInertia_gramBridgeDiagRight (N : Matrix ι κ ℝ) :
    matrixInertia (gramBridgeDiagRight N) =
      { pos := (matrixInertia (shiftedRowGram N)).neg + Fintype.card κ
        zero := (matrixInertia (shiftedRowGram N)).zero
        neg := (matrixInertia (shiftedRowGram N)).pos } := by
  change matrixInertia
      (twoBlockDiag (-((1 / 2 : ℝ) • shiftedRowGram N))
        ((2 : ℝ) • (1 : Matrix κ κ ℝ))) = _
  rw [matrixInertia_twoBlockDiag, matrixInertia_neg,
    matrixInertia_pos_smul (shiftedRowGram N) (by norm_num : (0 : ℝ) < 1 / 2),
    matrixInertia_pos_smul (1 : Matrix κ κ ℝ) (by norm_num : (0 : ℝ) < 2),
    matrixInertia_one]
  simp

/-- The reusable shifted-Gram inertia theorem.  Positive and zero indices
agree, while the negative indices differ by the ambient dimensions.  The
last relation is deliberately additive, avoiding truncated natural-number
subtraction. -/
theorem shiftedGram_inertia_relations (N : Matrix ι κ ℝ) :
    (matrixInertia (shiftedRowGram N)).pos =
        (matrixInertia (shiftedColGram N)).pos ∧
      (matrixInertia (shiftedRowGram N)).zero =
        (matrixInertia (shiftedColGram N)).zero ∧
      (matrixInertia (shiftedRowGram N)).neg + Fintype.card κ =
        (matrixInertia (shiftedColGram N)).neg + Fintype.card ι := by
  have hbridge :
      matrixInertia (gramBridgeDiagLeft N) =
        matrixInertia (gramBridgeDiagRight N) :=
    (matrixInertia_gramBridgeDiagLeft_eq_gramBridge N).trans
      (matrixInertia_gramBridgeDiagRight_eq_gramBridge N).symm
  rw [matrixInertia_gramBridgeDiagLeft,
    matrixInertia_gramBridgeDiagRight] at hbridge
  have hpos := congrArg Inertia.pos hbridge
  have hzero := congrArg Inertia.zero hbridge
  have hneg := congrArg Inertia.neg hbridge
  simp only at hpos hzero hneg
  constructor
  · exact hneg.symm
  constructor
  · exact hzero.symm
  · omega

/-- Row and column shifted Gram matrices have the same positive index. -/
theorem shiftedGram_pos_eq (N : Matrix ι κ ℝ) :
    (matrixInertia (shiftedRowGram N)).pos =
      (matrixInertia (shiftedColGram N)).pos :=
  (shiftedGram_inertia_relations N).1

/-- Row and column shifted Gram matrices have the same nullity. -/
theorem shiftedGram_zero_eq (N : Matrix ι κ ℝ) :
    (matrixInertia (shiftedRowGram N)).zero =
      (matrixInertia (shiftedColGram N)).zero :=
  (shiftedGram_inertia_relations N).2.1

/-- Additive negative-index relation for shifted rectangular Gram matrices. -/
theorem shiftedGram_neg_add_card_eq (N : Matrix ι κ ℝ) :
    (matrixInertia (shiftedRowGram N)).neg + Fintype.card κ =
      (matrixInertia (shiftedColGram N)).neg + Fintype.card ι :=
  (shiftedGram_inertia_relations N).2.2

end Inertia
end SpectralGraph
