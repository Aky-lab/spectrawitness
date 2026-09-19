import SpectralGraph.Inertia.SchurComplement

/-!
# Rectangular Gram matrices at arbitrary positive thresholds

The positive and zero indices of `NNᵀ - tI` and `NᵀN - tI` agree for every
`t > 0`. Their negative indices differ by the dimensions of the index types.
The proof compares the two Schur complements of `[I N; Nᵀ tI]`; it requires
neither a singular value decomposition nor a rank or injectivity hypothesis.
-/

namespace SpectralGraph.Inertia
open Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Row Gram matrix shifted by a real threshold. -/
def rowGramAt (N : Matrix ι κ ℝ) (t : ℝ) : Matrix ι ι ℝ :=
  N * N.transpose - t • (1 : Matrix ι ι ℝ)

/-- Column Gram matrix shifted by a real threshold. -/
def colGramAt (N : Matrix ι κ ℝ) (t : ℝ) : Matrix κ κ ℝ :=
  N.transpose * N - t • (1 : Matrix κ κ ℝ)

omit [DecidableEq ι] [Fintype κ] in
/-- Transposition exchanges the row and column shifted Gram matrices. -/
@[simp] theorem rowGramAt_transpose (N : Matrix ι κ ℝ) (t : ℝ) :
    rowGramAt N.transpose t = colGramAt N t := by
  simp [rowGramAt, colGramAt]

omit [Fintype ι] [DecidableEq κ] in
@[simp] theorem colGramAt_transpose (N : Matrix ι κ ℝ) (t : ℝ) :
    colGramAt N.transpose t = rowGramAt N t := by
  simp [rowGramAt, colGramAt]

omit [Fintype ι] in
/-- The Schur complement of the scalar block, written as a scalar multiple of
the shifted row Gram matrix. Nonzero thresholds suffice here. -/
theorem rowGramAt_schur (N : Matrix ι κ ℝ) {t : ℝ} (ht : t ≠ 0) :
    (1 : Matrix ι ι ℝ) - N * (t⁻¹ • (1 : Matrix κ κ ℝ)) * N.transpose =
      -(t⁻¹ • rowGramAt N t) := by
  simp only [rowGramAt, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    smul_sub, smul_smul, inv_mul_cancel₀ ht, one_smul]
  abel

/-- Positive and zero indices agree at every positive threshold. The last
identity uses addition, avoiding truncated subtraction of natural numbers. -/
theorem gramAt_inertia_relations (N : Matrix ι κ ℝ) {t : ℝ} (ht : 0 < t) :
    (matrixInertia (rowGramAt N t)).pos = (matrixInertia (colGramAt N t)).pos ∧
    (matrixInertia (rowGramAt N t)).zero = (matrixInertia (colGramAt N t)).zero ∧
    (matrixInertia (rowGramAt N t)).neg + Fintype.card κ =
      (matrixInertia (colGramAt N t)).neg + Fintype.card ι := by
  letI : Invertible (1 : Matrix ι ι ℝ) := invertibleOne
  letI : Invertible (t • (1 : Matrix κ κ ℝ)) := by
    apply invertibleOfLeftInverse (t • (1 : Matrix κ κ ℝ))
      (t⁻¹ • (1 : Matrix κ κ ℝ))
    simp [smul_smul, ne_of_gt ht]
  have hinv : ⅟(t • (1 : Matrix κ κ ℝ)) = t⁻¹ • (1 : Matrix κ κ ℝ) := rfl
  have hleft := matrixInertia_fromBlocks_schur₁₁
    (1 : Matrix ι ι ℝ) N (t • (1 : Matrix κ κ ℝ)) (by simp [Matrix.IsSymm])
  have hright := matrixInertia_fromBlocks_schur₂₂
    (1 : Matrix ι ι ℝ) N (t • (1 : Matrix κ κ ℝ)) (by simp [Matrix.IsSymm])
  have hcol : t • (1 : Matrix κ κ ℝ) - N.transpose * ⅟(1 : Matrix ι ι ℝ) * N =
      -(colGramAt N t) := by simp [colGramAt, sub_eq_add_neg, add_comm]
  rw [hcol, matrixInertia_neg, matrixInertia_one] at hleft
  rw [hinv, rowGramAt_schur N (ne_of_gt ht), matrixInertia_neg,
    matrixInertia_pos_smul _ (inv_pos.mpr ht), matrixInertia_pos_smul _ ht,
    matrixInertia_one] at hright
  have h := hleft.symm.trans hright
  have hp := congrArg Inertia.pos h
  have hz := congrArg Inertia.zero h
  have hn := congrArg Inertia.neg h
  simp only at hp hz hn
  exact ⟨by omega, by omega, by omega⟩

/-- Transfer the positive index at a positive squared-singular-value threshold. -/
theorem gramAt_pos_eq (N : Matrix ι κ ℝ) {t : ℝ} (ht : 0 < t) :
    (matrixInertia (rowGramAt N t)).pos = (matrixInertia (colGramAt N t)).pos :=
  (gramAt_inertia_relations N ht).1

/-- Positive eigenvalues have the same multiplicities in the two Gram matrices. -/
theorem gramAt_zero_eq (N : Matrix ι κ ℝ) {t : ℝ} (ht : 0 < t) :
    (matrixInertia (rowGramAt N t)).zero = (matrixInertia (colGramAt N t)).zero :=
  (gramAt_inertia_relations N ht).2.1

/-- Dimension-corrected negative index of a rectangular shifted Gram matrix. -/
theorem gramAt_neg_add_card_eq (N : Matrix ι κ ℝ) {t : ℝ} (ht : 0 < t) :
    (matrixInertia (rowGramAt N t)).neg + Fintype.card κ =
      (matrixInertia (colGramAt N t)).neg + Fintype.card ι :=
  (gramAt_inertia_relations N ht).2.2

/-- When the row space is at least as large, its shifted Gram inertia is
obtained by adding the dimension excess to the negative index. -/
theorem gramAt_neg_eq_add (N : Matrix ι κ ℝ) {t : ℝ} (ht : 0 < t)
    (hcard : Fintype.card κ ≤ Fintype.card ι) :
    (matrixInertia (rowGramAt N t)).neg =
      (matrixInertia (colGramAt N t)).neg + (Fintype.card ι - Fintype.card κ) := by
  have h := gramAt_neg_add_card_eq N ht
  omega

/-- Signature transfer across a rectangular Gram matrix, including the signed
dimension correction. -/
theorem gramAt_signature_eq (N : Matrix ι κ ℝ) {t : ℝ} (ht : 0 < t) :
    matrixSignature (rowGramAt N t) = matrixSignature (colGramAt N t) +
      (Fintype.card κ : ℤ) - (Fintype.card ι : ℤ) := by
  have hp := gramAt_pos_eq N ht
  have hn := gramAt_neg_add_card_eq N ht
  simp only [matrixSignature, Inertia.signature]
  omega

end SpectralGraph.Inertia
