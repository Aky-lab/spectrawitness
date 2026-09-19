import SpectralGraph.Inertia.ShiftedGramGeneral

/-! Full inertia of scalar-shifted off-diagonal blocks. This matrix interface
is independent of graphs and applies to arbitrary real rectangular matrices. -/

namespace SpectralGraph.Inertia
open Matrix

/-- Full inertia of a positively shifted bipartite block, using a squared
threshold on its row Gram matrix. This works for any real rectangular block. -/
theorem bipartiteBlock_pos_shift_inertia
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (B : Matrix ι κ ℝ) {t : ℝ} (ht : 0 < t) :
    matrixInertia (Matrix.fromBlocks (t • (1 : Matrix ι ι ℝ)) B B.transpose
        (t • (1 : Matrix κ κ ℝ))) =
      { pos := (matrixInertia (rowGramAt B (t ^ 2))).neg + Fintype.card κ
        zero := (matrixInertia (rowGramAt B (t ^ 2))).zero
        neg := (matrixInertia (rowGramAt B (t ^ 2))).pos } := by
  letI : Invertible (t • (1 : Matrix κ κ ℝ)) := by
    apply invertibleOfLeftInverse (t • (1 : Matrix κ κ ℝ))
      (t⁻¹ • (1 : Matrix κ κ ℝ))
    simp [smul_smul, ne_of_gt ht]
  have hinv : ⅟(t • (1 : Matrix κ κ ℝ)) = t⁻¹ • (1 : Matrix κ κ ℝ) := rfl
  have hscale : t⁻¹ * t ^ 2 = t := by
    field_simp
  have hschur : t • (1 : Matrix ι ι ℝ) -
      B * (t⁻¹ • (1 : Matrix κ κ ℝ)) * B.transpose =
      -(t⁻¹ • rowGramAt B (t ^ 2)) := by
    simp only [rowGramAt, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      smul_sub, smul_smul, hscale]
    abel
  have h := matrixInertia_fromBlocks_schur₂₂
    (t • (1 : Matrix ι ι ℝ)) B (t • (1 : Matrix κ κ ℝ))
    (by simp [Matrix.IsSymm])
  rw [hinv, hschur, matrixInertia_neg,
    matrixInertia_pos_smul _ (inv_pos.mpr ht), matrixInertia_pos_smul _ ht,
    matrixInertia_one] at h
  simpa using h

end SpectralGraph.Inertia
