import Mathlib.LinearAlgebra.Matrix.SchurComplement
import SpectralGraph.Inertia.BlockDiagonal
import SpectralGraph.Inertia.Congruence
import SpectralGraph.Inertia.Restriction

/-!
# Inertia and Schur complements

Reusable inertia bookkeeping for exact symmetric elimination.
-/

namespace SpectralGraph
namespace Inertia

open Matrix

/-- Inertia is additive across an invertible symmetric bottom-right pivot and
its Schur complement. -/
theorem matrixInertia_fromBlocks_schur₂₂
    {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ)
    (hD : D.IsSymm) [Invertible D] :
    matrixInertia (Matrix.fromBlocks A B B.transpose D) =
      { pos := (matrixInertia (A - B * ⅟ D * B.transpose)).pos +
          (matrixInertia D).pos
        zero := (matrixInertia (A - B * ⅟ D * B.transpose)).zero +
          (matrixInertia D).zero
        neg := (matrixInertia (A - B * ⅟ D * B.transpose)).neg +
          (matrixInertia D).neg } := by
  let S := A - B * ⅟ D * B.transpose
  let P : Matrix (m ⊕ n) (m ⊕ n) ℝ :=
    Matrix.fromBlocks 1 0 (⅟ D * B.transpose) 1
  let diag := twoBlockDiag S D
  letI : Invertible (1 : Matrix m m ℝ) := invertibleOne
  letI : Invertible (1 : Matrix n n ℝ) := invertibleOne
  letI : Invertible P := by
    dsimp [P]
    exact Matrix.fromBlocksZero₁₂Invertible 1 (⅟ D * B.transpose) 1
  have hPt : P.transpose = Matrix.fromBlocks 1 (B * ⅟ D) 0 1 := by
    simp [P, Matrix.fromBlocks_transpose, Matrix.transpose_mul,
      Matrix.invOf_eq_nonsing_inv, hD.inv.eq]
  have hfactor : Matrix.fromBlocks A B B.transpose D =
      P.transpose * diag * P := by
    rw [hPt]
    simpa [S, diag, twoBlockDiag, P] using
      (Matrix.fromBlocks_eq_of_invertible₂₂ A B B.transpose D)
  rw [← matrixInertia_eq_of_congr diag
    (Matrix.fromBlocks A B B.transpose D) P hfactor]
  exact matrixInertia_twoBlockDiag S D

/-- Top-left companion of `matrixInertia_fromBlocks_schur₂₂`. -/
theorem matrixInertia_fromBlocks_schur₁₁
    {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ)
    (hA : A.IsSymm) [Invertible A] :
    matrixInertia (Matrix.fromBlocks A B B.transpose D) =
      { pos := (matrixInertia (D - B.transpose * ⅟ A * B)).pos +
          (matrixInertia A).pos
        zero := (matrixInertia (D - B.transpose * ⅟ A * B)).zero +
          (matrixInertia A).zero
        neg := (matrixInertia (D - B.transpose * ⅟ A * B)).neg +
          (matrixInertia A).neg } := by
  rw [← matrixInertia_submatrix_equiv
    (Matrix.fromBlocks A B B.transpose D) (Equiv.sumComm n m)]
  change matrixInertia
    ((Matrix.fromBlocks A B B.transpose D).submatrix Sum.swap Sum.swap) = _
  rw [Matrix.fromBlocks_submatrix_sum_swap_sum_swap]
  simpa only [Matrix.transpose_transpose] using
    matrixInertia_fromBlocks_schur₂₂ D B.transpose A hA

end Inertia
end SpectralGraph
