import SpectralGraph.Inertia.Matrix

/-! # Semantic inertia of a real diagonal matrix -/

namespace SpectralGraph
open QuadraticForm
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A diagonal form represents the corresponding weighted sum of squares. -/
private theorem diagonal_toQuadraticForm_eq_weightedSumSquares
    (w : ι → ℝ) :
    (Matrix.diagonal w).toQuadraticForm' =
      QuadraticMap.weightedSumSquares ℝ w := by
  ext x
  simp [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply,
    QuadraticMap.weightedSumSquares_apply, Matrix.diagonal_apply,
    mul_comm, mul_left_comm]

/-- The semantic inertia of a real diagonal matrix is obtained by counting
the positive, zero, and negative diagonal entries. -/
theorem matrixInertia_diagonal (w : ι → ℝ) :
    matrixInertia (Matrix.diagonal w) =
      { pos := (Finset.univ.filter fun i ↦ 0 < w i).card
        zero := (Finset.univ.filter fun i ↦ w i = 0).card
        neg := (Finset.univ.filter fun i ↦ w i < 0).card } := by
  have hpos : (matrixInertia (Matrix.diagonal w)).pos =
      (Finset.univ.filter fun i ↦ 0 < w i).card := by
    change sigPos (Matrix.diagonal w).toQuadraticForm' = _
    rw [diagonal_toQuadraticForm_eq_weightedSumSquares,
      QuadraticForm.sigPos_weightedSumSquares]
    rw [← Set.ncard_coe_finset]
    congr 1
    ext i
    simp
  have hneg : (matrixInertia (Matrix.diagonal w)).neg =
      (Finset.univ.filter fun i ↦ w i < 0).card := by
    change sigNeg (Matrix.diagonal w).toQuadraticForm' = _
    rw [diagonal_toQuadraticForm_eq_weightedSumSquares,
      QuadraticForm.sigNeg_weightedSumSquares]
    rw [← Set.ncard_coe_finset]
    congr 1
    ext i
    simp
  have hzero : (matrixInertia (Matrix.diagonal w)).zero =
      (Finset.univ.filter fun i ↦ w i = 0).card := by
    change Module.finrank ℝ
        ↥(QuadraticMap.radical (Matrix.diagonal w).toQuadraticForm') = _
    rw [diagonal_toQuadraticForm_eq_weightedSumSquares,
      QuadraticForm.radical_weightedSumSquares, Pi.dim_spanSubset]
    rw [← Set.ncard_coe_finset]
    congr 1
    ext i
    simp
  rcases hI : matrixInertia (Matrix.diagonal w) with ⟨p, z, n⟩
  simp only [hI] at hpos hzero hneg
  cases hpos
  cases hzero
  cases hneg
  rfl


end SpectralGraph
