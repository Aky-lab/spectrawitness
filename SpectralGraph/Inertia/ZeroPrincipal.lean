import SpectralGraph.Inertia.Restriction
import SpectralGraph.Inertia.BlockDiagonal
import SpectralGraph.Inertia.Diagonal

/-!
# Zero principal blocks and inertia

A vanishing principal block bounds its cardinality by the nullity plus the
smaller sign index of the ambient real quadratic form.  No symmetry is needed:
`matrixInertia` of a nonsymmetric matrix is the inertia of its associated
quadratic form.
-/

namespace SpectralGraph
namespace Inertia

variable {V K : Type*} [Fintype V] [DecidableEq V]
  [Fintype K] [DecidableEq K]

private theorem matrixInertia_zero :
    matrixInertia (0 : Matrix K K ℝ) =
      { pos := 0, zero := Fintype.card K, neg := 0 } := by
  have hdiag : (0 : Matrix K K ℝ) = Matrix.diagonal (fun _ : K ↦ (0 : ℝ)) := by
    ext i j
    simp [Matrix.diagonal_apply]
  rw [hdiag, matrixInertia_diagonal]
  simp

/-- A zero principal block has cardinality at most the ambient nullity plus
the smaller of the positive and negative inertia indices. -/
theorem card_le_matrixInertia_zero_add_min_of_submatrix_eq_zero
    (A : Matrix V V ℝ) (e : K ↪ V)
    (hzero : A.submatrix e e = 0) :
    Fintype.card K ≤ (matrixInertia A).zero +
      min (matrixInertia A).pos (matrixInertia A).neg := by
  have hneg := matrixInertia_submatrix_neg_add_zero_le A e
  rw [hzero, matrixInertia_zero] at hneg
  have hpos := matrixInertia_submatrix_neg_add_zero_le (-A) e
  have hsubneg : (-A).submatrix e e = 0 := by
    ext i j
    change -A (e i) (e j) = 0
    rw [show A (e i) (e j) = 0 from congr_fun (congr_fun hzero i) j]
    simp
  rw [hsubneg, matrixInertia_zero, matrixInertia_neg] at hpos
  norm_num at hneg hpos
  by_cases hle : (matrixInertia A).pos ≤ (matrixInertia A).neg
  · rw [min_eq_left hle]
    omega
  · have hge : (matrixInertia A).neg ≤ (matrixInertia A).pos := Nat.le_of_not_ge hle
    rw [min_eq_right hge]
    omega

end Inertia
end SpectralGraph
