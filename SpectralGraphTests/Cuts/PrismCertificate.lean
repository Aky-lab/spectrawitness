import SpectralGraphTests.Cuts.Definitions
import SpectralGraph.Inertia.CenteredBound
import SpectralGraph.Certificate.IntegerCheck

/-! Exact integer certificates bound to the named prism Laplacian. -/

namespace SpectralGraphTests.Cuts

open SpectralGraph SpectralGraph.Certificate SpectralGraph.Inertia

set_option maxHeartbeats 1600000

/-- Directly authored full-scale input `6L - γ(6I-J)` for the prism. -/
def prismInput (g : Int) : DenseIntMatrix := DenseIntMatrix.ofFn 6 fun i j =>
  6 * ((if i = j then 3 else 0) -
    (if i ≠ j ∧ (i / 3 = j / 3 ∨ i % 3 = j % 3) then 1 else 0)) -
  g * ((if i = j then 6 else 0) - 1)

theorem prismInput_rat_two : (prismInput 2).toRatMatrix =
    (6 : ℚ) • prism.lapMatrix ℚ -
      (2 : ℚ) • ((6 : ℚ) • (1 : Matrix (Fin 6) (Fin 6) ℚ) -
        Matrix.of (fun (_ : Fin 6) (_ : Fin 6) => (1 : ℚ))) := by
  decide +kernel

theorem prismInput_rat_three : (prismInput 3).toRatMatrix =
    (6 : ℚ) • prism.lapMatrix ℚ -
      (3 : ℚ) • ((6 : ℚ) • (1 : Matrix (Fin 6) (Fin 6) ℚ) -
        Matrix.of (fun (_ : Fin 6) (_ : Fin 6) => (1 : ℚ))) := by
  decide +kernel

theorem prismInput_real_two :
    ratCastMatrix (prismInput 2).toRatMatrix =
      centeredShift (prism.lapMatrix ℝ) 2 := by
  rw [prismInput_rat_two]
  ext i j
  have hone : ((1 : Matrix (Fin 6) (Fin 6) ℚ) i j : ℝ) =
      (1 : Matrix (Fin 6) (Fin 6) ℝ) i j := by
    change ((1 : Matrix (Fin 6) (Fin 6) ℚ).map (Rat.castHom ℝ)) i j = _
    rw [Matrix.map_one] <;> simp
  simp [ratCastMatrix, centeredShift, SimpleGraph.lapMatrix,
    SimpleGraph.degMatrix, SimpleGraph.adjMatrix, Matrix.diagonal_apply,
    hone]
  split_ifs <;> norm_num [hone]

theorem prismInput_real_three :
    ratCastMatrix (prismInput 3).toRatMatrix =
      centeredShift (prism.lapMatrix ℝ) 3 := by
  rw [prismInput_rat_three]
  ext i j
  have hone : ((1 : Matrix (Fin 6) (Fin 6) ℚ) i j : ℝ) =
      (1 : Matrix (Fin 6) (Fin 6) ℝ) i j := by
    change ((1 : Matrix (Fin 6) (Fin 6) ℚ).map (Rat.castHom ℝ)) i j = _
    rw [Matrix.map_one] <;> simp
  simp [ratCastMatrix, centeredShift, SimpleGraph.lapMatrix,
    SimpleGraph.degMatrix, SimpleGraph.adjMatrix, Matrix.diagonal_apply,
    hone]
  split_ifs <;> norm_num [hone]

theorem prismInput_two_checked : (prismInput 2).checkInertia ⟨4, 2, 0⟩ = true := by
  decide +kernel

theorem prismInput_three_checked : (prismInput 3).checkInertia ⟨2, 3, 1⟩ = true := by
  decide +kernel

theorem prism_centered_two_inertia :
    matrixInertia (centeredShift (prism.lapMatrix ℝ) 2) = ⟨4, 2, 0⟩ := by
  rw [← prismInput_real_two]
  exact DenseIntMatrix.checkInertia_sound _ _ prismInput_two_checked

theorem prism_centered_three_inertia :
    matrixInertia (centeredShift (prism.lapMatrix ℝ) 3) = ⟨2, 3, 1⟩ := by
  rw [← prismInput_real_three]
  exact DenseIntMatrix.checkInertia_sound _ _ prismInput_three_checked

theorem prism_centered_two_neg_zero :
    (matrixInertia (centeredShift (prism.lapMatrix ℝ) 2)).neg = 0 := by
  rw [prism_centered_two_inertia]

end SpectralGraphTests.Cuts
