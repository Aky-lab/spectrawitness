import SpectralGraph.Certificate.LinearSolveReal
import SpectralGraph.Certificate.FastInertia

namespace SpectralGraphTests.LinearSolve
open SpectralGraph SpectralGraph.Certificate Matrix

def diagonal : Matrix (Fin 2) (Fin 2) ℚ := !![2, 0; 0, 3]

example : inverseBilinear diagonal ![2, -1] ![4, 6] = 2 :=
  checkInverseBilinear_sound _ _ _ ![2, 2] _ (by decide +kernel)

example : inverseBilinear (ratCastMatrix diagonal)
    ![(2 : ℝ), -1] ![(4 : ℝ), 6] = 2 := by
  have hu : (fun i : Fin 2 ↦ ((![2, -1] i : ℚ) : ℝ)) = ![2, -1] := by
    ext i; fin_cases i <;> norm_num
  have hv : (fun i : Fin 2 ↦ ((![4, 6] i : ℚ) : ℝ)) = ![4, 6] := by
    ext i; fin_cases i <;> norm_num
  simpa only [hu, hv, Rat.cast_ofNat] using
    checkInverseBilinear_real_sound diagonal ![2, -1] ![4, 6] ![2, 2] 2 (by decide +kernel)

example : checkInverseBilinear diagonal ![2, -1] ![4, 6] ![2, 3] 2 = false := by
  decide +kernel
example : checkInverseBilinear diagonal ![2, -1] ![4, 6] ![2, 2] 3 = false := by
  decide +kernel
-- Consistent singular systems must still be rejected at the inverse boundary.
example : checkInverseBilinear (0 : Matrix (Fin 1) (Fin 1) ℚ)
    ![1] ![0] ![1] 1 = false := by decide +kernel
example : checkInverseBilinearWithInverse diagonal !![1/2, 0; 0, 1/3]
    ![2, -1] ![4, 6] ![2, 2] 2 = true := by decide +kernel
example : checkInverseBilinearWithInverse diagonal 0
    ![2, -1] ![4, 6] ![2, 2] 2 = false := by decide +kernel
example : checkInverseBilinear (1 : Matrix (Fin 0) (Fin 0) ℚ)
    0 0 0 0 = true := by decide +kernel

def pivot : Matrix (Fin 1) (Fin 1) ℚ := !![2]
def pivotInverse : Matrix (Fin 1) (Fin 1) ℚ := !![1/2]
def coupling : Matrix (Fin 1) (Fin 2) ℚ := fun _ ↦ ![2, 4]
def solution : Matrix (Fin 1) (Fin 2) ℚ := fun _ ↦ ![1, 2]
def trailing : Matrix (Fin 2) (Fin 2) ℚ := !![5, 0; 0, 10]
def remainder : Matrix (Fin 2) (Fin 2) ℚ := !![3, -4; -4, 2]

example : checkSchur pivot pivotInverse coupling solution coupling.transpose
    trailing remainder = true := by decide +kernel
example : checkSchur pivot pivotInverse coupling 0 coupling.transpose
    trailing remainder = false := by decide +kernel
example : checkSchur pivot pivotInverse coupling solution coupling.transpose
    trailing 0 = false := by decide +kernel

/-- The checked block solve integrates with semantic inertia additivity. -/
example : matrixInertia (Matrix.fromBlocks (ratCastMatrix pivot)
    (coupling.map (Rat.castHom ℝ)) (coupling.map (Rat.castHom ℝ)).transpose
    (ratCastMatrix trailing)) = ⟨2, 0, 1⟩ := by
  have hp : matrixInertia (ratCastMatrix pivot) = ⟨1, 0, 0⟩ := by
    rw [matrixInertia_eq_fastComputedInertia pivot (by decide +kernel)]
    decide +kernel
  have hs : matrixInertia (ratCastMatrix remainder) = ⟨1, 0, 1⟩ := by
    rw [matrixInertia_eq_fastComputedInertia remainder (by decide +kernel)]
    decide +kernel
  rw [checkSchur_inertia pivot pivotInverse coupling solution trailing remainder
    (by decide +kernel) (by decide +kernel), hp, hs]
  rfl

end SpectralGraphTests.LinearSolve
