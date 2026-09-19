import SpectralGraph.Certificate.ProductWitnessSubspace
import SpectralGraph.Inertia.NegativeSpectrum
import SpectralGraphTests.Applications.PathEndpoint8

namespace SpectralGraphTests.Applications.PathEndpointSupporting
open Matrix SpectralGraph SpectralGraph.Certificate SpectralGraph.Inertia
open SpectralGraphTests.Applications.PathEndpoint8

def P8 : Matrix (Fin 8) (Fin 8) ℚ :=
  A8 + (223 / 4016 : ℚ) • vecMulVec endpoint8 endpoint8
def U8 : Matrix (Fin 8) (Fin 2) ℚ := !![
  1,-7; 1,-5; 1,-3; 1,-1; 1,1; 1,3; 1,5; 1,7]
def d8 : Fin 2 → ℚ := ![-2, -3129 / 1004]
def W8 : Matrix (Fin 8) (Fin 2) ℚ := !![
  -1/4,-2063/2008; -1/4,2510/2008; -1/4,1506/2008; -1/4,502/2008;
  -1/4,-502/2008; -1/4,-1506/2008; -1/4,-2510/2008; -1/4,2063/2008]

theorem P8_eq_literal_update :
    P8 = A8Literal + (223 / 4016 : ℚ) • vecMulVec endpoint8 endpoint8 := by
  simp [P8, A8_eq_literal]
theorem P8_old_witness : checkNegativeSubspace P8 U8 d8 = true := by
  rw [P8_eq_literal_update]; decide +kernel
theorem P8_supplied_image : checkNegativeSubspaceWithImage P8 U8 W8 d8 = true := by
  rw [P8_eq_literal_update]; decide +kernel
theorem P8_supplied_implies_old : checkNegativeSubspace P8 U8 d8 = true :=
  checkNegativeSubspaceWithImage_implies_checkNegativeSubspace P8 U8 W8 d8 P8_supplied_image
theorem P8_image_bound : P8 * U8 = W8 := by rw [P8_eq_literal_update]; decide +kernel

theorem P8_real_eq_shifted :
    ratCastMatrix P8 = L8 (223 / 4016 : ℝ) - (1/4 : ℝ) • 1 := by
  rw [shifted_update]
  unfold P8 ratCastMatrix
  ext i j
  simp only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, vecMulVec_apply]
  norm_num

theorem L8_second_smallest_half_lt_from_partial :
    (L8_isHermitian (223/4016 : ℝ)).eigenvalues₀ ⟨6, by decide⟩ < (1/4 : ℝ) := by
  rw [eigenvalues₀_lt_iff, ← P8_real_eq_shifted]
  have h := checkNegativeSubspace_sound P8 U8 d8 P8_old_witness
  norm_num at h ⊢
  exact h

def corruptW8 : Matrix (Fin 8) (Fin 2) ℚ := fun i j ↦
  if i = 0 ∧ j = 0 then W8 i j + 1 else W8 i j
theorem P8_reject_corrupt_image :
    checkNegativeSubspaceWithImage P8 U8 corruptW8 d8 = false := by
  rw [P8_eq_literal_update]; decide +kernel
theorem P8_reject_wrong_diagonal :
    checkNegativeSubspace P8 U8 ![-2, -3129/1005] = false := by
  rw [P8_eq_literal_update]; decide +kernel
theorem P8_reject_wrong_matrix :
    checkNegativeSubspace (A8 + (224/4016 : ℚ) • vecMulVec endpoint8 endpoint8) U8 d8 = false := by
  rw [A8_eq_literal]; decide +kernel

end SpectralGraphTests.Applications.PathEndpointSupporting
