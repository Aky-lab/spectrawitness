import SpectralGraphTests.Applications.PathEndpoint8Defs
import SpectralGraph.Certificate.RankOneUpdate

namespace SpectralGraphTests.Applications.PathEndpoint8
open Matrix SpectralGraph SpectralGraph.Certificate

def A8Inverse : Matrix (Fin 8) (Fin 8) ℚ := !![
 -53940/26537,-66992/26537,-63296/26537,-43776/26537,-13312/26537,20480/26537,49152/26537,65536/26537;
 -66992/26537,-50244/26537,-47472/26537,-32832/26537,-9984/26537,15360/26537,36864/26537,49152/26537;
 -63296/26537,-47472/26537,-19780/26537,-13680/26537,-4160/26537,6400/26537,15360/26537,20480/26537;
 -43776/26537,-32832/26537,-13680/26537,8892/26537,2704/26537,-4160/26537,-9984/26537,-13312/26537;
 -13312/26537,-9984/26537,-4160/26537,2704/26537,8892/26537,-13680/26537,-32832/26537,-43776/26537;
 20480/26537,15360/26537,6400/26537,-4160/26537,-13680/26537,-19780/26537,-47472/26537,-63296/26537;
 49152/26537,36864/26537,15360/26537,-9984/26537,-32832/26537,-47472/26537,-50244/26537,-66992/26537;
 65536/26537,49152/26537,20480/26537,-13312/26537,-43776/26537,-63296/26537,-66992/26537,-53940/26537]
def endpointSolve8 : Fin 8 → ℚ := ![-1004/223,-976/223,-704/223,-256/223,
  256/223,704/223,976/223,1004/223]

theorem inverse_certificate : checkInverseBilinearWithInverse A8 A8Inverse
    endpoint8 endpoint8 endpointSolve8 (-2008/223) = true := by
  rw [A8_eq_literal]
  decide +kernel

def wrongEndpointSolve8 : Fin 8 → ℚ := ![-1003/223,-976/223,-704/223,-256/223,
  256/223,704/223,976/223,1004/223]

theorem reject_wrong_solve : checkInverseBilinearWithInverse A8 A8Inverse
    endpoint8 endpoint8 wrongEndpointSolve8 (-2008/223) = false := by
  rw [A8_eq_literal]
  decide +kernel
theorem inverse_value : (fun i ↦ (endpoint8 i : ℝ)) ⬝ᵥ
    ((ratCastMatrix A8)⁻¹ *ᵥ fun i ↦ (endpoint8 i : ℝ)) = (-2008/223 : ℝ) := by
  simpa [inverseBilinear] using checkInverseBilinearWithInverse_real_sound A8 A8Inverse
    endpoint8 endpoint8 endpointSolve8 (-2008/223) inverse_certificate
@[implicit_reducible] noncomputable def A8Invertible : Invertible (ratCastMatrix A8) := by
  have h : A8Inverse * A8 = 1 := (of_decide_eq_true inverse_certificate).1
  have hr : ratCastMatrix A8Inverse * ratCastMatrix A8 = 1 := by
    unfold ratCastMatrix
    rw [← Matrix.map_mul, h]
    simp
  exact invertibleOfLeftInverse _ _ hr

end SpectralGraphTests.Applications.PathEndpoint8
