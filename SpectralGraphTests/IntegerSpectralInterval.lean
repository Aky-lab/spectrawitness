import SpectralGraph.Certificate.IntegerSpectralInterval
import SpectralGraph.Certificate.LinearSolveReal

namespace SpectralGraphTests.IntegerSpectralInterval
open SpectralGraph SpectralGraph.Certificate Matrix

def repeated : DenseIntMatrix := ⟨4, #[0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2]⟩

-- Nonintegral endpoints are checked entirely by integer arithmetic.
example : repeated.checkEigenvaluesIoc (-1 / 2) (3 / 2) ⟨4, 0, 0⟩ ⟨1, 0, 3⟩ 3 = true := by
  decide +kernel
example : repeated.checkEigenvaluesIoc 0 1 ⟨3, 1, 0⟩ ⟨1, 2, 1⟩ 2 = true := by decide +kernel
example : repeated.checkEigenvaluesIoc 1 1 ⟨1, 2, 1⟩ ⟨1, 2, 1⟩ 0 = true := by decide +kernel
example : repeated.checkEigenvaluesIoc 1 0 ⟨1, 2, 1⟩ ⟨3, 1, 0⟩ 0 = false := by decide +kernel
example : repeated.checkEigenvaluesIoc 0 1 ⟨3, 1, 0⟩ ⟨1, 2, 1⟩ 1 = false := by decide +kernel

theorem repeated_hermitian : (ratCastMatrix repeated.toRatMatrix).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ratCastMatrix, DenseIntMatrix.toRatMatrix, DenseIntMatrix.entry, repeated]

-- This is a statement about actual eigenvalues, rather than only inertia records.
theorem repeated_count :
    (Finset.univ.filter fun i ↦ (-1 / 2 : ℝ) < repeated_hermitian.eigenvalues i ∧
      repeated_hermitian.eigenvalues i ≤ (3 / 2 : ℝ)).card = 3 := by
  simpa using repeated.checkEigenvaluesIoc_sound repeated_hermitian
    (-1 / 2) (3 / 2) ⟨4, 0, 0⟩ ⟨1, 0, 3⟩ 3 (by decide +kernel)

-- Denominator clearing retains negative thresholds and off-diagonal entries.
def edge : DenseIntMatrix := ⟨2, #[0, 1, 1, 0]⟩
example : (edge.rationalShift (-3 / 2)).entries = #[3, 2, 2, 3] := by decide +kernel
example : edge.checkEigenvaluesIoc (-3 / 2) 1 ⟨2, 0, 0⟩ ⟨0, 1, 1⟩ 2 = true := by decide +kernel
example : edge.checkEigenvaluesIoc (-1) 1 ⟨1, 1, 0⟩ ⟨0, 1, 1⟩ 1 = true := by decide +kernel

-- Normalizing the generated shifts must not hide malformed original storage.
example : (⟨2, #[1]⟩ : DenseIntMatrix).checkEigenvaluesIoc (-1) 2
    ⟨2, 0, 0⟩ ⟨0, 0, 2⟩ 2 = false := by decide +kernel
example : (⟨1, #[1, 99]⟩ : DenseIntMatrix).checkInertiaAt 0 ⟨1, 0, 0⟩ = false := by decide +kernel
example : (⟨2, #[0, 1, 2, 0]⟩ : DenseIntMatrix).checkInertiaAt 0 ⟨1, 0, 1⟩ = false := by decide +kernel
example : (⟨0, #[]⟩ : DenseIntMatrix).checkEigenvaluesIoc (-1 / 3) (1 / 7)
    ⟨0, 0, 0⟩ ⟨0, 0, 0⟩ 0 = true := by decide +kernel

-- The efficient inverse checker also certifies real bilinear quantities.
example : inverseBilinear (ratCastMatrix (!![2] : Matrix (Fin 1) (Fin 1) ℚ))
    (fun _ ↦ (3 : ℝ)) (fun _ ↦ (4 : ℝ)) = 6 := by
  simpa using checkInverseBilinearWithInverse_real_sound
    (!![2] : Matrix (Fin 1) (Fin 1) ℚ) !![1 / 2]
    (fun _ ↦ 3) (fun _ ↦ 4) (fun _ ↦ 2) 6 (by decide +kernel)

#print axioms SpectralGraph.Certificate.DenseIntMatrix.checkEigenvaluesIoc_sound
#print axioms SpectralGraph.Certificate.checkInverseBilinearWithInverse_real_sound

example : repeated.checkEigenvalueBracket 0 1 ⟨3, 1, 0⟩ ⟨1, 2, 1⟩ 1 = true := by decide +kernel
example : repeated.checkEigenvalueBracket 0 1 ⟨3, 1, 0⟩ ⟨1, 2, 1⟩ 2 = true := by decide +kernel
example : repeated.checkEigenvalueBracket (1 / 2) (3 / 2) ⟨3, 0, 1⟩ ⟨1, 0, 3⟩ 1 = true := by decide +kernel
example : repeated.checkEigenvalueBracket 0 1 ⟨3, 1, 0⟩ ⟨1, 2, 1⟩ 0 = false := by decide +kernel
example : repeated.checkEigenvalueBracket 0 1 ⟨3, 1, 0⟩ ⟨1, 2, 1⟩ 4 = false := by decide +kernel
example : repeated.checkEigenvalueBracket 1 1 ⟨1, 2, 1⟩ ⟨1, 2, 1⟩ 1 = false := by decide +kernel
example : repeated.checkEigenvalueBracket 1 0 ⟨1, 2, 1⟩ ⟨3, 1, 0⟩ 1 = false := by decide +kernel

example : (0 : ℝ) < repeated_hermitian.eigenvalues₀ ⟨1, by decide⟩ ∧
    repeated_hermitian.eigenvalues₀ ⟨1, by decide⟩ ≤ 1 := by
  simpa only [Rat.cast_zero, Rat.cast_one] using repeated.checkEigenvalueBracket_sound repeated_hermitian
    0 1 ⟨3, 1, 0⟩ ⟨1, 2, 1⟩ ⟨1, by decide⟩ (by decide +kernel)

example : (0 : ℝ) < repeated_hermitian.eigenvalues₀ ⟨2, by decide⟩ ∧
    repeated_hermitian.eigenvalues₀ ⟨2, by decide⟩ ≤ 1 := by
  simpa only [Rat.cast_zero, Rat.cast_one] using repeated.checkEigenvalueBracket_sound repeated_hermitian
    0 1 ⟨3, 1, 0⟩ ⟨1, 2, 1⟩ ⟨2, by decide⟩ (by decide +kernel)

#print axioms SpectralGraph.Certificate.DenseIntMatrix.checkEigenvalueBracket_sound

end SpectralGraphTests.IntegerSpectralInterval
