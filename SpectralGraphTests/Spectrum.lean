import SpectralGraph.Certificate.SpectralInterval

namespace SpectralGraphTests.Spectrum
open SpectralGraph SpectralGraph.Certificate Matrix

def repeated : Matrix (Fin 4) (Fin 4) ℚ := Matrix.diagonal ![0, 1, 1, 2]
def atZero : InertiaCertificate (Fin 4) := ⟨1, 1, ⟨3, 1, 0⟩⟩
def atOne : InertiaCertificate (Fin 4) := ⟨1, 1, ⟨1, 2, 1⟩⟩
def atTwo : InertiaCertificate (Fin 4) := ⟨1, 1, ⟨0, 1, 3⟩⟩

example : checkEigenvaluesIoc repeated 0 1 atZero atOne 2 = true := by decide +kernel
example : checkEigenvaluesIoc repeated 1 2 atOne atTwo 1 = true := by decide +kernel
example : checkEigenvaluesIoc repeated 1 1 atOne atOne 0 = true := by decide +kernel
example : checkEigenvaluesIoc repeated 1 0 atOne atZero 0 = false := by decide +kernel
example : checkEigenvaluesIoc repeated 0 1 atZero atOne 1 = false := by decide +kernel

theorem repeated_hermitian : (ratCastMatrix repeated).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases hij : i = j <;> simp [ratCastMatrix, repeated, hij, eq_comm]

/-- A semantic multiplicity statement about mathlib eigenvalues, proved using
only rational endpoint certificates. The eigenvalues themselves are not computed. -/
theorem two_eigenvalues_in_Ioc :
    (Finset.univ.filter fun i ↦ (0 : ℝ) < repeated_hermitian.eigenvalues i ∧
      repeated_hermitian.eigenvalues i ≤ (1 : ℝ)).card = 2 := by
  simpa using checkEigenvaluesIoc_sound repeated repeated_hermitian
    0 1 atZero atOne 2 (by decide +kernel)

example : checkEigenvalueBracket repeated 0 1 atZero atOne 1 = true := by decide +kernel
example : checkEigenvalueBracket repeated 0 1 atZero atOne 2 = true := by decide +kernel
example : checkEigenvalueBracket repeated 0 1 atZero atOne 0 = false := by decide +kernel
example : checkEigenvalueBracket repeated 0 1 atZero atOne 4 = false := by decide +kernel
example : checkEigenvalueBracket repeated 1 1 atOne atOne 1 = false := by decide +kernel

/-- Both occurrences of the repeated eigenvalue are localized separately. -/
example : (0 : ℝ) < repeated_hermitian.eigenvalues₀ ⟨1, by simp⟩ ∧
    repeated_hermitian.eigenvalues₀ ⟨1, by simp⟩ ≤ 1 := by
  simpa using checkEigenvalueBracket_sound repeated repeated_hermitian 0 1 atZero atOne
    ⟨1, by simp⟩ (by decide +kernel)

#print axioms two_eigenvalues_in_Ioc
#print axioms checkEigenvalueBracket_sound

end SpectralGraphTests.Spectrum
