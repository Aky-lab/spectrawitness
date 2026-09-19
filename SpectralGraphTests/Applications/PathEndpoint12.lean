import SpectralGraphTests.Applications.PathEndpoint12Zero
import SpectralGraphTests.Applications.PathEndpoint12Half
import SpectralGraphTests.Applications.PathEndpoint12Transition
import SpectralGraphTests.Applications.PathEndpoint12Double
import SpectralGraph.Inertia.NegativeSpectrum

namespace SpectralGraphTests.Applications.PathEndpointSupporting
open SpectralGraph SpectralGraph.Certificate SpectralGraph.Inertia

theorem L12_second_smallest_zero_lt :
    (L12_isHermitian 0).eigenvalues₀ ⟨10, by decide⟩ < (1/9 : ℝ) := by
  rw [eigenvalues₀_lt_iff]
  have hs := L12_shifted 0
  norm_num at hs
  rw [hs]
  simp [B12_inertia_zero]
theorem L12_second_smallest_half_lt :
    (L12_isHermitian ((c12/2 : ℚ) : ℝ)).eigenvalues₀ ⟨10, by decide⟩ < (1/9 : ℝ) := by
  rw [eigenvalues₀_lt_iff, L12_shifted (c12/2)]; simp [B12_inertia_half]
theorem L12_second_smallest_transition_eq :
    (L12_isHermitian (c12 : ℝ)).eigenvalues₀ ⟨10, by decide⟩ = (1/9 : ℝ) := by
  apply le_antisymm
  · rw [eigenvalues₀_le_iff, L12_shifted c12]; simp [B12_inertia_transition]
  · rw [le_eigenvalues₀_iff, L12_shifted c12]; simp [B12_inertia_transition]
theorem L12_threshold_lt_second_smallest_double :
    (1/9 : ℝ) < (L12_isHermitian ((2*c12 : ℚ) : ℝ)).eigenvalues₀ ⟨10, by decide⟩ := by
  rw [lt_eigenvalues₀_iff, L12_shifted (2*c12)]; simp [B12_inertia_double]

end SpectralGraphTests.Applications.PathEndpointSupporting
