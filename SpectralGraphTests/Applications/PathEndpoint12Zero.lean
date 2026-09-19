import SpectralGraphTests.Applications.PathEndpoint12Defs
import SpectralGraph.Certificate.FastInertia
namespace SpectralGraphTests.Applications.PathEndpointSupporting
open SpectralGraph SpectralGraph.Certificate
theorem B12_inertia_zero : matrixInertia (ratCastMatrix (B12 0)) = ⟨10,0,2⟩ := by
  rw [matrixInertia_eq_fastComputedInertia _ (by decide +kernel)]; decide +kernel
end SpectralGraphTests.Applications.PathEndpointSupporting
