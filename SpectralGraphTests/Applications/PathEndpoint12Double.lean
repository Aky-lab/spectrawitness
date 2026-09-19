import SpectralGraphTests.Applications.PathEndpoint12Defs
import SpectralGraph.Certificate.FastInertia
namespace SpectralGraphTests.Applications.PathEndpointSupporting
open SpectralGraph SpectralGraph.Certificate
theorem B12_inertia_double : matrixInertia (ratCastMatrix (B12 (2*c12))) = ⟨11,0,1⟩ := by
  rw [matrixInertia_eq_fastComputedInertia _ (by decide +kernel)]; decide +kernel
end SpectralGraphTests.Applications.PathEndpointSupporting
