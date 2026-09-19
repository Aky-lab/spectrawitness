import SpectralGraphTests.Applications.PathEndpoint8Defs
import SpectralGraph.Certificate.FastInertia

namespace SpectralGraphTests.Applications.PathEndpoint8
open SpectralGraph SpectralGraph.Certificate

theorem A8_inertia : matrixInertia (ratCastMatrix A8) = ⟨6,0,2⟩ := by
  rw [A8_eq_literal]
  rw [matrixInertia_eq_fastComputedInertia A8Literal (by decide +kernel)]
  decide +kernel

end SpectralGraphTests.Applications.PathEndpoint8
