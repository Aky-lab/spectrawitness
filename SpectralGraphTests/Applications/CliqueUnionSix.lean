import SpectralGraph.Graph.CliqueUnion
import SpectralGraphTests.CliqueUnionCertificate

/-! Structural consequence of the checked `K₃ ⊔ K₂ ⊔ K₁` certificate. -/

namespace SpectralGraphTests.Applications.CliqueUnionSix

open Matrix SpectralGraph SpectralGraph.Graph
open SpectralGraphTests.CliqueUnionCertificate

theorem shifted_matrix_identity :
    graph.adjMatrix ℝ - ((-1 : ℚ) : ℝ) • 1 = 1 + graph.adjMatrix ℝ := by
  ext i j
  simp [Matrix.one_apply]
  ring

theorem shifted_inertia_one_add :
    matrixInertia (1 + graph.adjMatrix ℝ) = ⟨3, 3, 0⟩ := by
  rw [← shifted_matrix_identity]
  exact shifted_inertia

/-- The checked cutoff at `-1` proves that the complement of the named graph
is complete multipartite. -/
theorem complement_isCompleteMultipartite :
    graphᶜ.IsCompleteMultipartite := by
  apply compl_isCompleteMultipartite_of_one_add_adjMatrix_inertia_neg_eq_zero
  simpa [shifted_inertia_one_add]

end SpectralGraphTests.Applications.CliqueUnionSix
