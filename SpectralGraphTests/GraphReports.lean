import SpectralGraphTests.GraphReports.K3Report

namespace SpectralGraphTests.GraphReports
open SpectralGraph SpectralGraph.Graph

-- An independent client uses the checked report without copying its proof.
theorem completeThree_repeated_second :
    (K3Report.endpoint_0 : ℝ) <
      (adjacency_isHermitian IndependentGraphs.completeThree).eigenvalues₀ ⟨1, by decide⟩ ∧
    (adjacency_isHermitian IndependentGraphs.completeThree).eigenvalues₀ ⟨1, by decide⟩ ≤
      (K3Report.endpoint_1 : ℝ) := by
  simpa only [K3Report.graph] using K3Report.query_0

theorem completeThree_negative_multiplicity :
    (Finset.univ.filter fun j =>
      (K3Report.endpoint_0 : ℝ) <
        (adjacency_isHermitian IndependentGraphs.completeThree).eigenvalues j ∧
      (adjacency_isHermitian IndependentGraphs.completeThree).eigenvalues j ≤
        (K3Report.endpoint_1 : ℝ)).card = 2 := by
  simpa only [K3Report.graph] using K3Report.query_2

end SpectralGraphTests.GraphReports
