import SpectralGraph.Graph.EncodingCheck
import SpectralGraph.Graph.IntegerSpectrum
import SpectralGraphTests.GraphReports.IndependentGraphs

/- Generated from exact JSON, SHA256 8d36fc8c79dc849369906330fb19f2050b175ed54eedb21e4033b4311b262ab0.
The external producer is untrusted; compile this file for kernel verification. -/
namespace SpectralGraphTests.GraphReports.K3Report
open SpectralGraph SpectralGraph.Graph

def rows : PackedAdjacencyRows := #[6, 4, 0]
theorem rows_valid : packedRowsValid 3 rows = true := by decide +kernel
def emittedGraph : SimpleGraph (Fin 3) := graphOfPackedRows 3 rows
instance : DecidableRel emittedGraph.Adj := by unfold emittedGraph; infer_instance
def graph : SimpleGraph (Fin 3) := _root_.SpectralGraphTests.GraphReports.IndependentGraphs.completeThree
instance : DecidableRel graph.Adj := by unfold graph; infer_instance
theorem graph_matches : emittedGraph = graph := by
  have h : ∀ i j : Fin 3, emittedGraph.Adj i j ↔ graph.Adj i j := by decide +kernel
  ext i j
  exact h i j

def endpoint_0 : ℚ := -2
theorem inertia_0 : matrixInertia (graph.adjMatrix ℝ - (endpoint_0 : ℝ) • 1) = ⟨3,0,0⟩ :=
  checkAdjacencyInertiaAt_sound graph endpoint_0 ⟨3,0,0⟩ (by decide +kernel)

def endpoint_1 : ℚ := -1
theorem inertia_1 : matrixInertia (graph.adjMatrix ℝ - (endpoint_1 : ℝ) • 1) = ⟨1,2,0⟩ :=
  checkAdjacencyInertiaAt_sound graph endpoint_1 ⟨1,2,0⟩ (by decide +kernel)

def endpoint_2 : ℚ := 2
theorem inertia_2 : matrixInertia (graph.adjMatrix ℝ - (endpoint_2 : ℝ) • 1) = ⟨0,1,2⟩ :=
  checkAdjacencyInertiaAt_sound graph endpoint_2 ⟨0,1,2⟩ (by decide +kernel)

theorem query_0 :
    (endpoint_0 : ℝ) < (adjacency_isHermitian graph).eigenvalues₀ ⟨1, by decide⟩ ∧
    (adjacency_isHermitian graph).eigenvalues₀ ⟨1, by decide⟩ ≤ (endpoint_1 : ℝ) := by
  apply (Inertia.eigenvalues₀_mem_Ioc_iff _ (adjacency_isHermitian graph) _ _ _).mpr
  rw [inertia_0, inertia_1]
  decide

theorem query_1 :
    (endpoint_0 : ℝ) < (adjacency_isHermitian graph).eigenvalues₀ ⟨2, by decide⟩ ∧
    (adjacency_isHermitian graph).eigenvalues₀ ⟨2, by decide⟩ ≤ (endpoint_1 : ℝ) := by
  apply (Inertia.eigenvalues₀_mem_Ioc_iff _ (adjacency_isHermitian graph) _ _ _).mpr
  rw [inertia_0, inertia_1]
  decide

theorem query_2 :
    (Finset.univ.filter fun j => (endpoint_0 : ℝ) < (adjacency_isHermitian graph).eigenvalues j ∧
      (adjacency_isHermitian graph).eigenvalues j ≤ (endpoint_1 : ℝ)).card = 2 := by
  rw [Inertia.eigenvalue_count_Ioc_eq _ (adjacency_isHermitian graph) _ _ (by norm_num [endpoint_0, endpoint_1]),
    inertia_0, inertia_1]
  decide

theorem query_3 :
    (Finset.univ.filter fun j => (endpoint_1 : ℝ) < (adjacency_isHermitian graph).eigenvalues j ∧
      (adjacency_isHermitian graph).eigenvalues j ≤ (endpoint_2 : ℝ)).card = 1 := by
  rw [Inertia.eigenvalue_count_Ioc_eq _ (adjacency_isHermitian graph) _ _ (by norm_num [endpoint_1, endpoint_2]),
    inertia_1, inertia_2]
  decide

theorem query_4 :
    (Finset.univ.filter fun j => (endpoint_1 : ℝ) < (adjacency_isHermitian graph).eigenvalues j ∧
      (adjacency_isHermitian graph).eigenvalues j ≤ (endpoint_1 : ℝ)).card = 0 := by
  rw [Inertia.eigenvalue_count_Ioc_eq _ (adjacency_isHermitian graph) _ _ (by norm_num [endpoint_1, endpoint_1]),
    inertia_1]
  decide

end SpectralGraphTests.GraphReports.K3Report
