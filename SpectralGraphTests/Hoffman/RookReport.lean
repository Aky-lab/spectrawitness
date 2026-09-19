import SpectralGraph.Graph.EncodingCheck
import SpectralGraph.Graph.IntegerSpectrum
import SpectralGraphTests.Hoffman.Definitions

/- Generated from exact JSON, SHA256 ceff8c895a23ce276e6c48ff7f9d53e0c29417b4068227a6657670846b6a19f4.
The external producer is untrusted; compile this file for kernel verification. -/
namespace SpectralGraphTests.Hoffman.RookReport
open SpectralGraph SpectralGraph.Graph

def rows : PackedAdjacencyRows := #[78, 148, 288, 112, 160, 256, 384, 256, 0]
theorem rows_valid : packedRowsValid 9 rows = true := by decide +kernel
def emittedGraph : SimpleGraph (Fin 9) := graphOfPackedRows 9 rows
instance : DecidableRel emittedGraph.Adj := by unfold emittedGraph; infer_instance
def graph : SimpleGraph (Fin 9) := _root_.SpectralGraphTests.Hoffman.Definitions.rook3
instance : DecidableRel graph.Adj := by unfold graph; infer_instance
theorem graph_matches : emittedGraph = graph := by
  have h : ∀ i j : Fin 9, emittedGraph.Adj i j ↔ graph.Adj i j := by decide +kernel
  ext i j
  exact h i j

def endpoint_0 : ℚ := -4
theorem inertia_0 : matrixInertia (graph.adjMatrix ℝ - (endpoint_0 : ℝ) • 1) = ⟨9,0,0⟩ :=
  checkAdjacencyInertiaAt_sound graph endpoint_0 ⟨9,0,0⟩ (by decide +kernel)

def endpoint_1 : ℚ := -2
theorem inertia_1 : matrixInertia (graph.adjMatrix ℝ - (endpoint_1 : ℝ) • 1) = ⟨5,4,0⟩ :=
  checkAdjacencyInertiaAt_sound graph endpoint_1 ⟨5,4,0⟩ (by decide +kernel)

def endpoint_2 : ℚ := 0
theorem inertia_2 : matrixInertia (graph.adjMatrix ℝ - (endpoint_2 : ℝ) • 1) = ⟨5,0,4⟩ :=
  checkAdjacencyInertiaAt_sound graph endpoint_2 ⟨5,0,4⟩ (by decide +kernel)

theorem query_0 :
    (Finset.univ.filter fun j => (endpoint_0 : ℝ) < (adjacency_isHermitian graph).eigenvalues j ∧
      (adjacency_isHermitian graph).eigenvalues j ≤ (endpoint_1 : ℝ)).card = 4 := by
  rw [Inertia.eigenvalue_count_Ioc_eq _ (adjacency_isHermitian graph) _ _ (by norm_num [endpoint_0, endpoint_1]),
    inertia_0, inertia_1]
  decide

theorem query_1 :
    (Finset.univ.filter fun j => (endpoint_1 : ℝ) < (adjacency_isHermitian graph).eigenvalues j ∧
      (adjacency_isHermitian graph).eigenvalues j ≤ (endpoint_2 : ℝ)).card = 0 := by
  rw [Inertia.eigenvalue_count_Ioc_eq _ (adjacency_isHermitian graph) _ _ (by norm_num [endpoint_1, endpoint_2]),
    inertia_1, inertia_2]
  decide

end SpectralGraphTests.Hoffman.RookReport
