import SpectralGraph.Graph.EncodingCheck
import SpectralGraph.Graph.IntegerSpectrum
import SpectralGraphTests.Independence.Definitions

/- Generated from exact JSON, SHA256 dd599075b02e957c065b65021ff43755a65a03f7c40f8baf60705b392bdf6475.
The external producer is untrusted; compile this file for kernel verification. -/
namespace SpectralGraphTests.Independence.PetersenReport
open SpectralGraph SpectralGraph.Graph

def rows : PackedAdjacencyRows := #[50, 68, 136, 272, 512, 384, 768, 512, 0, 0]
theorem rows_valid : packedRowsValid 10 rows = true := by decide +kernel
def emittedGraph : SimpleGraph (Fin 10) := graphOfPackedRows 10 rows
instance : DecidableRel emittedGraph.Adj := by unfold emittedGraph; infer_instance
def graph : SimpleGraph (Fin 10) := _root_.SpectralGraphTests.Independence.Definitions.petersen
instance : DecidableRel graph.Adj := by unfold graph; infer_instance
theorem graph_matches : emittedGraph = graph := by
  have h : ∀ i j : Fin 10, emittedGraph.Adj i j ↔ graph.Adj i j := by decide +kernel
  ext i j
  exact h i j

def endpoint_0 : ℚ := 0
theorem inertia_0 : matrixInertia (graph.adjMatrix ℝ - (endpoint_0 : ℝ) • 1) = ⟨6,0,4⟩ :=
  checkAdjacencyInertiaAt_sound graph endpoint_0 ⟨6,0,4⟩ (by decide +kernel)

def endpoint_1 : ℚ := 4
theorem inertia_1 : matrixInertia (graph.adjMatrix ℝ - (endpoint_1 : ℝ) • 1) = ⟨0,0,10⟩ :=
  checkAdjacencyInertiaAt_sound graph endpoint_1 ⟨0,0,10⟩ (by decide +kernel)

theorem query_0 :
    (Finset.univ.filter fun j => (endpoint_0 : ℝ) < (adjacency_isHermitian graph).eigenvalues j ∧
      (adjacency_isHermitian graph).eigenvalues j ≤ (endpoint_1 : ℝ)).card = 6 := by
  rw [Inertia.eigenvalue_count_Ioc_eq _ (adjacency_isHermitian graph) _ _ (by norm_num [endpoint_0, endpoint_1]),
    inertia_0, inertia_1]
  decide

end SpectralGraphTests.Independence.PetersenReport
