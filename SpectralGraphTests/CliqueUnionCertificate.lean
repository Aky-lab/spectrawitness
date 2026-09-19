import SpectralGraph.Graph.EncodingCheck
import SpectralGraph.Graph.IntegerSpectrum

/-! Kernel-checked adjacency inertia for `K₃ ⊔ K₂ ⊔ K₁`. -/

namespace SpectralGraphTests.CliqueUnionCertificate

open SpectralGraph SpectralGraph.Graph

/-- Packed upper-triangular rows for a triangle on `0,1,2`, an edge on
`3,4`, and the isolated vertex `5`. -/
def rows : PackedAdjacencyRows := #[6, 4, 0, 16, 0, 0]

theorem rows_valid : packedRowsValid 6 rows = true := by decide +kernel

/-- The named six-vertex graph `K₃ ⊔ K₂ ⊔ K₁`. -/
def graph : SimpleGraph (Fin 6) := graphOfPackedRows 6 rows

instance : DecidableRel graph.Adj := by unfold graph; infer_instance

def triangleCell : Finset (Fin 6) := {0, 1, 2}
def edgeCell : Finset (Fin 6) := {3, 4}
def isolatedCell : Finset (Fin 6) := {5}

theorem cell_cardinalities :
    triangleCell.card = 3 ∧ edgeCell.card = 2 ∧ isolatedCell.card = 1 := by
  decide +kernel

theorem adjacency_description (i j : Fin 6) : graph.Adj i j ↔
    i ≠ j ∧ ((i ∈ triangleCell ∧ j ∈ triangleCell) ∨
      (i ∈ edgeCell ∧ j ∈ edgeCell)) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- Exact singular shifted-adjacency inertia: three positive and three zero
directions, with no negative direction. -/
theorem shifted_inertia :
    matrixInertia (graph.adjMatrix ℝ - ((-1 : ℚ) : ℝ) • 1) = ⟨3, 3, 0⟩ :=
  checkAdjacencyInertiaAt_sound graph (-1) ⟨3, 3, 0⟩ (by decide +kernel)

end SpectralGraphTests.CliqueUnionCertificate
