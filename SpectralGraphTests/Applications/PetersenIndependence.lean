import SpectralGraph.Graph.Independence
import SpectralGraphTests.Independence.PetersenReport

/-! The named Petersen report's zero endpoint gives its sharp independence bound. -/

namespace SpectralGraphTests.Applications.PetersenIndependence

open SpectralGraph SpectralGraph.Graph
open SpectralGraphTests.Independence

private theorem petersen_inertia :
    matrixInertia (Definitions.petersen.adjMatrix ℝ) = ⟨6, 0, 4⟩ := by
  simpa [PetersenReport.graph, PetersenReport.endpoint_0] using PetersenReport.inertia_0

theorem indepSet_card_le_four (s : Finset (Fin 10))
    (hs : Definitions.petersen.IsIndepSet (↑s : Set (Fin 10))) : s.card ≤ 4 := by
  have h := indepSet_card_le_adjacency_inertia Definitions.petersen s hs
  simpa [petersen_inertia] using h

theorem indepNum_eq_four : Definitions.petersen.indepNum = 4 := by
  have hu := indepNum_le_adjacency_inertia Definitions.petersen
  have hu' : Definitions.petersen.indepNum ≤ 4 := by
    simpa [petersen_inertia] using hu
  have hset : Definitions.petersen.IsIndepSet
      ({0, 2, 8, 9} : Finset (Fin 10)) := by decide +kernel
  have hl := hset.card_le_indepNum
  have hcard : ({0, 2, 8, 9} : Finset (Fin 10)).card = 4 := by decide +kernel
  rw [hcard] at hl
  exact Nat.le_antisymm hu' hl

end SpectralGraphTests.Applications.PetersenIndependence
