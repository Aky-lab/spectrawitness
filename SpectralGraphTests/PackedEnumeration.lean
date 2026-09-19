import SpectralGraph.Graph.PackedEnumeration

/-! Small, kernel-reduced enumeration regressions; these exercise the actual
executable list generator, including empty orders and restrictive bounds. -/
namespace SpectralGraphTests.PackedEnumeration
open SpectralGraph.Graph

example : packedConnectedDegreeGraphs 0 3 = [] := by decide
example : packedConnectedDegreeGraphs 1 0 = [#[0]] := by decide
example : packedConnectedDegreeGraphs 2 0 = [] := by decide
example : (packedConnectedDegreeGraphs 2 1).length = 1 := by decide
example : packedConnectedDegreeGraphs 3 1 = [] := by decide
-- Two labelled paths and one triangle; isomorphic duplicates are intentional.
example : (packedConnectedDegreeGraphs 3 2).length = 3 := by decide
-- Saturated vertices are pruned before the next extension step.
example : (packedConnectedDegreeGraphs 4 2).length = 6 := by decide
example : (packedConnectedDegreeGraphs 4 3).length = 21 := by decide

-- Completeness plus an empty computed list proves a universal impossibility.
example (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj]
    (hG : G.Connected) (hd : HasDegreeAtMost G 1) : False := by
  obtain ⟨rows, hrows, _⟩ := packedConnectedDegreeGraphs_complete 3 1 G hG hd
  have hempty : packedConnectedDegreeGraphs 3 1 = [] := by decide
  rw [hempty] at hrows
  exact List.not_mem_nil hrows

#print axioms packedConnectedDegreeGraphs_complete
#print axioms packedConnectedDegreeGraphs_sound
end SpectralGraphTests.PackedEnumeration
