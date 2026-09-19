import SpectralGraph.Graph.PackedEnumerationFast

namespace SpectralGraphTests.PackedEnumerationFast
open SpectralGraph.Graph

-- For eight isolated vertices and bound three, generate 8 + 28 + 56 subsets,
-- without constructing the remaining 164 subsets of the full powerset.
example : (packedDegreeSelectionListFast 8 3 #[]).length = 92 := by decide
-- All vertices of a triangle are saturated at bound two.
example : packedDegreeSelectionListFast 3 2 #[6, 4, 0] = [] := by decide
example : (packedDegreeSelectionListFast 3 3 #[6, 4, 0]).length = 7 := by decide
-- End-to-end optimized recursion retains the exact reference outputs.
example : (packedConnectedDegreeGraphsFast 4 2).length = 6 := by decide
example : (packedConnectedDegreeGraphsFast 4 3).length = 21 := by decide
example : packedConnectedDegreeGraphsFast 3 1 = [] := by decide
-- A real streamed child check: every one-vertex extension has exactly n+1 rows.
example : allPackedDegreeExtensionsFast 5 3 #[] (fun rows ↦ decide (rows.size = 6)) = true := by
  decide
example : allPackedDegreeExtensionsFast 5 3 #[] (fun rows ↦ decide (rows.size = 5)) = false := by
  decide

#print axioms mem_packedConnectedDegreeGraphsFast_iff
#print axioms packedConnectedDegreeGraphsFast_complete
#print axioms allPackedDegreeExtensionsFast_eq_true_iff
end SpectralGraphTests.PackedEnumerationFast
