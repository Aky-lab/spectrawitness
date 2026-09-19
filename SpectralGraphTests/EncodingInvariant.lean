import SpectralGraph.Graph.EncodingInvariant

namespace SpectralGraphTests.EncodingInvariant
open SpectralGraph.Graph

-- Strict row validity is preserved even though edge storage need not be symmetric.
example : PackedRowsValid 3 (extendPackedRows #[2, 1] ({0} : Finset (Fin 2))) := by
  exact (show PackedRowsValid 2 #[2, 1] by decide).extend _
example : symmetricPackedRowsValid 3 (extendPackedRows #[2, 1] ({0} : Finset (Fin 2))) = false := by
  decide
-- Rebuilding masks high bits and writes exact dimensions.
example : PackedRowsValid 2 (extendPackedRows #[4] ({0} : Finset (Fin 1))) := by
  exact (packedRowsValid_extend_iff _ _).mpr (by decide)
example : PackedRowsValid 2 (extendPackedRows #[] (∅ : Finset (Fin 1))) := by
  exact (packedRowsValid_extend_iff _ _).mpr (by decide)
-- Existing loops survive and remain invalid; the invariant never hides this defect.
example : packedRowsValid 2 (extendPackedRows #[1] ({0} : Finset (Fin 1))) = false := by
  decide
-- Generic proofs discharge validity for any size, without evaluating a large census.
example (n d : Nat) {rows : PackedAdjacencyRows}
    (hr : rows ∈ packedConnectedDegreeGraphsFast n d) : rows.size = n :=
  (packedConnectedDegreeGraphsFast_valid n d hr).1

#print axioms PackedRowsValid.extend
#print axioms packedConnectedDegreeGraphs_valid
#print axioms packedConnectedDegreeGraphsFast_all_valid
end SpectralGraphTests.EncodingInvariant
