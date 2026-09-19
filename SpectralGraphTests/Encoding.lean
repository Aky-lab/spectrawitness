import SpectralGraph.Graph.EncodingCheck

/-! Kernel-checked encoding boundary and semantics examples. -/

open SpectralGraph.Graph

-- The empty graph has an exact empty encoding.
example : packedRowsValid 0 #[] = true := by decide
example : symmetricPackedRowsValid 0 #[] = true := by decide

-- P₃ in triangular and full symmetric formats.
example : packedRowsValid 3 #[2, 4, 0] = true := by decide
example : symmetricPackedRowsValid 3 #[2, 5, 2] = true := by decide
example : symmetricPackedRowsValid 3 #[2, 4, 0] = false := by decide
example : graphOfPackedRows 3 #[2, 4, 0] = graphOfPackedRows 3 #[2, 5, 2] := by
  apply (graphOfPackedRows_eq_iff _ _ _).mpr
  decide

-- Wrong dimensions, high bits, and loops are independently rejected.
example : packedRowsValid 3 #[2, 4] = false := by decide
example : packedRowsValid 3 #[2, 4, 0, 0] = false := by decide
example : packedRowsValid 3 #[10, 4, 0] = false := by decide
example : packedRowsValid 3 #[3, 4, 0] = false := by decide
example : packedRowsValid 0 #[0] = false := by decide

-- The total decoder has defined semantics even for malformed input.
example : packedDegreeAt 3 #[3, 4] 0 = 1 := by decide
example : packedDegreeAt 3 #[3, 4] 1 = 2 := by decide
example : packedDegreeAt 3 #[3, 4] 3 = 0 := by decide
example : packedAdjacencyMatrix Int 3 #[3, 4] 0 0 = 0 := by decide
example : packedAdjacencyMatrix Int 3 #[3, 4] 2 1 = 1 := by decide

-- Checked raw matrix entries agree with mathlib, not just the forgiving decoder.
example : (fun i j : Fin 3 ↦ if packedAdjacencyBit #[2, 5, 2] i.val j.val
      then (1 : Int) else 0) = (graphOfPackedRows 3 #[2, 5, 2]).adjMatrix Int := by
  exact rawPackedMatrix_eq_adjMatrix Int (by decide)

example : extendPackedRows (n := 2) #[2, 0] {1} = #[2, 4, 0] := by decide
example : graphOfPackedRows 3 (extendPackedRows (n := 2) #[2, 0] {1}) =
    oneVertexExtension (graphOfPackedRows 2 #[2, 0]) {1} :=
  graphOfPackedRows_extend _ _

#print axioms graphOfPackedRows_extend
#print axioms packedRowsValid_eq_true_iff
#print axioms graphOfPackedRows_adj_iff_of_symmetric
#print axioms rawPackedMatrix_eq_adjMatrix
