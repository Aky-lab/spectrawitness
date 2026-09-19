import SpectralGraph.Graph.Biadjacency
import SpectralGraphTests.Bipartite
import SpectralGraph.Inertia.Diagonal

namespace SpectralGraphTests.Biadjacency
open SpectralGraph SpectralGraph.Graph SpectralGraph.Inertia Matrix
open SpectralGraphTests.Bipartite

-- The row Gram entry equals a vertex degree through graph semantics.
example : (biadjacencyMatrix pathThree side * (biadjacencyMatrix pathThree side).transpose)
    ⟨0, by decide⟩ ⟨0, by decide⟩ = 1 := by
  rw [biadjacency_mul_transpose_apply_self_eq_degree pathThree side path_bipartite]
  exact_mod_cast (show pathThree.degree (0 : Fin 3) = 1 by decide)

-- A 1-by-2 block exercises unequal sides and the full shifted inertia formula.
def block : Matrix (Fin 1) (Fin 2) ℝ := fun _ _ ↦ 1

private theorem block_gram (t : ℝ) :
    rowGramAt block t = Matrix.diagonal (fun _ : Fin 1 ↦ 2 - t) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [rowGramAt, block, Matrix.mul_apply]

example : matrixInertia (Matrix.fromBlocks ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
    block block.transpose ((2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))) =
      { pos := 3, zero := 0, neg := 0 } := by
  rw [bipartiteBlock_pos_shift_inertia block (by norm_num : (0 : ℝ) < 2), block_gram]
  norm_num [SpectralGraph.matrixInertia_diagonal]

example : matrixInertia (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ)
    block block.transpose (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
      { pos := 2, zero := 0, neg := 1 } := by
  have h := bipartiteBlock_pos_shift_inertia block (by norm_num : (0 : ℝ) < 1)
  norm_num [block_gram, SpectralGraph.matrixInertia_diagonal, matrixInertia_one] at h
  exact h

def twoEdges : SimpleGraph (Fin 4) := graphOfPackedRows 4 #[4, 8, 0, 0]
instance : DecidableRel twoEdges.Adj :=
  inferInstanceAs (DecidableRel (graphOfPackedRows 4 #[4, 8, 0, 0]).Adj)
def twoEdgeSide : Set (Fin 4) := {v | v.val < 2}
instance : DecidablePred (· ∈ twoEdgeSide) := fun v ↦ inferInstanceAs (Decidable (v.val < 2))
private theorem twoEdges_bipartite : twoEdges.IsBipartiteWith twoEdgeSide twoEdgeSideᶜ where
  disjoint := disjoint_compl_right
  mem_of_adj := by decide

-- A nonunit threshold forces two negative directions from degrees and common-neighbor counts.
example : 2 ≤ (matrixInertia ((1 / 2 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ) +
    twoEdges.adjMatrix ℝ)).neg := by
  apply two_le_shiftedAdjMatrix_neg_of_commonNeighbor_minor twoEdges twoEdgeSide
    twoEdges_bipartite (by norm_num : (0 : ℝ) < 1 / 2)
    (x := ⟨0, by decide⟩) (y := ⟨1, by decide⟩) (by decide)
  · have hd : twoEdges.degree (0 : Fin 4) = 1 := by decide
    norm_num [hd]
  · have hx : twoEdges.degree (0 : Fin 4) = 1 := by decide
    have hy : twoEdges.degree (1 : Fin 4) = 1 := by decide
    have hc : Fintype.card (twoEdges.commonNeighbors (0 : Fin 4) 1) = 0 := by decide
    norm_num [hx, hy, hc]

#print axioms shiftedAdjMatrix_inertia_eq_biadjacencyGram
#print axioms bipartiteBlock_pos_shift_inertia
end SpectralGraphTests.Biadjacency

