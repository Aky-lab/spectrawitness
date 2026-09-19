import SpectralGraph.Graph.Bipartite
import SpectralGraph.Graph.Encoding

namespace SpectralGraphTests.Bipartite
open SpectralGraph SpectralGraph.Graph SpectralGraph.Inertia

def pathThree : SimpleGraph (Fin 3) := graphOfPackedRows 3 #[2, 4, 0]
instance : DecidableRel pathThree.Adj := inferInstanceAs (DecidableRel (graphOfPackedRows 3 #[2, 4, 0]).Adj)
def side : Set (Fin 3) := {v | v ≠ 1}
instance : DecidablePred (· ∈ side) := fun v ↦ inferInstanceAs (Decidable (v ≠ 1))

theorem path_bipartite : pathThree.IsBipartiteWith side sideᶜ where
  disjoint := disjoint_compl_right
  mem_of_adj := by decide

example : graphSignature pathThree = 0 :=
  graphSignature_eq_zero_of_isBipartite pathThree path_bipartite.isBipartite
example : (matrixInertia (pathThree.adjMatrix ℝ)).pos =
    (matrixInertia (pathThree.adjMatrix ℝ)).neg :=
  adjMatrix_pos_eq_neg_of_isBipartite pathThree path_bipartite.isBipartite

#print axioms adjMatrix_pos_eq_neg_of_isBipartite
#print axioms graphSignature_eq_zero_of_isBipartite
end SpectralGraphTests.Bipartite
