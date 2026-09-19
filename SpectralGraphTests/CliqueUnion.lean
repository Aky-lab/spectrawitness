import SpectralGraph.Graph.CliqueUnion
import SpectralGraph.Graph.IntegerSpectrum
import SpectralGraphTests.Applications.CliqueUnionSix

/-! Regression and boundary cases for the shifted-adjacency characterization. -/

namespace SpectralGraphTests.CliqueUnion

open Matrix SpectralGraph SpectralGraph.Graph

def pathThreeRows : PackedAdjacencyRows := #[2, 4, 0]

def pathThree : SimpleGraph (Fin 3) := graphOfPackedRows 3 pathThreeRows

instance : DecidableRel pathThree.Adj := by unfold pathThree; infer_instance

def pathWitness : Fin 3 → ℝ := ![1, -1, 1]

theorem pathThree_witness_value :
    dotProduct pathWitness ((1 + pathThree.adjMatrix ℝ) *ᵥ pathWitness) = -1 := by
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have hb21 : Nat.testBit 2 1 = true := by decide
  have hb22 : Nat.testBit 2 2 = false := by decide
  have hb42 : Nat.testBit 4 2 = true := by decide
  norm_num [pathWitness, pathThree, pathThreeRows, graphOfPackedRows,
    graphOfPackedRows_adj_iff, packedUndirectedAdjacencyBit,
    packedAdjacencyBit, packedAdjacencyRow,
    dotProduct, mulVec, Fin.sum_univ_succ,
    Matrix.one_apply, SimpleGraph.adjMatrix_apply, h02, h20, h12, h21,
    hb21, hb22, hb42]

theorem pathThree_not_clique_union :
    ¬pathThreeᶜ.IsCompleteMultipartite := by
  intro hstructure
  have hpsd :=
    (one_add_adjMatrix_posSemidef_iff_compl_isCompleteMultipartite pathThree).mpr hstructure
  have hnonneg := hpsd.dotProduct_mulVec_nonneg pathWitness
  have hnonneg' : 0 ≤
      dotProduct pathWitness ((1 + pathThree.adjMatrix ℝ) *ᵥ pathWitness) := by
    simpa [pathWitness] using hnonneg
  rw [pathThree_witness_value] at hnonneg'
  norm_num at hnonneg'

theorem pathThree_one_add_not_posSemidef :
    ¬(1 + pathThree.adjMatrix ℝ).PosSemidef := by
  simpa [one_add_adjMatrix_posSemidef_iff_compl_isCompleteMultipartite pathThree]
    using pathThree_not_clique_union

theorem malformed_zero_negative_claim_rejected :
    checkAdjacencyInertiaAt pathThree (-1) ⟨3, 0, 0⟩ = false := by
  decide +kernel

theorem empty_vertex_boundary :
    ((⊥ : SimpleGraph (Fin 0))ᶜ).IsCompleteMultipartite := by
  constructor
  intro x
  exact Fin.elim0 x

theorem singleton_boundary :
    ((⊥ : SimpleGraph (Fin 1))ᶜ).IsCompleteMultipartite := by
  constructor
  intro x y z hxy hyz
  fin_cases x <;> fin_cases y <;> fin_cases z
  simpa using hxy

theorem isolated_vertices_boundary :
    ((⊥ : SimpleGraph (Fin 4))ᶜ).IsCompleteMultipartite := by
  constructor
  intro x y z hxy hyz
  have hxy' : x = y := by simpa using hxy
  have hyz' : y = z := by simpa using hyz
  subst y
  subst z
  simp

theorem complete_graph_boundary :
    ((⊤ : SimpleGraph (Fin 4))ᶜ).IsCompleteMultipartite := by
  simpa using
    (SimpleGraph.bot_isCompleteMultipartite :
      (⊥ : SimpleGraph (Fin 4)).IsCompleteMultipartite)

end SpectralGraphTests.CliqueUnion
