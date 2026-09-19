import SpectralGraph.Graph.Bipartite
import SpectralGraph.Inertia.BipartiteBlock
import SpectralGraph.Inertia.NegativeWitness

/-! Bipartite adjacency blocks, common-neighbor Gram matrices and exact Schur reduction. -/
namespace SpectralGraph.Graph
open SpectralGraph.Inertia Matrix
open scoped SimpleGraph
universe u

/-- The real biadjacency block from a set to its complement. -/
def biadjacencyMatrix
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidablePred (· ∈ s)] :
    Matrix s (sᶜ : Set V) ℝ :=
  (G.adjMatrix ℝ).toBlock (· ∈ s) (· ∉ s)

/-- An entry of the square of an adjacency matrix counts common neighbors.
This is independent of bipartiteness and is useful whenever a Gram matrix is
identified with a restricted adjacency square. -/
theorem adjMatrix_mul_self_apply_eq_card_commonNeighbors
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    (G.adjMatrix ℝ * G.adjMatrix ℝ) x y =
      (Fintype.card (G.commonNeighbors x y) : ℝ) := by
  rw [SimpleGraph.adjMatrix_mul_apply]
  simp only [SimpleGraph.adjMatrix_apply, Finset.sum_boole]
  norm_cast
  rw [← Set.toFinset_card]
  congr 1
  ext z
  simp [SimpleGraph.commonNeighbors_eq, G.adj_comm]

/-- On one side of a bipartition, the biadjacency row Gram matrix counts
common neighbors in the whole graph. -/
theorem biadjacency_mul_transpose_apply_eq_card_commonNeighbors
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidablePred (· ∈ s)]
    (h : G.IsBipartiteWith s sᶜ) (x y : s) :
    (biadjacencyMatrix G s * (biadjacencyMatrix G s).transpose) x y =
      (Fintype.card (G.commonNeighbors x y) : ℝ) := by
  let f : {z : (sᶜ : Set V) // G.Adj x z ∧ G.Adj y z} →
      G.commonNeighbors x y := fun z => ⟨z.1.1, z.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro z w hzw
      apply Subtype.ext
      apply Subtype.ext
      change (f z).1 = (f w).1
      rw [hzw]
    · intro z
      have hz : z.1 ∈ sᶜ := by
        rcases h.mem_of_adj z.2.1 with hz | hz
        · exact hz.2
        · exact (hz.1 x.property).elim
      exact ⟨⟨⟨z.1, hz⟩, z.2⟩, rfl⟩
  let e : {z : (sᶜ : Set V) // G.Adj x z ∧ G.Adj y z} ≃
      G.commonNeighbors x y := Equiv.ofBijective f hf
  calc
    (biadjacencyMatrix G s * (biadjacencyMatrix G s).transpose) x y =
        ∑ z : (sᶜ : Set V), if G.Adj x z ∧ G.Adj y z then (1 : ℝ) else 0 := by
          rw [Matrix.mul_apply]
          simp only [biadjacencyMatrix, Matrix.toBlock_apply,
            Matrix.transpose_apply, SimpleGraph.adjMatrix_apply]
          apply Finset.sum_congr rfl
          intro z hz
          by_cases hxz : G.Adj x z <;> by_cases hyz : G.Adj y z <;>
            simp [hxz, hyz]
    _ = (Fintype.card {z : (sᶜ : Set V) // G.Adj x z ∧ G.Adj y z} : ℝ) := by
      rw [Finset.sum_boole]
      norm_cast
      simpa only [Set.toFinset_setOf] using
        (Set.toFinset_card {z : (sᶜ : Set V) | G.Adj x z ∧ G.Adj y z})
    _ = (Fintype.card (G.commonNeighbors x y) : ℝ) := by
      exact_mod_cast Fintype.card_congr e

/-- The diagonal row-Gram entries are vertex degrees. -/
theorem biadjacency_mul_transpose_apply_self_eq_degree
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidablePred (· ∈ s)]
    (h : G.IsBipartiteWith s sᶜ) (x : s) :
    (biadjacencyMatrix G s * (biadjacencyMatrix G s).transpose) x x =
      (G.degree x : ℝ) := by
  rw [biadjacency_mul_transpose_apply_eq_card_commonNeighbors G s h]
  norm_cast
  simpa [SimpleGraph.commonNeighbors_eq] using
    (G.card_neighborSet_eq_degree x)

/-- Diagonal entries of the shifted row Gram matrix. -/
theorem biadjacencyRowGram_sub_one_apply_self
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidablePred (· ∈ s)]
    (h : G.IsBipartiteWith s sᶜ) (x : s) :
    (biadjacencyMatrix G s * (biadjacencyMatrix G s).transpose -
      (1 : Matrix s s ℝ)) x x =
      (G.degree x : ℝ) - 1 := by
  rw [Matrix.sub_apply,
    biadjacency_mul_transpose_apply_self_eq_degree G s h]
  simp

/-- Off-diagonal entries of the shifted row Gram matrix. -/
theorem biadjacencyRowGram_sub_one_apply_of_ne
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidablePred (· ∈ s)]
    (h : G.IsBipartiteWith s sᶜ) {x y : s} (hxy : x ≠ y) :
    (biadjacencyMatrix G s * (biadjacencyMatrix G s).transpose -
      (1 : Matrix s s ℝ)) x y =
      (Fintype.card (G.commonNeighbors x y) : ℝ) := by
  rw [Matrix.sub_apply,
    biadjacency_mul_transpose_apply_eq_card_commonNeighbors G s h]
  simp [hxy]

/-- The common-neighbor principal-minor criterion used in dense bipartite
obstructions.  It is stated without any degree or order specialization. -/
theorem two_le_biadjacencyRowGram_sub_one_pos_of_commonNeighbor_minor
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidablePred (· ∈ s)]
    (h : G.IsBipartiteWith s sᶜ) {x y : s} (hxy : x ≠ y)
    (hx : 0 < (G.degree x : ℝ) - 1)
    (hdet :
      (Fintype.card (G.commonNeighbors x y) : ℝ) ^ 2 <
        ((G.degree x : ℝ) - 1) * ((G.degree y : ℝ) - 1)) :
    2 ≤ (matrixInertia
      (biadjacencyMatrix G s * (biadjacencyMatrix G s).transpose - 1)).pos := by
  let B := biadjacencyMatrix G s
  let M : Matrix s s ℝ := B * B.transpose - 1
  have hM : M.IsSymm := by
    rw [Matrix.IsSymm]
    simp [M, Matrix.transpose_sub, Matrix.transpose_mul]
  have htwo : 2 ≤ (matrixInertia M).pos := by
    apply two_le_matrixInertia_pos_of_principal_pair M hM x y
    · rw [show M x x = (G.degree x : ℝ) - 1 by
          simpa [M, B] using biadjacencyRowGram_sub_one_apply_self G s h x]
      exact hx
    · rw [show M x x = (G.degree x : ℝ) - 1 by
          simpa [M, B] using biadjacencyRowGram_sub_one_apply_self G s h x,
        show M y y = (G.degree y : ℝ) - 1 by
          simpa [M, B] using biadjacencyRowGram_sub_one_apply_self G s h y,
        show M x y = (Fintype.card (G.commonNeighbors x y) : ℝ) by
          simpa [M, B] using
            biadjacencyRowGram_sub_one_apply_of_ne G s h hxy]
      exact sub_pos.mpr hdet
  simpa [M, B] using htwo

/-- Reindexing a bipartite adjacency matrix by a side and its complement
gives the expected off-diagonal block matrix. -/
theorem adjMatrix_submatrix_sumCompl_eq_fromBlocks
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidablePred (· ∈ s)]
    (h : G.IsBipartiteWith s sᶜ) :
    (G.adjMatrix ℝ).submatrix (Equiv.Set.sumCompl s) (Equiv.Set.sumCompl s) =
      Matrix.fromBlocks 0 (biadjacencyMatrix G s)
        (biadjacencyMatrix G s).transpose 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · have hn : ¬G.Adj i j := by
      intro hij
      rcases h.mem_of_adj hij with hij | hij
      · exact hij.2 j.property
      · exact hij.1 i.property
    simp [biadjacencyMatrix,
      Matrix.fromBlocks_apply₁₁, SimpleGraph.adjMatrix_apply, hn]
  · rfl
  · simp [biadjacencyMatrix, Matrix.toBlock_apply,
      Matrix.fromBlocks_apply₂₁, SimpleGraph.adjMatrix_apply, G.adj_comm]
  · have hn : ¬G.Adj i j := by
      intro hij
      rcases h.mem_of_adj hij with hij | hij
      · exact i.property hij.1
      · exact j.property hij.2
    simp [biadjacencyMatrix,
      Matrix.fromBlocks_apply₂₂, SimpleGraph.adjMatrix_apply, hn]

/-- Unit-shift compatibility wrapper. For arbitrary shifts, prefer
`shiftedAdjMatrix_submatrix_sumCompl_eq_fromBlocks`. -/
theorem unitAdjMatrix_submatrix_sumCompl_eq_fromBlocks
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidablePred (· ∈ s)]
    (h : G.IsBipartiteWith s sᶜ) :
    (1 + G.adjMatrix ℝ).submatrix
        (Equiv.Set.sumCompl s) (Equiv.Set.sumCompl s) =
      Matrix.fromBlocks 1 (biadjacencyMatrix G s)
        (biadjacencyMatrix G s).transpose 1 := by
  rw [Matrix.submatrix_add]
  change
    (1 : Matrix V V ℝ).submatrix (Equiv.Set.sumCompl s) (Equiv.Set.sumCompl s) +
        (G.adjMatrix ℝ).submatrix (Equiv.Set.sumCompl s) (Equiv.Set.sumCompl s) = _
  rw [Matrix.submatrix_one_equiv,
    adjMatrix_submatrix_sumCompl_eq_fromBlocks G s h]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.one_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

/-- Unit-shift compatibility formula for a rectangular block.
For the full matrix-only formula at arbitrary positive shifts, prefer
`SpectralGraph.Inertia.bipartiteBlock_pos_shift_inertia`. -/
theorem fromBlocks_unit_neg_eq_rowSchur_neg
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (B : Matrix ι κ ℝ) :
    (matrixInertia (Matrix.fromBlocks 1 B B.transpose 1)).neg =
      (matrixInertia (1 - B * B.transpose)).neg := by
  letI : Invertible (1 : Matrix κ κ ℝ) := invertibleOne
  have h := matrixInertia_fromBlocks_schur₂₂
    (1 : Matrix ι ι ℝ) B (1 : Matrix κ κ ℝ) Matrix.isSymm_one
  simpa [SpectralGraph.Inertia.matrixInertia_one] using congrArg Inertia.neg h

/-- Unit-shift compatibility formula in Gram coordinates.
Prefer `SpectralGraph.Inertia.bipartiteBlock_pos_shift_inertia` for arbitrary
positive shifts or the full inertia triple. -/
theorem fromBlocks_unit_neg_eq_rowGram_sub_one_pos
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (B : Matrix ι κ ℝ) :
    (matrixInertia (Matrix.fromBlocks 1 B B.transpose 1)).neg =
      (matrixInertia (B * B.transpose - 1)).pos := by
  rw [fromBlocks_unit_neg_eq_rowSchur_neg]
  have hneg := matrixInertia_neg (B * B.transpose - 1)
  have hmatrix : 1 - B * B.transpose = -(B * B.transpose - 1) := by
    module
  rw [hmatrix, hneg]

/-- Unit-shift compatibility interface. For the full inertia triple at arbitrary
positive shifts, prefer `shiftedAdjMatrix_inertia_eq_biadjacencyGram`.
The negative index of `I+A(G)`
is the positive index of the shifted row Gram matrix of either biadjacency
block. -/
theorem unitAdjMatrix_neg_eq_biadjacencyRowGram_sub_one_pos
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidablePred (· ∈ s)]
    (h : G.IsBipartiteWith s sᶜ) :
    (matrixInertia (1 + G.adjMatrix ℝ)).neg =
      (matrixInertia
        (biadjacencyMatrix G s * (biadjacencyMatrix G s).transpose - 1)).pos := by
  let e := Equiv.Set.sumCompl s
  have hreindex := matrixInertia_submatrix_equiv
    (1 + G.adjMatrix ℝ) e
  have hblock := unitAdjMatrix_submatrix_sumCompl_eq_fromBlocks G s h
  calc
    (matrixInertia (1 + G.adjMatrix ℝ)).neg =
        (matrixInertia ((1 + G.adjMatrix ℝ).submatrix e e)).neg := by
          exact congrArg Inertia.neg hreindex.symm
    _ = (matrixInertia (Matrix.fromBlocks 1 (biadjacencyMatrix G s)
          (biadjacencyMatrix G s).transpose 1)).neg := by rw [hblock]
    _ = _ := fromBlocks_unit_neg_eq_rowGram_sub_one_pos
      (biadjacencyMatrix G s)

/-- A positive common-neighbor principal minor on either side of a
bipartition forces two negative directions in `I + A(G)`. -/
theorem two_le_unitAdjMatrix_neg_of_bipartite_commonNeighbor_minor
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidablePred (· ∈ s)]
    (h : G.IsBipartiteWith s sᶜ) {x y : s} (hxy : x ≠ y)
    (hx : 0 < (G.degree x : ℝ) - 1)
    (hdet :
      (Fintype.card (G.commonNeighbors x y) : ℝ) ^ 2 <
        ((G.degree x : ℝ) - 1) * ((G.degree y : ℝ) - 1)) :
    2 ≤ (matrixInertia (1 + G.adjMatrix ℝ)).neg := by
  rw [unitAdjMatrix_neg_eq_biadjacencyRowGram_sub_one_pos G s h]
  exact two_le_biadjacencyRowGram_sub_one_pos_of_commonNeighbor_minor
    G s h hxy hx hdet


end SpectralGraph.Graph



namespace SpectralGraph.Graph
open SpectralGraph.Inertia Matrix

/-- A real scalar adjacency shift respects the bipartition block structure. -/
theorem shiftedAdjMatrix_submatrix_sumCompl_eq_fromBlocks
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidablePred (· ∈ s)]
    (h : G.IsBipartiteWith s sᶜ) (t : ℝ) :
    (t • (1 : Matrix V V ℝ) + G.adjMatrix ℝ).submatrix
        (Equiv.Set.sumCompl s) (Equiv.Set.sumCompl s) =
      Matrix.fromBlocks (t • 1) (biadjacencyMatrix G s)
        (biadjacencyMatrix G s).transpose (t • 1) := by
  rw [Matrix.submatrix_add]
  change (t • (1 : Matrix V V ℝ)).submatrix (Equiv.Set.sumCompl s) (Equiv.Set.sumCompl s) +
      (G.adjMatrix ℝ).submatrix (Equiv.Set.sumCompl s) (Equiv.Set.sumCompl s) = _
  have hscalar : (t • (1 : Matrix V V ℝ)).submatrix
      (Equiv.Set.sumCompl s) (Equiv.Set.sumCompl s) = t • 1 := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.one_apply]
  rw [hscalar, adjMatrix_submatrix_sumCompl_eq_fromBlocks G s h]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.one_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

/-- Full shifted adjacency inertia from the smaller bipartite Gram problem.
The shift is arbitrary and positive; the Gram threshold is its square. -/
theorem shiftedAdjMatrix_inertia_eq_biadjacencyGram
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidablePred (· ∈ s)]
    (h : G.IsBipartiteWith s sᶜ) {t : ℝ} (ht : 0 < t) :
    matrixInertia (t • (1 : Matrix V V ℝ) + G.adjMatrix ℝ) =
      { pos := (matrixInertia (rowGramAt (biadjacencyMatrix G s) (t ^ 2))).neg +
          Fintype.card (sᶜ : Set V)
        zero := (matrixInertia (rowGramAt (biadjacencyMatrix G s) (t ^ 2))).zero
        neg := (matrixInertia (rowGramAt (biadjacencyMatrix G s) (t ^ 2))).pos } := by
  rw [← matrixInertia_submatrix_equiv _ (Equiv.Set.sumCompl s),
    shiftedAdjMatrix_submatrix_sumCompl_eq_fromBlocks G s h t]
  exact bipartiteBlock_pos_shift_inertia _ ht

/-- At a positive adjacency threshold, either side's Gram matrix yields the
same negative index of the shifted graph matrix. -/
theorem shiftedAdjMatrix_neg_eq_biadjacencyColGram_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidablePred (· ∈ s)]
    (h : G.IsBipartiteWith s sᶜ) {t : ℝ} (ht : 0 < t) :
    (matrixInertia (t • (1 : Matrix V V ℝ) + G.adjMatrix ℝ)).neg =
      (matrixInertia (colGramAt (biadjacencyMatrix G s) (t ^ 2))).pos := by
  rw [shiftedAdjMatrix_inertia_eq_biadjacencyGram G s h ht]
  exact gramAt_pos_eq _ (sq_pos_of_pos ht)

/-- Diagonal entries of a shifted biadjacency Gram matrix are degree minus threshold. -/
theorem biadjacencyRowGramAt_apply_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidablePred (· ∈ s)]
    (h : G.IsBipartiteWith s sᶜ) (r : ℝ) (x : s) :
    rowGramAt (biadjacencyMatrix G s) r x x = (G.degree x : ℝ) - r := by
  simp [rowGramAt, Matrix.sub_apply,
    biadjacency_mul_transpose_apply_self_eq_degree G s h]

/-- Off-diagonal shifted Gram entries count common neighbors, at every threshold. -/
theorem biadjacencyRowGramAt_apply_of_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidablePred (· ∈ s)]
    (h : G.IsBipartiteWith s sᶜ) (r : ℝ) {x y : s} (hxy : x ≠ y) :
    rowGramAt (biadjacencyMatrix G s) r x y =
      (Fintype.card (G.commonNeighbors x y) : ℝ) := by
  simp [rowGramAt, Matrix.sub_apply, hxy,
    biadjacency_mul_transpose_apply_eq_card_commonNeighbors G s h]

/-- A common-neighbor two-by-two minor forces two negative directions below an
arbitrary negative adjacency threshold. No degree or order specialization is used. -/
theorem two_le_shiftedAdjMatrix_neg_of_commonNeighbor_minor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidablePred (· ∈ s)]
    (h : G.IsBipartiteWith s sᶜ) {t : ℝ} (ht : 0 < t)
    {x y : s} (hxy : x ≠ y)
    (hx : 0 < (G.degree x : ℝ) - t ^ 2)
    (hdet : (Fintype.card (G.commonNeighbors x y) : ℝ) ^ 2 <
      ((G.degree x : ℝ) - t ^ 2) * ((G.degree y : ℝ) - t ^ 2)) :
    2 ≤ (matrixInertia (t • (1 : Matrix V V ℝ) + G.adjMatrix ℝ)).neg := by
  rw [shiftedAdjMatrix_inertia_eq_biadjacencyGram G s h ht]
  apply two_le_matrixInertia_pos_of_principal_pair
    (rowGramAt (biadjacencyMatrix G s) (t ^ 2))
    (by simp [rowGramAt, Matrix.IsSymm, Matrix.transpose_sub, Matrix.transpose_mul]) x y
  · simpa [biadjacencyRowGramAt_apply_self G s h] using hx
  · simpa [biadjacencyRowGramAt_apply_self G s h,
      biadjacencyRowGramAt_apply_of_ne G s h _ hxy] using sub_pos.mpr hdet

end SpectralGraph.Graph

