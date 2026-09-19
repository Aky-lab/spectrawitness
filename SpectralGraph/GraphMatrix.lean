import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.IncMatrix
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.LineGraph

/-!
# Incidence, signless Laplacian, and line-graph matrices

This module provides the unsigned incidence matrix, the signless Laplacian
`Q = D + A`, and the shifted matrix `M = Q - 2I`.

Mathlib's `SimpleGraph.incMatrix` has one column for every element of `Sym2 V`.
For the line-graph identity we also define the usual edge-indexed incidence
matrix, whose columns are exactly the edges of `G`.
-/

open Matrix

namespace SpectralGraph
namespace GraphMatrix

variable {V : Type _} [Fintype V] [DecidableEq V]

/-- The signless Laplacian `Q(G) = D(G) + A(G)`. -/
def signlessLapMatrix (R : Type _) [AddMonoidWithOne R]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] : Matrix V V R :=
  G.degMatrix R + G.adjMatrix R

/-- The shifted signless Laplacian `M(G) = Q(G) - 2I`, over the reals.
The rational companion supports exact computations with this real matrix. -/
def shiftedSignless (G : _root_.SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  signlessLapMatrix ℝ G - (2 : ℝ) • (1 : Matrix V V ℝ)

/-- The exact rational form of the shifted signless Laplacian.  Keeping this
next to the real semantic matrix lets certified computations use exact
arithmetic without duplicating graph-specific matrix definitions. -/
def shiftedSignlessRat (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    Matrix V V ℚ :=
  signlessLapMatrix ℚ G - (2 : ℚ) • (1 : Matrix V V ℚ)

/-- Symmetry of the semantic shifted signless matrix. -/
theorem shiftedSignless_isSymm
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    (shiftedSignless G).IsSymm := by
  exact ((G.isSymm_degMatrix ℝ).add G.isSymm_adjMatrix).sub
    (Matrix.isSymm_one.smul 2)

/-- Symmetry of the exact shifted signless matrix. -/
theorem shiftedSignlessRat_isSymm
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    (shiftedSignlessRat G).IsSymm := by
  exact ((G.isSymm_degMatrix ℚ).add G.isSymm_adjMatrix).sub
    (Matrix.isSymm_one.smul 2)

/-- Row sum of the exact shifted signless Laplacian. -/
theorem shiftedSignlessRat_mulVec_one_apply
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (shiftedSignlessRat G *ᵥ (1 : V → ℚ)) v =
      2 * (G.degree v : ℚ) - 2 := by
  rw [shiftedSignlessRat, signlessLapMatrix, Matrix.sub_mulVec,
    Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  simp [_root_.SimpleGraph.degMatrix_mulVec_apply]
  ring

/-- The exact all-ones quadratic form
`1ᵀ(Q(G)-2I)1 = 4|E(G)|-2|V(G)|`. -/
theorem shiftedSignlessRat_allOnesQuadratic
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    (1 : V → ℚ) ⬝ᵥ shiftedSignlessRat G *ᵥ (1 : V → ℚ) =
      4 * (G.edgeFinset.card : ℚ) - 2 * (Fintype.card V : ℚ) := by
  simp only [dotProduct, Pi.one_apply, one_mul,
    shiftedSignlessRat_mulVec_one_apply]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hdegree :
      (∑ v : V, (G.degree v : ℚ)) =
        2 * (G.edgeFinset.card : ℚ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  rw [hdegree]
  simp
  ring

/-- Exact and semantic shifted signless matrices agree under the canonical
embedding `ℚ → ℝ`. -/
theorem shiftedSignlessRat_map_cast_eq_shiftedSignless
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    (shiftedSignlessRat G).map (Rat.castHom ℝ) = shiftedSignless G := by
  ext v w
  by_cases hvw : v = w
  · subst w
    simp [shiftedSignlessRat, shiftedSignless, signlessLapMatrix,
      _root_.SimpleGraph.degMatrix, _root_.SimpleGraph.adjMatrix]
  · by_cases hadj : G.Adj v w <;>
      simp [shiftedSignlessRat, shiftedSignless, signlessLapMatrix,
        _root_.SimpleGraph.degMatrix, _root_.SimpleGraph.adjMatrix, hvw, hadj]

/-- The usual unsigned incidence matrix with columns indexed by actual edges.
This is the restriction of mathlib's `G.incMatrix` to `G.edgeSet`. -/
def edgeIncMatrix (R : Type _) [Zero R] [One R]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] : Matrix V G.edgeSet R :=
  fun v e => G.incMatrix R v e.1

omit [Fintype V] in
@[simp] theorem edgeIncMatrix_apply (R : Type _) [Zero R] [One R]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (v : V) (e : G.edgeSet) :
    edgeIncMatrix R G v e = G.incMatrix R v e.1 := rfl

/-- Entrywise form of the signless Laplacian. -/
theorem signlessLapMatrix_apply (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (v w : V) :
    signlessLapMatrix ℝ G v w =
      if v = w then (G.degree v : ℝ) else if G.Adj v w then 1 else 0 := by
  by_cases hvw : v = w
  · subst w
    simp [signlessLapMatrix, _root_.SimpleGraph.degMatrix,
      _root_.SimpleGraph.adjMatrix]
  · simp [signlessLapMatrix, _root_.SimpleGraph.degMatrix,
      _root_.SimpleGraph.adjMatrix, hvw]

/-- Mathlib's full unsigned incidence-matrix product is exactly `D+A`, hence
`NNᵀ = Q(G)` for the `Sym2 V`-indexed incidence matrix. -/
theorem incMatrix_mul_transpose_eq_signlessLapMatrix
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    G.incMatrix ℝ * (G.incMatrix ℝ).transpose = signlessLapMatrix ℝ G := by
  rw [_root_.SimpleGraph.incMatrix_mul_transpose]
  ext v w
  exact (signlessLapMatrix_apply G v w).symm

/-- Restricting the incidence matrix to actual edges does not change its row
Gram matrix: every non-edge column of mathlib's full incidence matrix is
zero. -/
theorem edgeIncMatrix_mul_transpose_eq_signlessLapMatrix
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    edgeIncMatrix ℝ G * (edgeIncMatrix ℝ G).transpose =
      signlessLapMatrix ℝ G := by
  rw [← incMatrix_mul_transpose_eq_signlessLapMatrix G]
  ext v w
  change (∑ e : G.edgeSet, G.incMatrix ℝ v e.1 * G.incMatrix ℝ w e.1) =
    ∑ e : Sym2 V, G.incMatrix ℝ v e * G.incMatrix ℝ w e
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun e : Sym2 V ↦ e ∈ G.edgeSet)
    (fun e ↦ G.incMatrix ℝ v e * G.incMatrix ℝ w e)
  have hnon :
      (∑ e : {e : Sym2 V // e ∉ G.edgeSet},
        G.incMatrix ℝ v e.1 * G.incMatrix ℝ w e.1) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    have hv : G.incMatrix ℝ v e.1 = 0 :=
      G.incMatrix_of_notMem_incidenceSet (fun h ↦ e.property h.1)
    simp [hv]
  rw [hnon, add_zero] at hsplit
  exact hsplit

/-- The row Gram identity over an arbitrary commutative semiring.  This
version is used in characteristic two for the rooted determinant argument. -/
theorem edgeIncMatrix_mul_transpose_eq_signlessLapMatrix_of_commSemiring
    (S : Type*) [CommSemiring S]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    edgeIncMatrix S G * (edgeIncMatrix S G).transpose =
      signlessLapMatrix S G := by
  ext v w
  change (∑ e : G.edgeSet, G.incMatrix S v e.1 * G.incMatrix S w e.1) = _
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun e : Sym2 V ↦ e ∈ G.edgeSet)
    (fun e ↦ G.incMatrix S v e * G.incMatrix S w e)
  have hnon :
      (∑ e : {e : Sym2 V // e ∉ G.edgeSet},
        G.incMatrix S v e.1 * G.incMatrix S w e.1) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    have hv : G.incMatrix S v e.1 = 0 :=
      G.incMatrix_of_notMem_incidenceSet (fun h ↦ e.property h.1)
    simp [hv]
  rw [hnon, add_zero] at hsplit
  rw [hsplit]
  change (G.incMatrix S * (G.incMatrix S).transpose) v w = _
  rw [_root_.SimpleGraph.incMatrix_mul_transpose]
  by_cases hvw : v = w
  · subst w
    simp [signlessLapMatrix, _root_.SimpleGraph.degMatrix,
      _root_.SimpleGraph.adjMatrix]
  · simp [signlessLapMatrix, _root_.SimpleGraph.degMatrix,
      _root_.SimpleGraph.adjMatrix, hvw]

/-- Every actual edge has exactly two incidence entries equal to one, so the
edge-edge Gram matrix has diagonal entry `2`. -/
theorem edgeIncMatrix_transpose_mul_diag
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (e : G.edgeSet) :
    ((edgeIncMatrix ℝ G).transpose * edgeIncMatrix ℝ G) e e = 2 := by
  classical
  change (∑ v : V, G.incMatrix ℝ v e.1 * G.incMatrix ℝ v e.1) = 2
  have hdiag := _root_.SimpleGraph.incMatrix_transpose_mul_diag
    (R := ℝ) (G := G) (e := e.1)
  simpa [Matrix.mul_apply, e.property] using hdiag

/-- Distinct adjacent vertices of the line graph correspond to two root-graph
edges with a unique common endpoint.  Their Gram entry is therefore `1`. -/
theorem edgeIncMatrix_transpose_mul_apply_of_lineGraph_adj
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {e f : G.edgeSet} (h : G.lineGraph.Adj e f) :
    ((edgeIncMatrix ℝ G).transpose * edgeIncMatrix ℝ G) e f = 1 := by
  classical
  rw [_root_.SimpleGraph.lineGraph_adj_iff_exists] at h
  rcases h with ⟨hef, v, hve, hvf⟩
  change (∑ w : V, G.incMatrix ℝ w e.1 * G.incMatrix ℝ w f.1) = 1
  rw [Finset.sum_eq_single v]
  · have heInc : e.1 ∈ G.incidenceSet v :=
      (_root_.SimpleGraph.edge_mem_incidenceSet_iff G).2 hve
    have hfInc : f.1 ∈ G.incidenceSet v :=
      (_root_.SimpleGraph.edge_mem_incidenceSet_iff G).2 hvf
    rw [_root_.SimpleGraph.incMatrix_of_mem_incidenceSet G heInc,
      _root_.SimpleGraph.incMatrix_of_mem_incidenceSet G hfInc]
    norm_num
  · intro w hw hwv
    have hvw : v ≠ w := Ne.symm hwv
    by_cases hwe : w ∈ (e.1 : Sym2 V)
    · have hwf : w ∉ (f.1 : Sym2 V) := by
        intro hwf
        have heq : e.1 = f.1 :=
          Sym2.eq_of_ne_mem hvw hve hwe hvf hwf
        exact hef (Subtype.ext heq)
      have heInc : e.1 ∈ G.incidenceSet w :=
        (_root_.SimpleGraph.edge_mem_incidenceSet_iff G).2 hwe
      have hfNot : f.1 ∉ G.incidenceSet w := by
        simpa [_root_.SimpleGraph.edge_mem_incidenceSet_iff] using hwf
      rw [_root_.SimpleGraph.incMatrix_of_mem_incidenceSet G heInc,
        _root_.SimpleGraph.incMatrix_of_notMem_incidenceSet G hfNot]
      simp
    · have heNot : e.1 ∉ G.incidenceSet w := by
        simpa [_root_.SimpleGraph.edge_mem_incidenceSet_iff] using hwe
      rw [_root_.SimpleGraph.incMatrix_of_notMem_incidenceSet G heNot]
      simp
  · simp

/-- If two distinct root-graph edges are not adjacent in the line graph, then
no vertex is incident with both, so their Gram entry is `0`. -/
theorem edgeIncMatrix_transpose_mul_apply_of_not_lineGraph_adj
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {e f : G.edgeSet} (hef : e ≠ f) (h : ¬G.lineGraph.Adj e f) :
    ((edgeIncMatrix ℝ G).transpose * edgeIncMatrix ℝ G) e f = 0 := by
  classical
  change (∑ w : V, G.incMatrix ℝ w e.1 * G.incMatrix ℝ w f.1) = 0
  apply Finset.sum_eq_zero
  intro w hw
  by_cases hwe : w ∈ (e.1 : Sym2 V)
  · have hwf : w ∉ (f.1 : Sym2 V) := by
      intro hwf
      have hadj : G.lineGraph.Adj e f :=
        (_root_.SimpleGraph.lineGraph_adj_iff_exists).2 ⟨hef, w, hwe, hwf⟩
      exact h hadj
    have heInc : e.1 ∈ G.incidenceSet w :=
      (_root_.SimpleGraph.edge_mem_incidenceSet_iff G).2 hwe
    have hfNot : f.1 ∉ G.incidenceSet w := by
      simpa [_root_.SimpleGraph.edge_mem_incidenceSet_iff] using hwf
    rw [_root_.SimpleGraph.incMatrix_of_mem_incidenceSet G heInc,
      _root_.SimpleGraph.incMatrix_of_notMem_incidenceSet G hfNot]
    simp
  · have heNot : e.1 ∉ G.incidenceSet w := by
      simpa [_root_.SimpleGraph.edge_mem_incidenceSet_iff] using hwe
    rw [_root_.SimpleGraph.incMatrix_of_notMem_incidenceSet G heNot]
    simp

/-- The complementary-incidence Gram identity:
`NᵀN = A(L(G)) + 2I`, for the edge-indexed unsigned incidence matrix. -/
theorem edgeIncMatrix_transpose_mul_eq_lineGraphAdj_add_two
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel G.lineGraph.Adj] :
    (edgeIncMatrix ℝ G).transpose * edgeIncMatrix ℝ G =
      G.lineGraph.adjMatrix ℝ + (2 : ℝ) • (1 : Matrix G.edgeSet G.edgeSet ℝ) := by
  ext e f
  by_cases hef : e = f
  · subst f
    rw [edgeIncMatrix_transpose_mul_diag]
    simp
  · by_cases hadj : G.lineGraph.Adj e f
    · rw [edgeIncMatrix_transpose_mul_apply_of_lineGraph_adj G hadj]
      simp [hef, hadj, _root_.SimpleGraph.adjMatrix]
    · rw [edgeIncMatrix_transpose_mul_apply_of_not_lineGraph_adj G hef hadj]
      simp [hef, hadj, _root_.SimpleGraph.adjMatrix]

end GraphMatrix
end SpectralGraph
