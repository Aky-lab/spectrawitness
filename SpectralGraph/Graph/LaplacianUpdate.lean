import SpectralGraph.Inertia.RankOneSpectrum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.Operations

/-!
# Laplacian conductance updates

An added conductance on `u-v` is represented by the rank-one matrix formed
from the signed endpoint vector.  The coefficient is algebraic (and may be
any real); nonnegative coefficients have the usual conductance meaning.
-/

namespace SpectralGraph.Graph

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The signed incidence vector of the ordered endpoints.  In particular it
is zero when the endpoints coincide. -/
def edgeVector (u v : V) : V → ℝ := Pi.single u 1 - Pi.single v 1

/-- The Laplacian of `G` with extra conductance `w` on `u-v`. -/
def laplacianUpdate (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) (w : ℝ) : Matrix V V ℝ :=
  G.lapMatrix ℝ + w • vecMulVec (edgeVector u v) (edgeVector u v)

theorem edgeVector_self (u : V) : edgeVector u u = 0 := by
  simp [edgeVector]

theorem edgeVector_apply (u v x : V) : edgeVector u v x =
    (if x = u then 1 else 0) - if x = v then 1 else 0 := by
  simp [edgeVector, Pi.single_apply]

theorem edgeVector_outer_isHermitian (u v : V) :
    (vecMulVec (edgeVector u v) (edgeVector u v)).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simp [vecMulVec_apply, mul_comm]

theorem laplacianUpdate_isHermitian (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) (w : ℝ) : (laplacianUpdate G u v w).IsHermitian := by
  exact (G.isHermitian_lapMatrix (R := ℝ)).add
    ((edgeVector_outer_isHermitian u v).smul (IsSelfAdjoint.all w))

/-- Entrywise endpoint semantics of a nonloop conductance update: add `w` on
the endpoint diagonals and subtract `w` on the two cross entries. -/
theorem laplacianUpdate_endpoints (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (huv : u ≠ v) (w : ℝ) :
    laplacianUpdate G u v w u u = G.lapMatrix ℝ u u + w ∧
      laplacianUpdate G u v w v v = G.lapMatrix ℝ v v + w ∧
      laplacianUpdate G u v w u v = G.lapMatrix ℝ u v - w ∧
      laplacianUpdate G u v w v u = G.lapMatrix ℝ v u - w := by
  simp [laplacianUpdate, edgeVector_apply, Matrix.vecMulVec_apply,
    huv, huv.symm, sub_eq_add_neg]

/-- Every entry outside the two-by-two endpoint block is unchanged. -/
theorem laplacianUpdate_apply_of_outside (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v x y : V) (h : (x ≠ u ∧ x ≠ v) ∨ (y ≠ u ∧ y ≠ v)) (w : ℝ) :
    laplacianUpdate G u v w x y = G.lapMatrix ℝ x y := by
  rcases h with hx | hy
  · simp [laplacianUpdate, edgeVector_apply, Matrix.vecMulVec_apply, hx]
  · simp [laplacianUpdate, edgeVector_apply, Matrix.vecMulVec_apply, hy]

/-- Increasing edge conductance weakly increases each descending ordered
eigenvalue.  Algebraically the coefficients may be any ordered reals. -/
theorem laplacianUpdate_eigenvalues₀_mono
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V)
    {a b : ℝ} (hab : a ≤ b) (k : Fin (Fintype.card V)) :
    (laplacianUpdate_isHermitian G u v a).eigenvalues₀ k ≤
      (laplacianUpdate_isHermitian G u v b).eigenvalues₀ k := by
  exact Inertia.eigenvalues₀_rankOne_mono (G.lapMatrix ℝ)
    (G.isHermitian_lapMatrix (R := ℝ)) (edgeVector u v) hab k

/-- A conductance increase moves an eigenvalue by at most one position in the
descending list. -/
theorem laplacianUpdate_eigenvalues₀_succ_le
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V)
    {a b : ℝ} (hab : a ≤ b) (k : Fin (Fintype.card V))
    (hk : k.val + 1 < Fintype.card V) :
    (laplacianUpdate_isHermitian G u v b).eigenvalues₀ ⟨k.val + 1, hk⟩ ≤
      (laplacianUpdate_isHermitian G u v a).eigenvalues₀ k := by
  exact Inertia.eigenvalues₀_rankOne_succ_le (G.lapMatrix ℝ)
    (G.isHermitian_lapMatrix (R := ℝ)) (edgeVector u v) hab k hk

private theorem degree_sup_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v x : V} (huv : u ≠ v) (hG : ¬ G.Adj u v) :
    ((G ⊔ SimpleGraph.edge u v).degree x : ℝ) =
      (G.degree x : ℝ) + (if x = u ∨ x = v then 1 else 0) := by
  classical
  by_cases hx : x = u
  · subst x
    have hset : (G ⊔ SimpleGraph.edge u v).neighborFinset u =
        insert v (G.neighborFinset u) := by
      ext j
      simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.sup_adj,
        SimpleGraph.edge_adj, Finset.mem_insert]
      aesop
    have hnot : v ∉ G.neighborFinset u := by
      simpa only [SimpleGraph.mem_neighborFinset] using hG
    simp only [SimpleGraph.degree, hset, Finset.card_insert_of_notMem hnot,
      Nat.cast_add, Nat.cast_one]
    simp [huv]
  · by_cases hxv : x = v
    · subst x
      have hG' : ¬ G.Adj v u := by simpa [SimpleGraph.adj_comm] using hG
      have hset : (G ⊔ SimpleGraph.edge u v).neighborFinset v =
          insert u (G.neighborFinset v) := by
        ext j
        simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.sup_adj,
          SimpleGraph.edge_adj, Finset.mem_insert]
        aesop
      have hnot : u ∉ G.neighborFinset v := by
        simpa only [SimpleGraph.mem_neighborFinset] using hG'
      simp only [SimpleGraph.degree, hset, Finset.card_insert_of_notMem hnot,
        Nat.cast_add, Nat.cast_one]
      simp [huv]
    · have hset : (G ⊔ SimpleGraph.edge u v).neighborFinset x =
          G.neighborFinset x := by
        ext j
        simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.sup_adj,
          SimpleGraph.edge_adj]
        simp [hx, hxv]
      simp only [SimpleGraph.degree, hset]
      simp only [hx, hxv, false_or, ite_false, add_zero]

/-- Adding a missing nonloop edge is precisely a unit conductance update of
the real Laplacian. -/
theorem laplacianUpdate_one_eq_sup_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (huv : u ≠ v) (hG : ¬ G.Adj u v) :
    laplacianUpdate G u v 1 = (G ⊔ SimpleGraph.edge u v).lapMatrix ℝ := by
  have hGsymm : ¬ G.Adj v u := by simpa [SimpleGraph.adj_comm] using hG
  ext x y
  simp only [laplacianUpdate, SimpleGraph.lapMatrix, Matrix.add_apply,
    Matrix.smul_apply, one_mul, Matrix.sub_apply, Matrix.vecMulVec_apply]
  by_cases hx : x = u
  · subst x
    by_cases hy : y = u
    · subst y
      simp [SimpleGraph.degMatrix, SimpleGraph.adjMatrix_apply,
        degree_sup_edge G huv hG, edgeVector_apply,
        SimpleGraph.sup_adj, SimpleGraph.edge_adj, huv, hG]
    · by_cases hyv : y = v
      · subst y
        simp [SimpleGraph.degMatrix, SimpleGraph.adjMatrix_apply,
          edgeVector_apply, SimpleGraph.sup_adj, SimpleGraph.edge_adj,
          huv, huv.symm, hG]
      · have huy : u ≠ y := fun h => hy h.symm
        simp [SimpleGraph.degMatrix, SimpleGraph.adjMatrix_apply,
          Matrix.diagonal_apply, edgeVector_apply, SimpleGraph.sup_adj,
          SimpleGraph.edge_adj, huv, hG, hy, hyv, huy]
  · by_cases hxv : x = v
    · subst x
      by_cases hy : y = u
      · subst y
        simp [SimpleGraph.degMatrix, SimpleGraph.adjMatrix_apply,
          edgeVector_apply, SimpleGraph.sup_adj, SimpleGraph.edge_adj,
          huv, huv.symm, hGsymm]
      · by_cases hyv : y = v
        · subst y
          simp [SimpleGraph.degMatrix, SimpleGraph.adjMatrix_apply,
            degree_sup_edge G huv hG, edgeVector_apply,
            SimpleGraph.sup_adj, SimpleGraph.edge_adj, huv, huv.symm, hGsymm]
        · have hvy : v ≠ y := fun h => hyv h.symm
          simp [SimpleGraph.degMatrix, SimpleGraph.adjMatrix_apply,
            Matrix.diagonal_apply, edgeVector_apply, SimpleGraph.sup_adj,
            SimpleGraph.edge_adj, huv, huv.symm, hGsymm, hy, hyv, hvy]
    · by_cases hy : y = u
      · subst y
        simp [SimpleGraph.degMatrix, SimpleGraph.adjMatrix_apply,
          edgeVector_apply, SimpleGraph.sup_adj, SimpleGraph.edge_adj,
          huv, hG, hx, hxv]
      · by_cases hyv : y = v
        · subst y
          simp [SimpleGraph.degMatrix, SimpleGraph.adjMatrix_apply,
            edgeVector_apply, SimpleGraph.sup_adj, SimpleGraph.edge_adj,
            huv, hGsymm, hx, hxv]
        · have hux : u ≠ x := fun h => hx h.symm
          have hvx : v ≠ x := fun h => hxv h.symm
          simp [SimpleGraph.degMatrix, SimpleGraph.adjMatrix_apply,
            Matrix.diagonal_apply, degree_sup_edge G huv hG,
            edgeVector_apply, SimpleGraph.sup_adj, SimpleGraph.edge_adj,
            huv, hx, hxv, hy, hyv, hux, hvx]

end SpectralGraph.Graph
