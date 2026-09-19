import SpectralGraph.Graph.LineGraph
import SpectralGraph.Inertia.Congruence
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! Bipartite adjacency inertia symmetry and vanishing signature. -/
namespace SpectralGraph.Graph
open SpectralGraph.Inertia Matrix
open scoped SimpleGraph
universe u

/-- Exact bipartite spectral symmetry: negating the adjacency matrix swaps
its positive and negative inertia indices, while a diagonal sign congruence
shows that the negated matrix has the same inertia. -/
theorem adjMatrix_inertia_swap_of_isBipartiteWith
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : Set V) [DecidablePred (· ∈ s)]
    (h : G.IsBipartiteWith s t) :
    matrixInertia (G.adjMatrix ℝ) =
      { pos := (matrixInertia (G.adjMatrix ℝ)).neg
        zero := (matrixInertia (G.adjMatrix ℝ)).zero
        neg := (matrixInertia (G.adjMatrix ℝ)).pos } := by
  let sign : V → ℝ := fun v ↦ if v ∈ s then 1 else -1
  let P : Matrix V V ℝ := Matrix.diagonal sign
  have hsign (v w : V) (hvw : G.Adj v w) : sign v * sign w = -1 := by
    rcases h.mem_of_adj hvw with hst | hts
    · have hwt : w ∉ s := fun hws ↦
        Set.disjoint_left.mp h.disjoint hws hst.2
      simp [sign, hst.1, hwt]
    · have hvt : v ∉ s := fun hvs ↦
        Set.disjoint_left.mp h.disjoint hvs hts.1
      simp [sign, hvt, hts.2]
  have hPmul : P * P = 1 := by
    simp only [P, Matrix.diagonal_mul_diagonal]
    ext v w
    by_cases hvw : v = w
    · subst w
      by_cases hv : v ∈ s <;> simp [sign, hv]
    · simp [hvw]
  letI : Invertible P := invertibleOfLeftInverse P P hPmul
  have hcongr : -(G.adjMatrix ℝ) = P.transpose * G.adjMatrix ℝ * P := by
    ext v w
    simp only [P, Matrix.diagonal_transpose, Matrix.diagonal_mul,
      Matrix.mul_diagonal]
    by_cases hvw : G.Adj v w
    · have hs := hsign v w hvw
      simp only [Matrix.neg_apply, SimpleGraph.adjMatrix_apply, hvw,
        ↓reduceIte, mul_one]
      exact hs.symm
    · simp [SimpleGraph.adjMatrix_apply, hvw]
  have hiner := matrixInertia_eq_of_congr
    (G.adjMatrix ℝ) (-(G.adjMatrix ℝ)) P hcongr
  rw [matrixInertia_neg] at hiner
  exact hiner

/-- A bipartite graph has adjacency signature zero. -/
theorem graphSignature_eq_zero_of_isBipartiteWith
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : Set V) [DecidablePred (· ∈ s)]
    (h : G.IsBipartiteWith s t) :
    graphSignature G = 0 := by
  have hiner := adjMatrix_inertia_swap_of_isBipartiteWith G s t h
  have hp := congrArg Inertia.pos hiner
  simp only at hp
  simp only [graphSignature, matrixSignature, Inertia.signature]
  omega

/-- Type-independent exact inertia symmetry for a finite bipartite graph. -/
theorem adjMatrix_inertia_swap_of_isBipartite
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsBipartite) :
    matrixInertia (G.adjMatrix ℝ) =
      { pos := (matrixInertia (G.adjMatrix ℝ)).neg
        zero := (matrixInertia (G.adjMatrix ℝ)).zero
        neg := (matrixInertia (G.adjMatrix ℝ)).pos } := by
  classical
  obtain ⟨s, t, hst⟩ := h.exists_isBipartiteWith
  exact adjMatrix_inertia_swap_of_isBipartiteWith G s t hst

/-- A finite bipartite graph has adjacency signature zero. -/
theorem graphSignature_eq_zero_of_isBipartite
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsBipartite) :
    graphSignature G = 0 := by
  classical
  obtain ⟨s, t, hst⟩ := h.exists_isBipartiteWith
  exact graphSignature_eq_zero_of_isBipartiteWith G s t hst


/-- Positive and negative adjacency indices of a finite bipartite graph agree. -/
theorem adjMatrix_pos_eq_neg_of_isBipartite
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : G.IsBipartite) :
    (matrixInertia (G.adjMatrix ℝ)).pos = (matrixInertia (G.adjMatrix ℝ)).neg :=
  congrArg SpectralGraph.Inertia.pos (adjMatrix_inertia_swap_of_isBipartite G h)

end SpectralGraph.Graph

