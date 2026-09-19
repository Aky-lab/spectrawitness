import SpectralGraph.Graph.PartitionSpectrum
import SpectralGraph.Inertia.InvariantSpectrum

/-!
# Equitable cell maps and adjacency eigenvalues

Equitability is an additional neighbour-count hypothesis on a vertex cell
map.  It identifies an invariant subspace of the adjacency matrix and hence
lifts eigenpairs of the supplied (possibly nonsymmetric) count matrix to
actual adjacency eigenvalues.
-/

namespace SpectralGraph.Graph

open Matrix SpectralGraph.Inertia

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

/-- A cell map is equitable for `Q` when every vertex has `Q (p v) c`
neighbours in cell `c`.  The supplied count matrix need not be symmetric. -/
def IsEquitable (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → C) (Q : Matrix C C ℝ) : Prop :=
  ∀ v c, ((Finset.univ.filter fun w ↦ G.Adj v w ∧ p w = c).card : ℝ) =
    Q (p v) c

omit [DecidableEq V] [Fintype C] in
/-- Multiplying adjacency by a cell-indicator column counts neighbours in
that cell. -/
theorem adjMatrix_mul_cellIndicator_apply
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → C) (v : V) (c : C) :
    (G.adjMatrix ℝ * cellIndicator p) v c =
      ((Finset.univ.filter fun w ↦ G.Adj v w ∧ p w = c).card : ℝ) := by
  simp [Matrix.mul_apply, SimpleGraph.adjMatrix_apply, cellIndicator,
    ← ite_and, and_comm]

omit [DecidableEq V] in
/-- Equitable neighbour counts are exactly the entrywise data needed for the
indicator-column space to be adjacency invariant. -/
theorem IsEquitable.adjMatrix_mul_cellIndicator
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → C) (Q : Matrix C C ℝ)
    (hEquitable : IsEquitable G p Q) :
    G.adjMatrix ℝ * cellIndicator p = cellIndicator p * Q := by
  ext v c
  rw [adjMatrix_mul_cellIndicator_apply, hEquitable v c]
  simp [Matrix.mul_apply, cellIndicator]

/-- A nonzero eigenpair of an equitable count matrix lifts to an occurrence
in the actual ordered adjacency spectrum. -/
theorem eigenvalues₀_eq_of_equitable_eigenpair
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → C)
    (hp : Function.Surjective p) (Q : Matrix C C ℝ)
    (hEquitable : IsEquitable G p Q) (t : ℝ) (x : C → ℝ) (hx : x ≠ 0)
    (hQx : Q *ᵥ x = t • x) :
    ∃ k : Fin (Fintype.card V),
      (adjMatrix_isHermitian G).eigenvalues₀ k = t := by
  exact eigenvalues₀_eq_of_invariant_eigenpair
    (G.adjMatrix ℝ) (adjMatrix_isHermitian G) (cellIndicator p) Q
    (cellIndicator_mulVecLin_injective p hp)
    (hEquitable.adjMatrix_mul_cellIndicator G p Q) t x hx hQx

end SpectralGraph.Graph
