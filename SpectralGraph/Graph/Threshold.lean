import SpectralGraph.Certificate.Basic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

/-!
# Exact adjacency inertia at rational thresholds

Certifying `A(G) - t I` gives the positive, zero and negative indices relative
to any rational threshold `t`. The semantic target is the real shifted
adjacency matrix, so clients do not need to manage casts themselves.
-/

namespace SpectralGraph.Graph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Rational adjacency matrix shifted by an arbitrary rational threshold. -/
def adjacencyShift (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℚ) :
    Matrix V V ℚ := G.adjMatrix ℚ - t • (1 : Matrix V V ℚ)

omit [Fintype V] in
/-- Exact rational and real shifted adjacency matrices agree. -/
theorem adjacencyShift_cast (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℚ) :
    Certificate.ratCastMatrix (adjacencyShift G t) =
      G.adjMatrix ℝ - (t : ℝ) • (1 : Matrix V V ℝ) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Certificate.ratCastMatrix, adjacencyShift, SimpleGraph.adjMatrix]
  · by_cases h : G.Adj i j <;>
      simp [Certificate.ratCastMatrix, adjacencyShift, SimpleGraph.adjMatrix, hij, h]

/-- A portable certificate proves the real inertia at the chosen threshold. -/
theorem inertia_at_threshold (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : ℚ) (c : Certificate.InertiaCertificate V)
    (h : c.check (adjacencyShift G t) = true) :
    matrixInertia (G.adjMatrix ℝ - (t : ℝ) • (1 : Matrix V V ℝ)) = c.target := by
  rw [← adjacencyShift_cast G t]
  exact c.sound _ h

end SpectralGraph.Graph
