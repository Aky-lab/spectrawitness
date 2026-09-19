import SpectralGraph.Graph.LaplacianUpdate
import Mathlib.Combinatorics.SimpleGraph.Circulant

/-!
# A diagonal conductance update of the four-cycle

The edge `0-2` is absent from `C4`, so unit conductance is exactly insertion
of the ordinary diagonal edge.  Other real coefficients retain the algebraic
rank-one meaning; nonnegative coefficients are conductance additions.
-/

namespace SpectralGraphTests.Applications.CycleLaplacianUpdate

open Matrix SpectralGraph SpectralGraph.Graph

abbrev C4 : SimpleGraph (Fin 4) := SimpleGraph.cycleGraph 4

theorem diagonal_ne : (0 : Fin 4) ≠ 2 := by decide
theorem diagonal_not_adj : ¬ C4.Adj 0 2 := by decide

/-- Weight one is bound to an actual simple graph, not an untrusted dense
matrix. -/
theorem weightOne_eq_inserted_diagonal :
    laplacianUpdate C4 0 2 1 =
      (C4 ⊔ SimpleGraph.edge 0 2).lapMatrix ℝ :=
  laplacianUpdate_one_eq_sup_edge C4 diagonal_ne diagonal_not_adj

theorem arbitrary_conductance_mono (a b : ℝ) (hab : a ≤ b) (k : Fin 4) :
    (laplacianUpdate_isHermitian C4 0 2 a).eigenvalues₀ k ≤
      (laplacianUpdate_isHermitian C4 0 2 b).eigenvalues₀ k :=
  laplacianUpdate_eigenvalues₀_mono C4 0 2 hab k

theorem arbitrary_conductance_succ (a b : ℝ) (hab : a ≤ b)
    (k : Fin 4) (hk : k.val + 1 < 4) :
    (laplacianUpdate_isHermitian C4 0 2 b).eigenvalues₀
        ⟨k.val + 1, hk⟩ ≤
      (laplacianUpdate_isHermitian C4 0 2 a).eigenvalues₀ k :=
  laplacianUpdate_eigenvalues₀_succ_le C4 0 2 hab k hk

-- Weight zero and a nonintegral rational conductance use the public theorem.
example (k : Fin 4) :
    (laplacianUpdate_isHermitian C4 0 2 0).eigenvalues₀ k ≤
      (laplacianUpdate_isHermitian C4 0 2 (1 / 3)).eigenvalues₀ k := by
  exact arbitrary_conductance_mono 0 (1 / 3) (by norm_num) k

example : laplacianUpdate C4 0 2 0 = C4.lapMatrix ℝ := by
  simp [laplacianUpdate]

-- Coincident endpoints give the zero vector and hence no update at any weight.
example (w : ℝ) : laplacianUpdate C4 0 0 w = C4.lapMatrix ℝ := by
  simp [laplacianUpdate, edgeVector_self]

-- The endpoint block has the documented `+w,+w,-w,-w` entries.
example (w : ℝ) :
    laplacianUpdate C4 0 2 w 0 0 = C4.lapMatrix ℝ 0 0 + w ∧
      laplacianUpdate C4 0 2 w 2 2 = C4.lapMatrix ℝ 2 2 + w ∧
      laplacianUpdate C4 0 2 w 0 2 = C4.lapMatrix ℝ 0 2 - w ∧
      laplacianUpdate C4 0 2 w 2 0 = C4.lapMatrix ℝ 2 0 - w :=
  laplacianUpdate_endpoints C4 diagonal_ne w

/-! An already-present edge is different: union is idempotent, while another
unit of conductance changes the endpoint diagonal.  This prevents accidental
removal of the nonedge hypothesis from the graph identity. -/
theorem existingEdge_update_ne_union :
    laplacianUpdate C4 0 1 1 ≠
      (C4 ⊔ SimpleGraph.edge 0 1).lapMatrix ℝ := by
  have hadj : C4.Adj 0 1 := by decide
  have hsup : C4 ⊔ SimpleGraph.edge 0 1 = C4 :=
    SimpleGraph.sup_edge_of_adj C4 hadj
  have hdeg (i : Fin 4) :
      ((C4 ⊔ SimpleGraph.edge 0 1).degree i : ℝ) = (C4.degree i : ℝ) := by
    rw [(C4 ⊔ SimpleGraph.edge 0 1).degree_eq_sum_if_adj (R := ℝ) i,
      C4.degree_eq_sum_if_adj (R := ℝ) i]
    simp only [hsup]
  have hlap : (C4 ⊔ SimpleGraph.edge 0 1).lapMatrix ℝ = C4.lapMatrix ℝ := by
    ext i j
    simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
      Matrix.sub_apply, Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply,
      hsup, hdeg]
  intro h
  have hentry := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 0) h
  rw [hlap] at hentry
  have hu := (laplacianUpdate_endpoints C4 (by decide : (0 : Fin 4) ≠ 1) 1).1
  linarith

#print axioms weightOne_eq_inserted_diagonal
#print axioms arbitrary_conductance_mono
#print axioms existingEdge_update_ne_union

end SpectralGraphTests.Applications.CycleLaplacianUpdate
