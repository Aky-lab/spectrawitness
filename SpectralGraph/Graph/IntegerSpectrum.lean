import SpectralGraph.Certificate.IntegerSpectralInterval
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

/-! # Direct graph eigenvalue certificates using normalized integer arithmetic -/

namespace SpectralGraph.Graph
open SpectralGraph.Certificate
variable {n : Nat}

/-- Canonical dense integer adjacency storage, with no external array to validate. -/
def integerAdjacency (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : DenseIntMatrix :=
  DenseIntMatrix.ofFn n fun i j ↦
    if hi : i < n then if hj : j < n then
      if G.Adj ⟨i, hi⟩ ⟨j, hj⟩ then 1 else 0
    else 0 else 0

/-- Integer storage agrees exactly with the real adjacency matrix. -/
theorem integerAdjacency_cast (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ratCastMatrix (integerAdjacency G).toRatMatrix = G.adjMatrix ℝ := by
  refine Matrix.ext fun (i : Fin n) (j : Fin n) ↦ ?_
  change (((DenseIntMatrix.ofFn n _).entry i j : Int) : ℝ) = _
  rw [DenseIntMatrix.entry_ofFn n _ i j i.isLt j.isLt]
  by_cases h : G.Adj i j <;> simp [i.isLt, j.isLt, SimpleGraph.adjMatrix, h]

/-- Adjacency is Hermitian over the reals, supplied internally to spectral APIs. -/
theorem adjacency_isHermitian (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (G.adjMatrix ℝ).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simpa using (show (G.adjMatrix ℝ).IsSymm from G.isSymm_adjMatrix).apply i j

/-- Check adjacency inertia at a rational threshold using integer normalization. -/
def checkAdjacencyInertiaAt (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (t : ℚ) (target : Inertia) : Bool :=
  (integerAdjacency G).checkInertiaAt t target

theorem checkAdjacencyInertiaAt_sound (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (t : ℚ) (target : Inertia) (h : checkAdjacencyInertiaAt G t target = true) :
    matrixInertia (G.adjMatrix ℝ - (t : ℝ) • 1) = target := by
  have hi := (integerAdjacency G).checkInertiaAt_sound t target h
  rwa [integerAdjacency_cast] at hi

/-- Check the number of adjacency eigenvalues in `(a,b]`, counting multiplicity. -/
def checkAdjacencyEigenvaluesIoc (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b : ℚ) (left right : Inertia) (count : Nat) : Bool :=
  (integerAdjacency G).checkEigenvaluesIoc a b left right count

theorem checkAdjacencyEigenvaluesIoc_sound (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b : ℚ) (left right : Inertia) (count : Nat)
    (h : checkAdjacencyEigenvaluesIoc G a b left right count = true) :
    (Finset.univ.filter fun i ↦ (a : ℝ) < (adjacency_isHermitian G).eigenvalues i ∧
      (adjacency_isHermitian G).eigenvalues i ≤ (b : ℝ)).card = count := by
  have hc : a ≤ b ∧ checkAdjacencyInertiaAt G a left = true ∧
      checkAdjacencyInertiaAt G b right = true ∧ count + right.pos = left.pos := by
    simpa [checkAdjacencyEigenvaluesIoc, DenseIntMatrix.checkEigenvaluesIoc,
      checkAdjacencyInertiaAt, Bool.and_assoc] using h
  have hi := Inertia.eigenvalue_count_Ioc_add_pos_eq (G.adjMatrix ℝ) (adjacency_isHermitian G)
    (a : ℝ) (b : ℝ) (by exact_mod_cast hc.1)
  rw [checkAdjacencyInertiaAt_sound G a left hc.2.1,
    checkAdjacencyInertiaAt_sound G b right hc.2.2.1] at hi
  omega

/-- Check a bracket for a zero-based descending adjacency eigenvalue. -/
def checkAdjacencyEigenvalueBracket (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b : ℚ) (left right : Inertia) (k : Nat) : Bool :=
  (integerAdjacency G).checkEigenvalueBracket a b left right k

theorem checkAdjacencyEigenvalueBracket_sound (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b : ℚ) (left right : Inertia) (k : Fin (Fintype.card (Fin n)))
    (h : checkAdjacencyEigenvalueBracket G a b left right k.val = true) :
    (a : ℝ) < (adjacency_isHermitian G).eigenvalues₀ k ∧
      (adjacency_isHermitian G).eigenvalues₀ k ≤ (b : ℝ) := by
  have hc : k.val < n ∧ a ≤ b ∧ checkAdjacencyInertiaAt G a left = true ∧
      checkAdjacencyInertiaAt G b right = true ∧ (k.val < left.pos ∧ right.pos ≤ k.val) := by
    simpa [checkAdjacencyEigenvalueBracket, DenseIntMatrix.checkEigenvalueBracket,
      checkAdjacencyInertiaAt, integerAdjacency, DenseIntMatrix.ofFn, Bool.and_assoc] using h
  apply (Inertia.eigenvalues₀_mem_Ioc_iff _ (adjacency_isHermitian G) _ _ k).mpr
  rw [checkAdjacencyInertiaAt_sound G a left hc.2.2.1,
    checkAdjacencyInertiaAt_sound G b right hc.2.2.2.1]
  exact hc.2.2.2.2

end SpectralGraph.Graph
