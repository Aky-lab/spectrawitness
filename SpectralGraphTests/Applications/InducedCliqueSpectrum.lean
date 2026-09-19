import SpectralGraph.Graph.InducedSpectrum
import SpectralGraph.Certificate.SpectralInterval
import SpectralGraph.Inertia.NegativeSpectrum

/-!
# K4 induced-adjacency consumer

This is a concrete non-path use of the public induced-adjacency interface.
Deleting one vertex from `K4` has codimension one, while deleting two has
codimension two; the latter explicitly checks that the lower ambient index is
shifted by two.  These statements concern adjacency spectra, not induced
Laplacians (whose degrees change).
-/

namespace SpectralGraphTests.Applications.InducedCliqueSpectrum

open Matrix
open SpectralGraph
open SpectralGraph.Graph
open SpectralGraph.Certificate SpectralGraph.Inertia

abbrev K4 : SimpleGraph (Fin 4) := SimpleGraph.completeGraph (Fin 4)

def keepThree : Set (Fin 4) := {v | v ≠ 0}

instance keepThreeDecidable : DecidablePred (fun v : Fin 4 => v ∈ keepThree) := by
  intro v
  change Decidable (v ≠ 0)
  exact inferInstance

def keepTwo : Set (Fin 4) := {v | v ≠ 0 ∧ v ≠ 1}

instance keepTwoDecidable : DecidablePred (fun v : Fin 4 => v ∈ keepTwo) := by
  intro v
  change Decidable (v ≠ 0 ∧ v ≠ 1)
  exact inferInstance

def K4Rat : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, 1, 1, 1; 1, 0, 1, 1; 1, 1, 0, 1; 1, 1, 1, 0]

def K4AtNegOne : InertiaCertificate (Fin 4) where
  change := !![1, -1, -1, -1; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
  inverse := !![1, 1, 1, 1; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
  target := ⟨1, 3, 0⟩

theorem K4_adjMatrix_eq_ratCast : K4.adjMatrix ℝ = ratCastMatrix K4Rat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [K4, K4Rat, ratCastMatrix, SimpleGraph.adjMatrix_apply]

private theorem K4_shift_neg_one_inertia :
    matrixInertia (K4.adjMatrix ℝ - (-1 : ℝ) • 1) = ⟨1, 3, 0⟩ := by
  have h := K4AtNegOne.sound (K4Rat - (-1 : ℚ) • 1) (by decide +kernel)
  rw [ratCast_shift] at h
  rw [K4_adjMatrix_eq_ratCast]
  simpa [K4AtNegOne] using h

theorem K4_eigenvalue_one_eq_neg_one :
    (adjMatrix_isHermitian K4).eigenvalues₀ ⟨1, by decide⟩ = -1 := by
  have hi := K4_shift_neg_one_inertia
  apply le_antisymm
  · apply (eigenvalues₀_le_iff _ (adjMatrix_isHermitian K4) (-1)
      ⟨1, by decide⟩).mpr
    have hp := congrArg Inertia.pos hi
    norm_num at hp ⊢
    omega
  · apply (le_eigenvalues₀_iff _ (adjMatrix_isHermitian K4) (-1)
      ⟨1, by decide⟩).mpr
    calc
      (matrixInertia (K4.adjMatrix ℝ - (-1 : ℝ) • 1)).neg = 0 := by
        simpa using congrArg Inertia.neg hi
      _ < Fintype.card (Fin 4) - (⟨1, by decide⟩ : Fin 4).val := by decide

theorem K4_eigenvalue_three_eq_neg_one :
    (adjMatrix_isHermitian K4).eigenvalues₀ ⟨3, by decide⟩ = -1 := by
  have hi := K4_shift_neg_one_inertia
  apply le_antisymm
  · apply (eigenvalues₀_le_iff _ (adjMatrix_isHermitian K4) (-1)
      ⟨3, by decide⟩).mpr
    have hp := congrArg Inertia.pos hi
    norm_num at hp ⊢
    omega
  · apply (le_eigenvalues₀_iff _ (adjMatrix_isHermitian K4) (-1)
      ⟨3, by decide⟩).mpr
    calc
      (matrixInertia (K4.adjMatrix ℝ - (-1 : ℝ) • 1)).neg = 0 := by
        simpa using congrArg Inertia.neg hi
      _ < Fintype.card (Fin 4) - (⟨3, by decide⟩ : Fin 4).val := by decide

example :
    (K4.induce keepThree).adjMatrix ℝ =
      (K4.adjMatrix ℝ).submatrix (inducedVertexEmbedding keepThree)
        (inducedVertexEmbedding keepThree) := by
  classical
  exact induced_adjMatrix_eq_submatrix K4 keepThree

example :
    (K4.induce keepTwo).adjMatrix ℝ =
      (K4.adjMatrix ℝ).submatrix (inducedVertexEmbedding keepTwo)
        (inducedVertexEmbedding keepTwo) := by
  classical
  exact induced_adjMatrix_eq_submatrix K4 keepTwo

theorem K4_delete_one_interlaces (k : Fin (Fintype.card {v : Fin 4 // v ∈ keepThree})) :
    (adjMatrix_isHermitian K4).eigenvalues₀ ⟨k.val + 1, by
      have hk := k.isLt
      have hcard : Fintype.card {v : Fin 4 // v ∈ keepThree} = 3 := by decide
      norm_num at ⊢
      omega⟩ ≤
        (induced_adjMatrix_isHermitian K4 keepThree).eigenvalues₀ k ∧
      (induced_adjMatrix_isHermitian K4 keepThree).eigenvalues₀ k ≤
        (adjMatrix_isHermitian K4).eigenvalues₀ ⟨k.val, by
          have hk := k.isLt
          have hcard : Fintype.card {v : Fin 4 // v ∈ keepThree} = 3 := by decide
          norm_num at ⊢
          omega⟩ := by
  classical
  simpa only [show Fintype.card {v : Fin 4 // v ∈ keepThree} = 3 by decide,
    Fintype.card_fin, Nat.reduceSub] using
    (inducedAdjacencySpectrumInterlaces K4 keepThree k)

theorem K4_delete_two_interlaces (k : Fin (Fintype.card {v : Fin 4 // v ∈ keepTwo})) :
    (adjMatrix_isHermitian K4).eigenvalues₀ ⟨k.val + 2, by
      have hk := k.isLt
      have hcard : Fintype.card {v : Fin 4 // v ∈ keepTwo} = 2 := by decide
      norm_num at ⊢
      omega⟩ ≤
        (induced_adjMatrix_isHermitian K4 keepTwo).eigenvalues₀ k ∧
      (induced_adjMatrix_isHermitian K4 keepTwo).eigenvalues₀ k ≤
        (adjMatrix_isHermitian K4).eigenvalues₀ ⟨k.val, by
          have hk := k.isLt
          have hcard : Fintype.card {v : Fin 4 // v ∈ keepTwo} = 2 := by decide
          norm_num at ⊢
          omega⟩ := by
  classical
  simpa only [show Fintype.card {v : Fin 4 // v ∈ keepTwo} = 2 by decide,
    Fintype.card_fin, Nat.reduceSub] using
    (inducedAdjacencySpectrumInterlaces K4 keepTwo k)

-- This elaboration check intentionally supplies only the graph, retained set,
-- and retained index; codimension and ambient endpoint proofs stay internal.
example {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (T : Set W) [DecidablePred (· ∈ T)]
    [DecidableRel H.Adj] [DecidableRel (H.induce T).Adj]
    (j : Fin (Fintype.card {v : W // v ∈ T})) : True := by
  have h := inducedAdjacencySpectrumInterlaces H T j
  clear h
  trivial

-- For an empty ambient graph the retained type is also empty.  The indexed
-- interface is therefore vacuous: its call compiles under a bound variable,
-- without manufacturing a value of `Fin 0`.
example (H : SimpleGraph Empty) (T : Set Empty) [DecidablePred (· ∈ T)]
    [DecidableRel H.Adj] [DecidableRel (H.induce T).Adj] :
    ∀ _j : Fin (Fintype.card {v : Empty // v ∈ T}), True := by
  intro j
  have h := inducedAdjacencySpectrumInterlaces H T j
  clear h
  have hj := j.isLt
  have hcard : Fintype.card {v : Empty // v ∈ T} = 0 := by
    rw [Fintype.card_eq_zero]
  omega

/-- Deleting two vertices retains the repeated `-1` adjacency eigenvalue.
This is a concrete spectral conclusion, squeezed between the exact equal K4
endpoints at descending indices `1` and `3`. -/
theorem K4_delete_two_second_eigenvalue_eq_neg_one :
    (induced_adjMatrix_isHermitian K4 keepTwo).eigenvalues₀
      ⟨1, by decide⟩ = -1 := by
  have h := inducedAdjacencySpectrumInterlaces K4 keepTwo ⟨1, by decide⟩
  simp only [show Fintype.card {v : Fin 4 // v ∈ keepTwo} = 2 by decide,
    Fintype.card_fin, Nat.reduceSub] at h
  rw [K4_eigenvalue_three_eq_neg_one, K4_eigenvalue_one_eq_neg_one] at h
  linarith

#print axioms K4_delete_two_second_eigenvalue_eq_neg_one

end SpectralGraphTests.Applications.InducedCliqueSpectrum
