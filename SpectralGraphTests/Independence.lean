import SpectralGraph.Graph.Independence
import SpectralGraphTests.Applications.SignedC4Independence

namespace SpectralGraphTests.Independence

open Matrix SpectralGraph SpectralGraph.Graph SpectralGraph.Inertia
open SpectralGraphTests.Applications.SignedC4Independence

/-! Boundary checks for support, finite-type generality, and independence. -/

def edgelessBool : SimpleGraph Bool := ⊥
instance : DecidableRel edgelessBool.Adj := by unfold edgelessBool; infer_instance

theorem edgelessBool_indepNum : edgelessBool.indepNum = 2 := by
  have hz : matrixInertia (0 : Matrix Bool Bool ℝ) = ⟨0, 2, 0⟩ := by
    have hdiag : (0 : Matrix Bool Bool ℝ) = Matrix.diagonal (fun _ : Bool ↦ (0 : ℝ)) := by
      ext i j
      simp [Matrix.diagonal_apply]
    rw [hdiag, matrixInertia_diagonal]
    norm_num
  have hu := indepNum_le_inertia_of_supported edgelessBool
    (0 : Matrix Bool Bool ℝ) (by intro u v h; rfl)
  have hu' : edgelessBool.indepNum ≤ 2 := by simpa [hz] using hu
  have hs : edgelessBool.IsIndepSet (↑(Finset.univ : Finset Bool) : Set Bool) := by
    decide +kernel
  have hl := hs.card_le_indepNum
  norm_num at hl
  exact Nat.le_antisymm hu' hl

theorem edgelessFin3_indepNum : (⊥ : SimpleGraph (Fin 3)).indepNum = 3 := by
  have hz : matrixInertia (0 : Matrix (Fin 3) (Fin 3) ℝ) = ⟨0, 3, 0⟩ := by
    have hdiag : (0 : Matrix (Fin 3) (Fin 3) ℝ) =
        Matrix.diagonal (fun _ : Fin 3 ↦ (0 : ℝ)) := by
      ext i j
      simp [Matrix.diagonal_apply]
    rw [hdiag, matrixInertia_diagonal]
    norm_num
  have hu := indepNum_le_inertia_of_supported (⊥ : SimpleGraph (Fin 3))
    (0 : Matrix (Fin 3) (Fin 3) ℝ) (by intro u v h; rfl)
  have hu' : (⊥ : SimpleGraph (Fin 3)).indepNum ≤ 3 := by simpa [hz] using hu
  have hs : (⊥ : SimpleGraph (Fin 3)).IsIndepSet
      (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) := by decide +kernel
  have hl := hs.card_le_indepNum
  norm_num at hl
  exact Nat.le_antisymm hu' hl

example : (⊥ : SimpleGraph (Fin 0)).indepNum = 0 := by
  have hz : matrixInertia (0 : Matrix (Fin 0) (Fin 0) ℝ) = ⟨0, 0, 0⟩ := by
    have hdiag : (0 : Matrix (Fin 0) (Fin 0) ℝ) =
        Matrix.diagonal (fun _ : Fin 0 ↦ (0 : ℝ)) := by
      ext i j
      simp [Matrix.diagonal_apply]
    rw [hdiag, matrixInertia_diagonal]
    norm_num
  have hu := indepNum_le_inertia_of_supported (⊥ : SimpleGraph (Fin 0))
    (0 : Matrix (Fin 0) (Fin 0) ℝ) (by intro u v h; rfl)
  have hu' : (⊥ : SimpleGraph (Fin 0)).indepNum ≤ 0 := by simpa [hz] using hu
  omega

example : (∅ : Finset (Fin 0)).card ≤
    (matrixInertia (0 : Matrix (Fin 0) (Fin 0) ℝ)).zero +
      min (matrixInertia (0 : Matrix (Fin 0) (Fin 0) ℝ)).pos
        (matrixInertia (0 : Matrix (Fin 0) (Fin 0) ℝ)).neg := by
  apply indepSet_card_le_inertia_of_supported (⊥ : SimpleGraph (Fin 0)) 0
  · intro u v h
    rfl
  · decide +kernel

example : ({0} : Finset (Fin 1)).card ≤
    (matrixInertia (0 : Matrix (Fin 1) (Fin 1) ℝ)).zero +
      min (matrixInertia (0 : Matrix (Fin 1) (Fin 1) ℝ)).pos
        (matrixInertia (0 : Matrix (Fin 1) (Fin 1) ℝ)).neg := by
  apply indepSet_card_le_inertia_of_supported (⊥ : SimpleGraph (Fin 1)) 0
  · intro u v h
    rfl
  · decide +kernel

example : ({false, true} : Finset Bool).card ≤
    (matrixInertia (0 : Matrix Bool Bool ℝ)).zero +
      min (matrixInertia (0 : Matrix Bool Bool ℝ)).pos
        (matrixInertia (0 : Matrix Bool Bool ℝ)).neg := by
  apply indepSet_card_le_inertia_of_supported edgelessBool
    (0 : Matrix Bool Bool ℝ)
  · intro u v h
    rfl
  · decide +kernel

-- Diagonal entries are part of support: an identity matrix is not supported
-- on a nonempty edgeless graph, despite vanishing off the diagonal.
example : ¬ (∀ u v : Bool, ¬ edgelessBool.Adj u v →
    (1 : Matrix Bool Bool ℝ) u v = 0) := by
  intro h
  have hz := h false false (by simp [edgelessBool])
  norm_num at hz

example : ∀ u v : Bool, u ≠ v → (1 : Matrix Bool Bool ℝ) u v = 0 := by
  intro u v huv
  simp [huv]

def nonedgeEntry : Matrix Bool Bool ℝ := fun u v => if u = false ∧ v = true then 1 else 0

example : ¬ (∀ u v : Bool, ¬ edgelessBool.Adj u v → nonedgeEntry u v = 0) := by
  intro h
  have hz := h false true (by simp [edgelessBool])
  norm_num [nonedgeEntry] at hz

example : ¬ edgelessBool.indepNum ≤
    (matrixInertia (1 : Matrix Bool Bool ℝ)).zero +
      min (matrixInertia (1 : Matrix Bool Bool ℝ)).pos
        (matrixInertia (1 : Matrix Bool Bool ℝ)).neg := by
  rw [edgelessBool_indepNum, matrixInertia_one]
  decide

def edgeBool : SimpleGraph Bool := ⊤
instance : DecidableRel edgeBool.Adj := by unfold edgeBool; infer_instance

example : ¬ edgeBool.IsIndepSet (↑(Finset.univ : Finset Bool) : Set Bool) := by
  decide +kernel

example : ¬ (2 : Nat) ≤ 1 := by decide

-- Negating a supported degenerate matrix preserves support, so both signs
-- remain admissible without a positivity assumption on edge weights.
example : ∀ u v : Bool, ¬ edgelessBool.Adj u v →
    (-(0 : Matrix Bool Bool ℝ)) u v = 0 := by
  intro u v h
  simp

-- A singular all-zero weighting is supported on C4, so zero edge weights are
-- permitted by the semantic interface.
example : ∀ u v : Fin 4, ¬ C4.Adj u v →
    (0 : Matrix (Fin 4) (Fin 4) ℝ) u v = 0 := by
  intro u v h
  rfl

example : C4.IsIndepSet (↑({0, 2} : Finset (Fin 4)) : Set (Fin 4)) := by
  decide +kernel

def triangle : SimpleGraph (Fin 3) := ⊤
instance : DecidableRel triangle.Adj := by unfold triangle; infer_instance

theorem triangle_inertia : matrixInertia (triangle.adjMatrix ℝ) = ⟨1, 0, 2⟩ := by
  simpa [triangle] using checkAdjacencyInertiaAt_sound (⊤ : SimpleGraph (Fin 3)) 0 ⟨1, 0, 2⟩
    (by decide +kernel)

theorem neg_triangle_inertia : matrixInertia (-(triangle.adjMatrix ℝ)) = ⟨2, 0, 1⟩ := by
  rw [matrixInertia_neg]
  simp only [triangle_inertia]

example :
    (matrixInertia (triangle.adjMatrix ℝ)).zero +
      min (matrixInertia (triangle.adjMatrix ℝ)).pos
        (matrixInertia (triangle.adjMatrix ℝ)).neg =
    (matrixInertia (-(triangle.adjMatrix ℝ))).zero +
      min (matrixInertia (-(triangle.adjMatrix ℝ))).pos
        (matrixInertia (-(triangle.adjMatrix ℝ))).neg := by
  rw [triangle_inertia, neg_triangle_inertia]
  decide

example : ∀ u v : Fin 3, ¬ triangle.Adj u v →
    (-(triangle.adjMatrix ℝ)) u v = 0 := by
  intro u v h
  simp [SimpleGraph.adjMatrix_apply, h]

example : (matrixInertia (C4.adjMatrix ℝ)).zero = 2 := by
  rw [ordinary_adjacency_inertia]

end SpectralGraphTests.Independence
