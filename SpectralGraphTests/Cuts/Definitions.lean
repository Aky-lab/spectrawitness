import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.Density

/-! The triangular prism and one triangular face. -/

namespace SpectralGraphTests.Cuts

def prism : SimpleGraph (Fin 6) where
  Adj i j := i ≠ j ∧ (i.val / 3 = j.val / 3 ∨ i.val % 3 = j.val % 3)
  symm := by
    intro i j h
    exact ⟨h.1.symm, h.2.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩
  loopless := ⟨fun i h => h.1 rfl⟩

instance : DecidableRel prism.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

theorem prism_regular : prism.IsRegularOfDegree 3 := by
  unfold SimpleGraph.IsRegularOfDegree
  decide +kernel

def face : Finset (Fin 6) := {0, 1, 2}

theorem face_card : face.card = 3 := by decide +kernel

theorem face_cut_card : (prism.interedges face faceᶜ).card = 3 := by
  decide +kernel

end SpectralGraphTests.Cuts
