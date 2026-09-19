import SpectralGraph.Graph.IntegerSpectrum
import Mathlib.Combinatorics.SimpleGraph.Clique

/-! Independently authored named rook graph and its elementary combinatorics. -/

namespace SpectralGraphTests.Hoffman.Definitions

def rook3 : SimpleGraph (Fin 9) where
  Adj i j := i ≠ j ∧ (i.val / 3 = j.val / 3 ∨ i.val % 3 = j.val % 3)
  symm := by
    intro i j h
    exact ⟨Ne.symm h.1, h.2.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩
  loopless := ⟨fun i h => h.1 rfl⟩

instance : DecidableRel rook3.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

theorem rook3_regular : rook3.IsRegularOfDegree 4 := by
  unfold SimpleGraph.IsRegularOfDegree
  decide +kernel

def diagonal : Finset (Fin 9) := {0, 4, 8}

theorem diagonal_independent : rook3.IsIndepSet (↑diagonal : Set (Fin 9)) := by
  decide +kernel

theorem diagonal_card : diagonal.card = 3 := by
  decide +kernel

end SpectralGraphTests.Hoffman.Definitions
