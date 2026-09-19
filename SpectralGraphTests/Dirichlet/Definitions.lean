import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import SpectralGraph.Graph.LaplacianUpdate

namespace SpectralGraphTests.Dirichlet

/-- The four bridge vertices, ordered as two interiors followed by two terminals. -/
abbrev V := Fin 2 ⊕ Fin 2

/-- The unbalanced Wheatstone bridge: every distinct pair is adjacent except the
terminal-terminal pair. -/
def bridge : SimpleGraph V where
  Adj i j := i ≠ j ∧ (i.isLeft ∨ j.isLeft)
  symm := by
    intro i j h
    exact ⟨h.1.symm, h.2.elim Or.inr Or.inl⟩
  loopless := ⟨fun i h => h.1 rfl⟩

instance : DecidableRel bridge.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ _))

/-- The `v-t` edge has one extra unit of conductance, hence weight two. -/
def weightedBridge : Matrix V V ℝ :=
  SpectralGraph.Graph.laplacianUpdate bridge (Sum.inl 1) (Sum.inr 1) 1

end SpectralGraphTests.Dirichlet
