import SpectralGraph.Graph.IntegerSpectrum
import Mathlib.Combinatorics.SimpleGraph.Hasse

namespace SpectralGraphTests.IntegerSpectrum
open SpectralGraph SpectralGraph.Graph SimpleGraph

instance (n : Nat) : DecidableRel (pathGraph n).Adj := fun i j ↦
  decidable_of_iff (i.val + 1 = j.val ∨ j.val + 1 = i.val) pathGraph_adj.symm

-- No matrix conversion or Hermitian proof is supplied by the graph user.
example : checkAdjacencyEigenvalueBracket (pathGraph 5)
    (1732 / 1000) (1733 / 1000) ⟨1, 0, 4⟩ ⟨0, 0, 5⟩ 0 = true := by decide +kernel

theorem largest_path_five :
    (1732 / 1000 : ℝ) < (adjacency_isHermitian (pathGraph 5)).eigenvalues₀ ⟨0, by decide⟩ ∧
    (adjacency_isHermitian (pathGraph 5)).eigenvalues₀ ⟨0, by decide⟩ ≤ (1733 / 1000 : ℝ) := by
  simpa using checkAdjacencyEigenvalueBracket_sound (pathGraph 5)
    (1732 / 1000) (1733 / 1000) ⟨1, 0, 4⟩ ⟨0, 0, 5⟩ ⟨0, by decide⟩ (by decide +kernel)

example : checkAdjacencyEigenvaluesIoc (pathGraph 5) 0 2 ⟨2, 1, 2⟩ ⟨0, 0, 5⟩ 2 = true := by
  decide +kernel
example : checkAdjacencyEigenvalueBracket (pathGraph 5)
    (1733 / 1000) (1732 / 1000) ⟨0, 0, 5⟩ ⟨1, 0, 4⟩ 0 = false := by decide +kernel
example : checkAdjacencyEigenvalueBracket (pathGraph 5)
    0 2 ⟨2, 1, 2⟩ ⟨0, 0, 5⟩ 5 = false := by decide +kernel

#print axioms largest_path_five
end SpectralGraphTests.IntegerSpectrum
