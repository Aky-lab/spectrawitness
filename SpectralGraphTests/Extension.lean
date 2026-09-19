import SpectralGraph.Graph.ExtensionCompleteness

/-! Kernel-checked examples for connected bounded-degree extension generation. -/
namespace SpectralGraphTests.Extension
open SpectralGraph.Graph SimpleGraph

def edge : SimpleGraph (Fin 2) :=
  oneVertexExtension (⊥ : SimpleGraph (Fin 1)) {0}
instance : DecidableRel edge.Adj := oneVertexExtensionDecidableRel _ _

def pathThree : SimpleGraph (Fin 3) := oneVertexExtension edge {1}
instance : DecidableRel pathThree.Adj := oneVertexExtensionDecidableRel _ _

-- Degree-one capacity forbids adding any vertex to an already saturated edge.
example : boundedDegreeSelections edge 1 = ∅ := by decide
-- An isolated new vertex is deliberately excluded from connected enumeration.
example : (∅ : Finset (Fin 2)) ∉ boundedDegreeSelections edge 2 := by decide
-- A triangle is a permitted degree-two extension of an edge.
example : ({0, 1} : Finset (Fin 2)) ∈ boundedDegreeSelections edge 2 := by decide
-- The middle vertex of a path has exhausted its degree-two capacity.
example : ({1} : Finset (Fin 3)) ∉ boundedDegreeSelections pathThree 2 := by decide
-- Exactly the two single endpoints and their pair remain available.
example : (boundedDegreeSelections pathThree 2).card = 3 := by decide
-- Increasing the degree bound really changes the general-purpose enumeration.
example : (boundedDegreeSelections pathThree 3).card = 7 := by decide

example : pathThree.Connected := by
  apply connected_oneVertexExtension edge {1}
  · apply connected_oneVertexExtension (⊥ : SimpleGraph (Fin 1)) {0}
    · exact Connected.of_subsingleton
    · simp
  · simp

example : HasDegreeAtMost pathThree 2 := by
  apply (hasDegreeAtMost_oneVertexExtension_iff edge {1} 2).2
  unfold HasDegreeAtMost
  decide

#print axioms boundedDegreeExtensionCandidates_complete
#print axioms boundedDegreeExtensionCandidates_sound
#print axioms hasDegreeAtMost_oneVertexExtension_iff
end SpectralGraphTests.Extension
