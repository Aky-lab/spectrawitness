import SpectralGraph.Graph.PackedEnumeration
import SpectralGraph.Search.SubsetCheck

/-! Capacity-pruned bounded-degree enumeration. Generate only neighbor subsets
of available vertices and size at most the degree bound. The proof identifies
its output members exactly with the simple reference generator, preserving both
coverage and validity without trusting this optimization. -/
namespace SpectralGraph.Graph
open SpectralGraph.Search

/-- Vertices whose degree has room for one additional neighbor. -/
def packedAvailableVertices (n d : Nat) (rows : PackedAdjacencyRows) : List (Fin n) :=
  (List.finRange n).filter fun u ↦ decide (packedDegreeAt n rows u.val < d)

/-- Neighbor selections generated with capacity and size pruning in advance. -/
def packedDegreeSelectionListFast (n d : Nat) (rows : PackedAdjacencyRows) :
    List (Finset (Fin n)) :=
  nonemptySubsetsAtMost d (packedAvailableVertices n d rows)

theorem mem_packedDegreeSelectionListFast (n d : Nat)
    (rows : PackedAdjacencyRows) (S : Finset (Fin n)) :
    S ∈ packedDegreeSelectionListFast n d rows ↔
      S ∈ boundedDegreeSelections (graphOfPackedRows n rows) d := by
  have hn : (packedAvailableVertices n d rows).Nodup := (List.nodup_finRange n).filter _
  rw [packedDegreeSelectionListFast,
    mem_nonemptySubsetsAtMost d _ hn S,
    mem_boundedDegreeSelections]
  have hcapacity : S ⊆ (packedAvailableVertices n d rows).toFinset ↔
      ∀ u ∈ S, (graphOfPackedRows n rows).degree u < d := by
    simp [Finset.subset_iff, packedAvailableVertices, packedDegreeAt_eq_degree]
  rw [hcapacity]
  tauto

/-- Optimized executable extension step with exactly the same candidates as the
reference step, possibly in a different order. -/
def packedDegreeExtensionCandidatesFast (n d : Nat) (parents : List PackedAdjacencyRows) :
    List PackedAdjacencyRows :=
  parents.flatMap fun rows ↦
    (packedDegreeSelectionListFast n d rows).map (extendPackedRows rows)

theorem mem_packedDegreeExtensionCandidatesFast (n d : Nat)
    (parents : List PackedAdjacencyRows) (child : PackedAdjacencyRows) :
    child ∈ packedDegreeExtensionCandidatesFast n d parents ↔
      ∃ rows ∈ parents, ∃ S ∈ boundedDegreeSelections (graphOfPackedRows n rows) d,
        extendPackedRows rows S = child := by
  simp [packedDegreeExtensionCandidatesFast, mem_packedDegreeSelectionListFast]

/-- Reference census recursion with the verified pruned extension step. -/
def packedConnectedDegreeGraphsFast : Nat → Nat → List PackedAdjacencyRows
  | 0, _ => []
  | 1, _ => [#[0]]
  | n + 2, d => packedDegreeExtensionCandidatesFast (n + 1) d
      (packedConnectedDegreeGraphsFast (n + 1) d)

/-- Optimization preserves the exact set of encoded outputs at every order. -/
theorem mem_packedConnectedDegreeGraphsFast_iff (n d : Nat) (rows : PackedAdjacencyRows) :
    rows ∈ packedConnectedDegreeGraphsFast n d ↔ rows ∈ packedConnectedDegreeGraphs n d := by
  induction n generalizing rows with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [packedConnectedDegreeGraphsFast, packedConnectedDegreeGraphs,
        mem_packedDegreeExtensionCandidatesFast, mem_packedDegreeExtensionCandidates, ih]

/-- The optimized executable generator covers every connected bounded-degree graph. -/
theorem packedConnectedDegreeGraphsFast_complete (n d : Nat) :
    CoversConnectedDegree n d (packedConnectedDegreeGraphsFast n d) := by
  intro G _ hG hd
  obtain ⟨rows, hr, hIso⟩ := packedConnectedDegreeGraphs_complete n d G hG hd
  exact ⟨rows, (mem_packedConnectedDegreeGraphsFast_iff n d rows).mpr hr, hIso⟩

/-- Every optimized output is connected and satisfies the prescribed degree bound. -/
theorem packedConnectedDegreeGraphsFast_sound (n d : Nat)
    {rows : PackedAdjacencyRows} (hr : rows ∈ packedConnectedDegreeGraphsFast n d) :
    (graphOfPackedRows n rows).Connected ∧ HasDegreeAtMost (graphOfPackedRows n rows) d :=
  packedConnectedDegreeGraphs_sound n d ((mem_packedConnectedDegreeGraphsFast_iff n d rows).mp hr)

/-- Stream checks over all extensions of one packed parent, applying degree
capacity and cardinality restrictions before evaluating the child checker. -/
def allPackedDegreeExtensionsFast (n d : Nat) (rows : PackedAdjacencyRows)
    (check : PackedAdjacencyRows → Bool) : Bool :=
  allNonemptySubsetsAtMost d (packedAvailableVertices n d rows)
    (fun S ↦ check (extendPackedRows rows S))

/-- Streamed optimized checking has the same acceptance condition as evaluating
every member of the reference extension list. -/
theorem allPackedDegreeExtensionsFast_eq_true_iff (n d : Nat)
    (rows : PackedAdjacencyRows) (check : PackedAdjacencyRows → Bool) :
    allPackedDegreeExtensionsFast n d rows check = true ↔
      ∀ child ∈ packedDegreeExtensions n d rows, check child = true := by
  rw [allPackedDegreeExtensionsFast, allNonemptySubsetsAtMost_eq_all, List.all_eq_true]
  change (∀ S ∈ packedDegreeSelectionListFast n d rows, check (extendPackedRows rows S) = true) ↔ _
  simp only [mem_packedDegreeSelectionListFast, packedDegreeExtensions,
    List.mem_map, mem_packedDegreeSelectionList]
  constructor
  · intro h child hchild
    obtain ⟨S, hS, rfl⟩ := hchild
    exact h S hS
  · intro h S hS
    exact h _ ⟨S, hS, rfl⟩

end SpectralGraph.Graph

