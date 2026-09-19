import SpectralGraph.Graph.Encoding
import SpectralGraph.Graph.ExtensionCompleteness
import Mathlib.Data.List.Sublists

/-! Executable, complete connected bounded-degree enumeration by vertex extension.
This reference generator prioritizes a small auditable correctness proof; it retains
isomorphic duplicates and enumerates all subsets before applying degree pruning. -/
namespace SpectralGraph.Graph
open SimpleGraph

/-- An executable ordering of all subsets of the labelled vertex set. -/
def vertexSubsetList (n : Nat) : List (Finset (Fin n)) :=
  (List.finRange n).sublists.map List.toFinset

@[simp] theorem mem_vertexSubsetList {n : Nat} (S : Finset (Fin n)) :
    S ∈ vertexSubsetList n := by
  apply List.mem_map.mpr
  refine ⟨(List.finRange n).filter (fun u ↦ decide (u ∈ S)),
    List.mem_sublists.mpr List.filter_sublist, ?_⟩
  ext u
  simp

/-- Nonempty neighbor selections respecting new and old vertex degree capacity. -/
def packedDegreeSelectionList (n d : Nat) (rows : PackedAdjacencyRows) :
    List (Finset (Fin n)) :=
  (vertexSubsetList n).filter fun S ↦ decide
    (S.Nonempty ∧ S.card ≤ d ∧ ∀ u ∈ S, (graphOfPackedRows n rows).degree u < d)

@[simp] theorem mem_packedDegreeSelectionList (n d : Nat)
    (rows : PackedAdjacencyRows) (S : Finset (Fin n)) :
    S ∈ packedDegreeSelectionList n d rows ↔
      S ∈ boundedDegreeSelections (graphOfPackedRows n rows) d := by
  simp [packedDegreeSelectionList]

/-- Executable extensions of one packed graph. -/
def packedDegreeExtensions (n d : Nat) (rows : PackedAdjacencyRows) :
    List PackedAdjacencyRows :=
  (packedDegreeSelectionList n d rows).map (extendPackedRows rows)

/-- Executable extension step for an arbitrary finite parent family. -/
def packedDegreeExtensionCandidates (n d : Nat) (parents : List PackedAdjacencyRows) :
    List PackedAdjacencyRows := parents.flatMap (packedDegreeExtensions n d)

@[simp] theorem mem_packedDegreeExtensionCandidates (n d : Nat)
    (parents : List PackedAdjacencyRows) (child : PackedAdjacencyRows) :
    child ∈ packedDegreeExtensionCandidates n d parents ↔
      ∃ rows ∈ parents, ∃ S ∈ boundedDegreeSelections (graphOfPackedRows n rows) d,
        extendPackedRows rows S = child := by
  simp [packedDegreeExtensionCandidates, packedDegreeExtensions]

/-- Isomorphism coverage of all connected graphs of order `n` and degree at most `d`. -/
def CoversConnectedDegree (n d : Nat) (rows : List PackedAdjacencyRows) : Prop :=
  ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.Connected → HasDegreeAtMost G d →
      ∃ r ∈ rows, Nonempty (G ≃g graphOfPackedRows n r)

/-- The executable step preserves coverage, at any degree bound. -/
theorem CoversConnectedDegree.extensions {n d : Nat}
    {parents : List PackedAdjacencyRows} (hparents : CoversConnectedDegree n d parents)
    (hn : 0 < n) :
    CoversConnectedDegree (n + 1) d (packedDegreeExtensionCandidates n d parents) := by
  intro G _ hG hdegree
  obtain ⟨H, instH, hH, hHd, S, _, ⟨f⟩⟩ :=
    connected_boundedDegree_iso_oneVertexExtension hn G d hG hdegree
  letI := instH
  obtain ⟨rows, hrows, ⟨e⟩⟩ := hparents H hH hHd
  let T := relabelFinset e.toEquiv S
  let g : G ≃g oneVertexExtension (graphOfPackedRows n rows) T :=
    f.trans (oneVertexExtensionIso e S)
  have hT : T ∈ boundedDegreeSelections (graphOfPackedRows n rows) d := by
    apply (mem_boundedDegreeSelections _ d T).2
    exact oneVertexExtension_selection_conditions hn _ T d
      (g.connected_iff.mp hG) ((hasDegreeAtMost_iso_iff g d).mp hdegree)
  refine ⟨extendPackedRows rows T,
    (mem_packedDegreeExtensionCandidates _ _ _ _).mpr ⟨rows, hrows, T, hT, rfl⟩, ?_⟩
  rw [graphOfPackedRows_extend]
  exact ⟨g⟩

/-- Every generated child is connected and degree bounded if its parent is. -/
theorem packedDegreeExtensionCandidates_sound (n d : Nat)
    (parents : List PackedAdjacencyRows)
    (hparents : ∀ rows ∈ parents,
      (graphOfPackedRows n rows).Connected ∧ HasDegreeAtMost (graphOfPackedRows n rows) d)
    {child : PackedAdjacencyRows}
    (hchild : child ∈ packedDegreeExtensionCandidates n d parents) :
    (graphOfPackedRows (n + 1) child).Connected ∧
      HasDegreeAtMost (graphOfPackedRows (n + 1) child) d := by
  obtain ⟨rows, hr, S, hS, rfl⟩ :=
    (mem_packedDegreeExtensionCandidates _ _ _ _).mp hchild
  let e : graphOfPackedRows (n + 1) (extendPackedRows rows S) ≃g
      oneVertexExtension (graphOfPackedRows n rows) S :=
    { toEquiv := Equiv.refl _
      map_rel_iff' := by intro u v; simp [graphOfPackedRows_extend] }
  obtain ⟨hc, hd⟩ := boundedDegreeSelections_sound _ d
    (hparents rows hr).1 (hparents rows hr).2 hS
  exact ⟨e.connected_iff.mpr hc, (hasDegreeAtMost_iso_iff e d).mpr hd⟩

/-- Replacing candidates by isomorphic representatives preserves coverage. -/
theorem CoversConnectedDegree.deduplicate {n d : Nat}
    {candidates representatives : List PackedAdjacencyRows}
    (hcover : CoversConnectedDegree n d candidates)
    (hdedup : ∀ r ∈ candidates, ∃ s ∈ representatives,
      Nonempty (graphOfPackedRows n r ≃g graphOfPackedRows n s)) :
    CoversConnectedDegree n d representatives := by
  intro G _ hG hd
  obtain ⟨r, hr, ⟨f⟩⟩ := hcover G hG hd
  obtain ⟨s, hs, ⟨g⟩⟩ := hdedup r hr
  exact ⟨s, hs, ⟨f.trans g⟩⟩

/-- Reference exhaustive generator, including duplicates, indexed by graph order.
Order zero has no connected graphs; order one starts with the unique singleton. -/
def packedConnectedDegreeGraphs : Nat → Nat → List PackedAdjacencyRows
  | 0, _ => []
  | 1, _ => [#[0]]
  | n + 2, d => packedDegreeExtensionCandidates (n + 1) d
      (packedConnectedDegreeGraphs (n + 1) d)

/-- The reference generator covers every connected bounded-degree graph. -/
theorem packedConnectedDegreeGraphs_complete (n d : Nat) :
    CoversConnectedDegree n d (packedConnectedDegreeGraphs n d) := by
  induction n with
  | zero =>
    intro G _ hG _
    exact Fin.elim0 (Classical.choice hG.nonempty)
  | succ n ih =>
    cases n with
    | zero =>
      haveI : Subsingleton (Fin (0 + 1)) := ⟨fun a b ↦ Fin.ext (by omega)⟩
      intro G _ _ _
      refine ⟨#[0], by simp [packedConnectedDegreeGraphs], ?_⟩
      have hgraph : G = graphOfPackedRows 1 #[0] := by
        ext u v
        have huv : u = v := Subsingleton.elim u v
        subst v
        simp
      subst G
      exact ⟨SimpleGraph.Iso.refl⟩
    | succ n =>
      exact ih.extensions (Nat.zero_lt_succ n)

/-- Every output of the reference generator is a connected graph satisfying the bound. -/
theorem packedConnectedDegreeGraphs_sound (n d : Nat)
    {rows : PackedAdjacencyRows} (hrows : rows ∈ packedConnectedDegreeGraphs n d) :
    (graphOfPackedRows n rows).Connected ∧ HasDegreeAtMost (graphOfPackedRows n rows) d := by
  induction n generalizing rows with
  | zero => simp [packedConnectedDegreeGraphs] at hrows
  | succ n ih =>
    cases n with
    | zero =>
      haveI : Subsingleton (Fin (0 + 1)) := ⟨fun a b ↦ Fin.ext (by omega)⟩
      simp only [packedConnectedDegreeGraphs, List.mem_singleton] at hrows
      subst rows
      refine ⟨Connected.of_subsingleton, ?_⟩
      have hz : ∀ v, (graphOfPackedRows 1 #[0]).degree v = 0 := by decide
      intro v
      rw [hz]
      exact Nat.zero_le d
    | succ n =>
      exact packedDegreeExtensionCandidates_sound (n + 1) d _
        (fun _ h ↦ ih h) hrows

end SpectralGraph.Graph
