import SpectralGraph.Graph.ExtensionDegree
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Generic completeness step for extension-based graph enumeration

Every finite nontrivial connected graph can be relabelled so that deleting
the final vertex leaves a connected graph.  Together with the literal
one-vertex decomposition, this is the graph-theoretic induction step used by
finite graph censuses; it contains no degree bound or order cutoff.
-/

namespace SpectralGraph.Graph

open SimpleGraph

/-- Relabel `Fin (n+1)` so that its final vertex is sent to `v`; old vertices
are sent through `v.succAbove`. -/
def relabelFinalTo {n : Nat} (v : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
  finSuccEquivLast.trans (finSuccEquiv' v).symm

@[simp] theorem relabelFinalTo_last {n : Nat} (v : Fin (n + 1)) :
    relabelFinalTo v (Fin.last n) = v := by
  simp [relabelFinalTo]

@[simp] theorem relabelFinalTo_castSucc {n : Nat} (v : Fin (n + 1))
    (u : Fin n) :
    relabelFinalTo v u.castSucc = v.succAbove u := by
  simp [relabelFinalTo, finSuccEquiv'_symm_some]

/-- The complement of a singleton, in the subtype convention used by
`SimpleGraph.induce`, is equivalent to `Fin n`. -/
def complementSingletonEquivFin {n : Nat} (v : Fin (n + 1)) :
    {x : Fin (n + 1) // x ∈ ({v} : Set (Fin (n + 1)))ᶜ} ≃ Fin n :=
  (Equiv.subtypeEquivRight fun x ↦ by simp).trans
    (finSuccAboveEquiv v).symm

/-- Deleting `v` and then using the canonical `succAbove` labels gives the
old-vertex part after relabelling the final vertex to `v`. -/
def deletedVertexIsoOldPart {n : Nat} (G : SimpleGraph (Fin (n + 1)))
    (v : Fin (n + 1)) :
    G.induce ({v} : Set (Fin (n + 1)))ᶜ ≃g
      oldVertexPart (G.comap (relabelFinalTo v)) where
  toEquiv := complementSingletonEquivFin v
  map_rel_iff' := by
    intro x y
    simp only [oldVertexPart, SimpleGraph.comap_adj,
      relabelFinalTo_castSucc]
    let changeSubtype :
        {x : Fin (n + 1) // x ∈ ({v} : Set (Fin (n + 1)))ᶜ} ≃
          {x : Fin (n + 1) // x ≠ v} :=
      Equiv.subtypeEquivRight (fun _ ↦ by simp)
    have hx : v.succAbove (complementSingletonEquivFin v x) = x.val := by
      have happly := congrArg Subtype.val
        ((finSuccAboveEquiv v).apply_symm_apply (changeSubtype x))
      exact happly
    have hy : v.succAbove (complementSingletonEquivFin v y) = y.val := by
      have happly := congrArg Subtype.val
        ((finSuccAboveEquiv v).apply_symm_apply (changeSubtype y))
      exact happly
    rw [hx, hy]
    rfl

/-- Generic extension-enumeration completeness step: a connected graph of
order `n+1` (with `n>0`) is isomorphic to a one-vertex extension of a connected
graph of order `n`. -/
theorem connected_iso_oneVertexExtension_of_pos {n : Nat} (hn : 0 < n)
    (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj]
    (hconnected : G.Connected) :
    ∃ H : SimpleGraph (Fin n), ∃ S : Finset (Fin n),
      H.Connected ∧ Nonempty (G ≃g oneVertexExtension H S) := by
  letI : Nontrivial (Fin (n + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨v, hv⟩ :=
    hconnected.exists_connected_induce_compl_singleton_of_finite_nontrivial
  let relabelled := G.comap (relabelFinalTo v)
  let H := oldVertexPart relabelled
  letI : DecidableRel relabelled.Adj := inferInstance
  let S := finalVertexNeighbours relabelled
  have hH : H.Connected :=
    (deletedVertexIsoOldPart G v).connected_iff.mp hv
  refine ⟨H, S, hH, ?_⟩
  have hdecomp : relabelled = oneVertexExtension H S :=
    eq_oneVertexExtension_oldVertexPart relabelled
  let relabelIso : relabelled ≃g G :=
    { toEquiv := relabelFinalTo v
      map_rel_iff' := by rfl }
  let decompositionIso : relabelled ≃g oneVertexExtension H S :=
    { toEquiv := Equiv.refl _
      map_rel_iff' := by simp [hdecomp] }
  exact ⟨relabelIso.symm.trans decompositionIso⟩

/-- A connected bounded-degree graph has a connected bounded-degree parent
and a selection satisfying exactly the local capacity restrictions. -/
theorem connected_boundedDegree_iso_oneVertexExtension {n : Nat} (hn : 0 < n)
    (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj] (d : Nat)
    (hconnected : G.Connected) (hdegree : HasDegreeAtMost G d) :
    ∃ H : SimpleGraph (Fin n), ∃ _ : DecidableRel H.Adj,
      H.Connected ∧ HasDegreeAtMost H d ∧
      ∃ S ∈ boundedDegreeSelections H d,
        Nonempty (G ≃g oneVertexExtension H S) := by
  classical
  obtain ⟨H, S, hH, ⟨f⟩⟩ := connected_iso_oneVertexExtension_of_pos hn G hconnected
  have hExt : HasDegreeAtMost (oneVertexExtension H S) d :=
    (hasDegreeAtMost_iso_iff f d).1 hdegree
  have hParent := (hasDegreeAtMost_oneVertexExtension_iff H S d).1 hExt
  have hSelection := oneVertexExtension_selection_conditions hn H S d
    (f.connected_iff.mp hconnected) hExt
  exact ⟨H, inferInstance, hH, hParent.1, S,
    (mem_boundedDegreeSelections H d S).2 hSelection, ⟨f⟩⟩

section Census
attribute [local instance] Classical.propDecidable

/-- The finite semantic candidate family produced by one bounded-degree extension
step. The selections are executable; equality of `SimpleGraph` values is classical. -/
noncomputable def boundedDegreeExtensionCandidates {n : Nat}
    (parents : Finset (SimpleGraph (Fin n))) (d : Nat) :
    Finset (SimpleGraph (Fin (n + 1))) :=
  parents.biUnion fun H ↦ oneVertexExtensions H (boundedDegreeSelections H d)

/-- A census covering connected bounded-degree parents produces a census covering
all connected bounded-degree children. Parent labels need not match the labels
obtained by deleting a vertex: extension isomorphisms transport the selection. -/
theorem boundedDegreeExtensionCandidates_complete {n : Nat} (hn : 0 < n)
    (parents : Finset (SimpleGraph (Fin n))) (d : Nat)
    (hparents : ∀ H : SimpleGraph (Fin n), H.Connected → HasDegreeAtMost H d →
      ∃ R ∈ parents, Nonempty (H ≃g R))
    (G : SimpleGraph (Fin (n + 1))) (hG : G.Connected)
    (hdegree : HasDegreeAtMost G d) :
    ∃ K ∈ boundedDegreeExtensionCandidates parents d, Nonempty (G ≃g K) := by
  obtain ⟨H, instH, hH, hHd, S, hS, ⟨f⟩⟩ :=
    connected_boundedDegree_iso_oneVertexExtension hn G d hG hdegree
  have hi : instH = (fun a b ↦ Classical.propDecidable (H.Adj a b)) := Subsingleton.elim _ _
  subst instH
  obtain ⟨R, hR, ⟨e⟩⟩ := hparents H hH hHd
  let T := relabelFinset e.toEquiv S
  let g : G ≃g oneVertexExtension R T := f.trans (oneVertexExtensionIso e S)
  have hT : T ∈ boundedDegreeSelections R d := by
    apply (mem_boundedDegreeSelections R d T).2
    exact oneVertexExtension_selection_conditions hn R T d
      (g.connected_iff.mp hG) ((hasDegreeAtMost_iso_iff g d).mp hdegree)
  refine ⟨oneVertexExtension R T, ?_, ⟨g⟩⟩
  exact Finset.mem_biUnion.mpr ⟨R, hR,
    (mem_oneVertexExtensions_iff R _ _).mpr ⟨T, hT, rfl⟩⟩

/-- Candidate generation preserves validity when all supplied parents are valid. -/
theorem boundedDegreeExtensionCandidates_sound {n : Nat}
    (parents : Finset (SimpleGraph (Fin n))) (d : Nat)
    (hparents : ∀ H ∈ parents, H.Connected ∧ HasDegreeAtMost H d)
    {K : SimpleGraph (Fin (n + 1))}
    (hK : K ∈ boundedDegreeExtensionCandidates parents d) :
    K.Connected ∧ HasDegreeAtMost K d := by
  obtain ⟨H, hH, hK⟩ := Finset.mem_biUnion.mp hK
  obtain ⟨S, hS, rfl⟩ := (mem_oneVertexExtensions_iff H _ K).mp hK
  have hi : (fun a b ↦ Classical.propDecidable ((oneVertexExtension H S).Adj a b)) =
      oneVertexExtensionDecidableRel H S := Subsingleton.elim _ _
  rw [hi]
  exact boundedDegreeSelections_sound H d (hparents H hH).1 (hparents H hH).2 hS

end Census
end SpectralGraph.Graph

