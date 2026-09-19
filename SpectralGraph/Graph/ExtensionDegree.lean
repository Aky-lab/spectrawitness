import SpectralGraph.Graph.Extension
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Degrees in a one-vertex extension

These formulas are generic in the degree bound and are useful for any
extension-based bounded-degree graph enumeration.
-/

namespace SpectralGraph.Graph

open SimpleGraph

instance oneVertexExtensionDecidableRel {n : Nat}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) : DecidableRel (oneVertexExtension G S).Adj :=
  fun i j ↦ by
    refine Fin.lastCases ?_ (fun u ↦ ?_) i <;>
      refine Fin.lastCases ?_ (fun v ↦ ?_) j <;>
      simp only [oneVertexExtension, oneVertexExtensionAdj,
        Fin.lastCases_last, Fin.lastCases_castSucc] <;> infer_instance

theorem neighborFinset_oneVertexExtension_last {n : Nat}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) :
    (oneVertexExtension G S).neighborFinset (Fin.last n) =
      S.map Fin.castSuccEmb := by
  classical
  ext w
  refine Fin.lastCases ?_ (fun u ↦ ?_) w
  · simp
  · simp

theorem degree_oneVertexExtension_last {n : Nat}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) :
    (oneVertexExtension G S).degree (Fin.last n) = S.card := by
  rw [← card_neighborFinset_eq_degree,
    neighborFinset_oneVertexExtension_last G S, Finset.card_map]

theorem neighborFinset_oneVertexExtension_castSucc {n : Nat}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (u : Fin n) :
    (oneVertexExtension G S).neighborFinset u.castSucc =
      (G.neighborFinset u).map Fin.castSuccEmb ∪
        if u ∈ S then {Fin.last n} else ∅ := by
  classical
  ext w
  refine Fin.lastCases ?_ (fun v ↦ ?_) w
  · by_cases hu : u ∈ S <;> simp [hu]
  · by_cases hu : u ∈ S <;> simp [hu]

theorem degree_oneVertexExtension_castSucc {n : Nat}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (u : Fin n) :
    (oneVertexExtension G S).degree u.castSucc =
      G.degree u + if u ∈ S then 1 else 0 := by
  rw [← card_neighborFinset_eq_degree,
    neighborFinset_oneVertexExtension_castSucc G S u]
  by_cases hu : u ∈ S
  · simp [hu, Fin.castSucc_ne_last]
  · simp [hu]

/-- Pointwise formulation of a maximum-degree bound. -/
def HasDegreeAtMost {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (d : Nat) : Prop :=
  ∀ v, G.degree v ≤ d

theorem hasDegreeAtMost_iso_iff {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (f : G ≃g H) (d : Nat) :
    HasDegreeAtMost G d ↔ HasDegreeAtMost H d := by
  constructor
  · intro h w
    rw [← f.apply_symm_apply w, f.degree_eq]
    exact h (f.symm w)
  · intro h v
    rw [← f.degree_eq v]
    exact h (f v)

theorem hasDegreeAtMost_iff_maxDegree_le {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : Nat) :
    HasDegreeAtMost G d ↔ G.maxDegree ≤ d := by
  constructor
  · exact fun h ↦ G.maxDegree_le_of_forall_degree_le d h
  · intro h v
    exact (G.degree_le_maxDegree v).trans h

/-- Necessary neighbour-set conditions for a connected bounded-degree extension. -/
theorem oneVertexExtension_selection_conditions {n : Nat}
    (hn : 0 < n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (d : Nat)
    (hconnected : (oneVertexExtension G S).Connected)
    (hdegree : HasDegreeAtMost (oneVertexExtension G S) d) :
    S.Nonempty ∧ S.card ≤ d ∧ ∀ u ∈ S, G.degree u < d := by
  letI : Nontrivial (Fin (n + 1)) :=
    Fin.nontrivial_iff_two_le.mpr (by omega)
  have hnotIsolated :
      ¬ (oneVertexExtension G S).IsIsolated (Fin.last n) :=
    hconnected.preconnected.not_isIsolated (Fin.last n)
  have hneighbours :
      ((oneVertexExtension G S).neighborFinset (Fin.last n)).Nonempty :=
    (SimpleGraph.neighborFinset_nonempty
      (oneVertexExtension G S) (Fin.last n)).mpr hnotIsolated
  have hSnonempty : S.Nonempty := by
    rw [neighborFinset_oneVertexExtension_last G S,
      Finset.map_nonempty] at hneighbours
    exact hneighbours
  refine ⟨hSnonempty, ?_, ?_⟩
  · rw [← degree_oneVertexExtension_last G S]
    exact hdegree (Fin.last n)
  · intro u hu
    have hold := hdegree u.castSucc
    rw [degree_oneVertexExtension_castSucc G S u, if_pos hu] at hold
    omega

/-- Exact local criterion for preserving a maximum-degree bound. -/
theorem hasDegreeAtMost_oneVertexExtension_iff {n : Nat}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (d : Nat) :
    HasDegreeAtMost (oneVertexExtension G S) d ↔
      HasDegreeAtMost G d ∧ S.card ≤ d ∧ ∀ u ∈ S, G.degree u < d := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro u
      have hu := h u.castSucc
      rw [degree_oneVertexExtension_castSucc] at hu
      omega
    · simpa [degree_oneVertexExtension_last] using h (Fin.last n)
    · intro u hu
      have hd := h u.castSucc
      rw [degree_oneVertexExtension_castSucc, if_pos hu] at hd
      omega
  · rintro ⟨hG, hS, hselected⟩ v
    refine Fin.lastCases ?_ (fun u ↦ ?_) v
    · simpa [degree_oneVertexExtension_last] using hS
    · rw [degree_oneVertexExtension_castSucc]
      by_cases hu : u ∈ S
      · rw [if_pos hu]
        exact hselected u hu
      · simpa [hu] using hG u

/-- Finite choices that attach a new vertex while respecting degree capacity. -/
def boundedDegreeSelections {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (d : Nat) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun S ↦ S.Nonempty ∧ S.card ≤ d ∧ ∀ u ∈ S, G.degree u < d

@[simp] theorem mem_boundedDegreeSelections {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (d : Nat) (S : Finset (Fin n)) :
    S ∈ boundedDegreeSelections G d ↔
      S.Nonempty ∧ S.card ≤ d ∧ ∀ u ∈ S, G.degree u < d := by
  simp [boundedDegreeSelections]

/-- Attaching to a nonempty selection preserves connectedness. -/
theorem connected_oneVertexExtension {n : Nat} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (hG : G.Connected) (hS : S.Nonempty) :
    (oneVertexExtension G S).Connected := by
  obtain ⟨u, hu⟩ := hS
  let embed : G →g oneVertexExtension G S :=
    { toFun := Fin.castSucc
      map_rel' := by intro a b hab; exact (oneVertexExtension_adj_old G S a b).2 hab }
  apply (connected_iff_exists_forall_reachable _).2
  refine ⟨u.castSucc, fun v ↦ ?_⟩
  refine Fin.lastCases ?_ (fun w ↦ ?_) v
  · exact ((oneVertexExtension_adj_old_last G S u).2 hu).reachable
  · exact (hG u w).map embed

/-- Every permitted selection produces a connected bounded-degree graph. -/
theorem boundedDegreeSelections_sound {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (d : Nat) (hG : G.Connected)
    (hdegree : HasDegreeAtMost G d) {S : Finset (Fin n)}
    (hS : S ∈ boundedDegreeSelections G d) :
    (oneVertexExtension G S).Connected ∧
      HasDegreeAtMost (oneVertexExtension G S) d := by
  obtain ⟨hne, hcard, hcapacity⟩ := (mem_boundedDegreeSelections G d S).1 hS
  exact ⟨connected_oneVertexExtension G S hG hne,
    (hasDegreeAtMost_oneVertexExtension_iff G S d).2 ⟨hdegree, hcard, hcapacity⟩⟩

end SpectralGraph.Graph
