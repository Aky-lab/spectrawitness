import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Option

/-!
# Generic one-vertex extensions of finite labelled graphs

This file is independent of any degree bound or spectral predicate.  It gives the mathematical operation used by an extension-based
enumerator; executable encodings can later prove agreement with this stable
definition.
-/

namespace SpectralGraph.Graph

open SimpleGraph

/-- Adjacency for adjoining one new final vertex whose old neighbours are
exactly `S`. -/
def oneVertexExtensionAdj {n : Nat} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : Fin (n + 1) → Fin (n + 1) → Prop :=
  Fin.lastCases
    (Fin.lastCases False (fun v ↦ v ∈ S))
    (fun u ↦ Fin.lastCases (u ∈ S) (fun v ↦ G.Adj u v))

theorem oneVertexExtensionAdj_symm {n : Nat} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : Symmetric (oneVertexExtensionAdj G S) := by
  intro i j
  refine Fin.lastCases ?_ (fun u ↦ ?_) i <;>
    refine Fin.lastCases ?_ (fun v ↦ ?_) j
  · simp [oneVertexExtensionAdj]
  · simp [oneVertexExtensionAdj]
  · simp [oneVertexExtensionAdj]
  · simp only [oneVertexExtensionAdj, Fin.lastCases_castSucc]
    exact G.adj_symm

theorem oneVertexExtensionAdj_loopless {n : Nat} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : Std.Irrefl (oneVertexExtensionAdj G S) := by
  constructor
  intro i
  refine Fin.lastCases ?_ (fun u ↦ ?_) i <;>
    simp [oneVertexExtensionAdj]

/-- Adjoin a new final vertex to exactly the vertices in `S`. -/
def oneVertexExtension {n : Nat} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : SimpleGraph (Fin (n + 1)) where
  Adj := oneVertexExtensionAdj G S
  symm := oneVertexExtensionAdj_symm G S
  loopless := oneVertexExtensionAdj_loopless G S

@[simp] theorem oneVertexExtension_adj_old {n : Nat}
    (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (u v : Fin n) :
    (oneVertexExtension G S).Adj u.castSucc v.castSucc ↔ G.Adj u v := by
  simp [oneVertexExtension, oneVertexExtensionAdj]

@[simp] theorem oneVertexExtension_adj_last_old {n : Nat}
    (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v : Fin n) :
    (oneVertexExtension G S).Adj (Fin.last n) v.castSucc ↔ v ∈ S := by
  simp [oneVertexExtension, oneVertexExtensionAdj]

@[simp] theorem oneVertexExtension_adj_old_last {n : Nat}
    (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (u : Fin n) :
    (oneVertexExtension G S).Adj u.castSucc (Fin.last n) ↔ u ∈ S := by
  simp [oneVertexExtension, oneVertexExtensionAdj]

@[simp] theorem oneVertexExtension_not_adj_last {n : Nat}
    (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    ¬ (oneVertexExtension G S).Adj (Fin.last n) (Fin.last n) := by
  exact (oneVertexExtension G S).loopless.irrefl (Fin.last n)

/-- The family of extensions obtained from a chosen finite collection of
neighbour sets.  Degree restrictions belong in the choice of `selections`,
not in the generic extension operation. -/
noncomputable def oneVertexExtensions {n : Nat} (G : SimpleGraph (Fin n))
    (selections : Finset (Finset (Fin n))) : Finset (SimpleGraph (Fin (n + 1))) := by
  classical
  exact selections.image (oneVertexExtension G)

theorem mem_oneVertexExtensions_iff {n : Nat} (G : SimpleGraph (Fin n))
    (selections : Finset (Finset (Fin n))) (H : SimpleGraph (Fin (n + 1))) :
    H ∈ oneVertexExtensions G selections ↔
      ∃ S ∈ selections, oneVertexExtension G S = H := by
  classical
  simp [oneVertexExtensions]

/-! ## Relabelling compatibility -/

/-- Extend a permutation of the old vertices by fixing the newly adjoined
final vertex. -/
def extendFinalEquiv {n : Nat} (e : Fin n ≃ Fin n) :
    Fin (n + 1) ≃ Fin (n + 1) :=
  (finSuccEquivLast : Fin (n + 1) ≃ Option (Fin n)).trans
    (e.optionCongr.trans
      (finSuccEquivLast : Fin (n + 1) ≃ Option (Fin n)).symm)

@[simp] theorem extendFinalEquiv_castSucc {n : Nat} (e : Fin n ≃ Fin n)
    (u : Fin n) :
    extendFinalEquiv e u.castSucc = (e u).castSucc := by
  simp [extendFinalEquiv]

@[simp] theorem extendFinalEquiv_last {n : Nat} (e : Fin n ≃ Fin n) :
    extendFinalEquiv e (Fin.last n) = Fin.last n := by
  simp [extendFinalEquiv]

/-- Transport a neighbour set along a relabelling of the old vertices. -/
def relabelFinset {n : Nat} (e : Fin n ≃ Fin n) (S : Finset (Fin n)) :
    Finset (Fin n) :=
  S.map e.toEmbedding

@[simp] theorem mem_relabelFinset_apply {n : Nat} (e : Fin n ≃ Fin n)
    (S : Finset (Fin n)) (u : Fin n) :
    e u ∈ relabelFinset e S ↔ u ∈ S := by
  simp [relabelFinset]

/-- One-vertex extension commutes with relabelling.  This is the generic
transport theorem needed by any extension-based finite graph census. -/
def oneVertexExtensionIso {n : Nat} {G H : SimpleGraph (Fin n)}
    (f : G ≃g H) (S : Finset (Fin n)) :
    oneVertexExtension G S ≃g
      oneVertexExtension H (relabelFinset f.toEquiv S) where
  toEquiv := extendFinalEquiv f.toEquiv
  map_rel_iff' := by
    intro i j
    refine Fin.lastCases ?_ (fun u ↦ ?_) i <;>
      refine Fin.lastCases ?_ (fun v ↦ ?_) j
    · simp
    · simp only [extendFinalEquiv_last, extendFinalEquiv_castSucc,
        oneVertexExtension_adj_last_old, mem_relabelFinset_apply]
    · simp only [extendFinalEquiv_last, extendFinalEquiv_castSucc,
        oneVertexExtension_adj_old_last, mem_relabelFinset_apply]
    · simpa using (f.map_adj_iff (v := u) (w := v))

/-! ## Decomposition at the final labelled vertex -/

/-- The induced labelled graph on all vertices except the final one. -/
def oldVertexPart {n : Nat} (G : SimpleGraph (Fin (n + 1))) :
    SimpleGraph (Fin n) :=
  G.comap Fin.castSucc

/-- The old neighbours of the final labelled vertex. -/
def finalVertexNeighbours {n : Nat} (G : SimpleGraph (Fin (n + 1)))
    [DecidableRel G.Adj] : Finset (Fin n) :=
  Finset.univ.filter fun v ↦ G.Adj (Fin.last n) v.castSucc

@[simp] theorem mem_finalVertexNeighbours {n : Nat}
    (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj] (v : Fin n) :
    v ∈ finalVertexNeighbours G ↔ G.Adj (Fin.last n) v.castSucc := by
  simp [finalVertexNeighbours]

/-- Every graph on `Fin (n+1)` is literally the one-vertex extension of its
old part by the final vertex's neighbour set. -/
theorem eq_oneVertexExtension_oldVertexPart {n : Nat}
    (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj] :
    G = oneVertexExtension (oldVertexPart G) (finalVertexNeighbours G) := by
  ext i j
  refine Fin.lastCases ?_ (fun u ↦ ?_) i <;>
    refine Fin.lastCases ?_ (fun v ↦ ?_) j
  · simp
  · simp
  · simpa using G.adj_comm u.castSucc (Fin.last n)
  · simp [oldVertexPart]

end SpectralGraph.Graph

