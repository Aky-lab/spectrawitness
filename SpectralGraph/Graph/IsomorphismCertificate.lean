import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.NodupEquivFin

/-!
# Explicit finite graph-isomorphism certificates

An untrusted canonicalizer may return a proposed permutation as a list.  The
small checker below verifies that the list is a permutation and that adjacency
is preserved, then exposes an ordinary mathlib `SimpleGraph.Iso`.  This avoids
placing a refinement/individualisation implementation in the trusted path.
-/

namespace SpectralGraph
namespace Graph

open SimpleGraph

/-- A list contains every vertex exactly once. -/
def PermutationListSpec {n : Nat} (xs : List (Fin n)) : Prop :=
  xs.length = n ∧ xs.Nodup

def permutationListValid {n : Nat} (xs : List (Fin n)) : Bool :=
  xs.length == n && decide xs.Nodup

theorem permutationListValid_eq_true_iff {n : Nat} (xs : List (Fin n)) :
    permutationListValid xs = true ↔ PermutationListSpec xs := by
  simp [permutationListValid, PermutationListSpec]

theorem permutationList_mem_all {n : Nat} {xs : List (Fin n)}
    (h : PermutationListSpec xs) (x : Fin n) : x ∈ xs := by
  have hcard : xs.toFinset.card = Fintype.card (Fin n) := by
    rw [List.toFinset_card_of_nodup h.2, h.1, Fintype.card_fin]
  have huniv : xs.toFinset = Finset.univ :=
    (Finset.card_eq_iff_eq_univ xs.toFinset).mp hcard
  have : x ∈ xs.toFinset := by simp [huniv]
  simpa using this

/-- The equivalence encoded by a valid permutation list. -/
def permutationEquivOfList {n : Nat} (xs : List (Fin n))
    (h : PermutationListSpec xs) : Equiv.Perm (Fin n) :=
  (Equiv.cast (congrArg Fin h.1.symm)).trans
    (h.2.getEquivOfForallMemList xs (permutationList_mem_all h))

/-- Exact Boolean check for a proposed relabelling between two labelled
graphs.  The permutation data may be produced by any untrusted discovery
algorithm. -/
def graphRelabellingCertificateBool {n : Nat}
    (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (xs : List (Fin n)) : Bool :=
  if hvalid : permutationListValid xs = true then
    let h := (permutationListValid_eq_true_iff xs).mp hvalid
    let e := permutationEquivOfList xs h
    decide (∀ u v, H.Adj (e u) (e v) ↔ G.Adj u v)
  else false

/-- A successful explicit relabelling check produces a standard mathlib graph
isomorphism. -/
theorem graphRelabellingCertificateBool_sound {n : Nat}
    (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (xs : List (Fin n))
    (hcheck : graphRelabellingCertificateBool G H xs = true) :
    Nonempty (G ≃g H) := by
  unfold graphRelabellingCertificateBool at hcheck
  split at hcheck
  next hvalid =>
    let hperm := (permutationListValid_eq_true_iff xs).mp hvalid
    let e := permutationEquivOfList xs hperm
    have hadj : ∀ u v, H.Adj (e u) (e v) ↔ G.Adj u v :=
      of_decide_eq_true hcheck
    exact ⟨{ e with map_rel_iff' := hadj _ _ }⟩
  next hvalid => simp at hcheck

end Graph
end SpectralGraph
