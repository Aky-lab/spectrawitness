import SpectralGraph.Graph.IsomorphismCertificate
import SpectralGraph.Graph.InertiaIso
import SpectralGraph.Search.Coverage

/-!
# Isomorphism-certified finite graph search

A natural-number permutation input is checked without silently discarding
invalid vertices. Coverage and property checking compose through ordinary
mathlib graph isomorphisms; no canonicalization algorithm is trusted.
-/

namespace SpectralGraph.Graph

/-- Strict conversion: a single out-of-range vertex rejects the whole list. -/
def parsePermutation (n : Nat) : List Nat → Option (List (Fin n))
  | [] => some []
  | x :: xs => if h : x < n then
      (parsePermutation n xs).map (⟨x, h⟩ :: ·)
    else none

/-- Relabeling checker for untrusted natural-number input. -/
def checkIsomorphism {n : Nat} (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (xs : List Nat) : Bool :=
  match parsePermutation n xs with
  | none => false
  | some ys => graphRelabellingCertificateBool G H ys

/-- Accepted input yields an ordinary graph isomorphism. -/
theorem checkIsomorphism_sound {n : Nat} (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (xs : List Nat)
    (h : checkIsomorphism G H xs = true) : Nonempty (G ≃g H) := by
  unfold checkIsomorphism at h
  cases hp : parsePermutation n xs with
  | none => simp [hp] at h
  | some ys => exact graphRelabellingCertificateBool_sound G H ys (by simpa [hp] using h)

/-- Build a graph cover from checked representative assignments. Graph
encoding is arbitrary and need not be injective; the relation uses decoded
graphs. This supports packed, sparse, or externally serialized graph data. -/
def certifiedCover {α : Type*} {n : Nat} {admissible : α → Prop}
    (decode : α → SimpleGraph (Fin n))
    [∀ x, DecidableRel (decode x).Adj]
    (C : Search.Certificate admissible) (D : Search.DedupCertificate α (List Nat))
    (h : Search.dedupCertificateValid
      (fun x y p ↦ checkIsomorphism (decode x) (decode y) p) C.candidates D = true) :
    Search.Cover admissible (fun x y ↦ Nonempty (decode x ≃g decode y)) where
  representatives := D.representatives
  exhaustive x hx := by
    exact Search.dedupCertificateValid_sound _ _
      (fun x y p hp ↦ checkIsomorphism_sound (decode x) (decode y) p hp)
      C.candidates D h x (C.exhaustive x hx)

/-- End-to-end spectral search theorem. Exhaustiveness, checked isomorphism
assignments, and sound spectral checks on retained representatives imply the
inertia property for every admissible graph at the chosen real threshold. -/
theorem verifyInertia {α : Type*} {n : Nat} {admissible : α → Prop}
    (decode : α → SimpleGraph (Fin n))
    [∀ x, DecidableRel (decode x).Adj]
    (C : Search.Certificate admissible) (D : Search.DedupCertificate α (List Nat))
    (assignments : Search.dedupCertificateValid
      (fun x y p ↦ checkIsomorphism (decode x) (decode y) p) C.candidates D = true)
    (t : ℝ) (P : Inertia → Prop) (check : α → Bool)
    (sound : ∀ x, check x = true →
      P (matrixInertia ((decode x).adjMatrix ℝ - t • (1 : Matrix (Fin n) (Fin n) ℝ))))
    (checked : D.representatives.all check = true) :
    ∀ x, admissible x →
      P (matrixInertia ((decode x).adjMatrix ℝ - t • (1 : Matrix (Fin n) (Fin n) ℝ))) := by
  apply (certifiedCover decode C D assignments).verify _ check sound _ checked
  intro x y h hp
  obtain ⟨e⟩ := h
  rw [inertia_shift_eq_of_iso e t]
  exact hp

end SpectralGraph.Graph
