import SpectralGraph.Search.Exhaustive

/-!
# Generic certificate-checked duplicate elimination

An optimized or entirely untrusted discovery procedure may propose a short
representative list and, for every input, an index plus a certificate relating
that input to its representative.  The checker below validates those claims.
No property of the discovery algorithm or its keys is used by downstream
proofs.
-/

namespace SpectralGraph
namespace Search

/-- Proposed representatives together with one representative index and
relation certificate for every original candidate. -/
structure DedupCertificate (α : Type*) (κ : Type*) where
  representatives : List α
  assignments : List (Nat × κ)

/-- Check assignments structurally, so a successful check also certifies that
there is exactly one assignment for every input. -/
def dedupAssignmentsValid {α κ : Type*}
    (check : α → α → κ → Bool) (representatives : List α) :
    List α → List (Nat × κ) → Bool
  | [], [] => true
  | x :: xs, (i, cert) :: assignments =>
      match representatives[i]? with
      | some representative =>
          check x representative cert &&
            dedupAssignmentsValid check representatives xs assignments
      | none => false
  | _, _ => false

/-- Validate the linear coverage map.  Properties required of the retained
representatives (for example connectedness) are checked separately; including
a quadratic representative-membership scan here would make large certificates
needlessly expensive. -/
def dedupCertificateValid {α κ : Type*}
    (check : α → α → κ → Bool) (candidates : List α)
    (certificate : DedupCertificate α κ) : Bool :=
  dedupAssignmentsValid check certificate.representatives candidates
    certificate.assignments

theorem dedupAssignmentsValid_sound {α κ : Type*}
    (check : α → α → κ → Bool) (representatives : List α)
    {candidates : List α} {assignments : List (Nat × κ)}
    (hvalid : dedupAssignmentsValid check representatives candidates assignments = true) :
    ∀ x ∈ candidates,
      ∃ representative ∈ representatives, ∃ cert,
        check x representative cert = true := by
  induction candidates generalizing assignments with
  | nil => simp
  | cons x xs ih =>
      cases assignments with
      | nil => simp [dedupAssignmentsValid] at hvalid
      | cons assignment assignments =>
          rcases assignment with ⟨i, cert⟩
          cases hget : representatives[i]? with
          | none => simp [dedupAssignmentsValid, hget] at hvalid
          | some representative =>
              have hboth :
                  check x representative cert = true ∧
                    dedupAssignmentsValid check representatives xs assignments = true := by
                simpa [dedupAssignmentsValid, hget, Bool.and_eq_true] using hvalid
              intro y hy
              simp only [List.mem_cons] at hy
              rcases hy with rfl | hy
              · refine ⟨representative, ?_, cert, hboth.1⟩
                exact List.mem_of_getElem? hget
              · exact ih hboth.2 y hy

/-- Soundness of generic certified deduplication.  Every original candidate
is related by a successfully checked certificate to one of the retained
representatives. -/
theorem dedupCertificateValid_sound {α κ : Type*}
    (check : α → α → κ → Bool) (R : α → α → Prop)
    (hcheck : ∀ x y cert, check x y cert = true → R x y)
    (candidates : List α) (certificate : DedupCertificate α κ)
    (hvalid : dedupCertificateValid check candidates certificate = true) :
    ∀ x ∈ candidates,
      ∃ representative ∈ certificate.representatives, R x representative := by
  intro x hx
  obtain ⟨representative, hrepresentative, cert, hcert⟩ :=
    dedupAssignmentsValid_sound check certificate.representatives hvalid x hx
  exact ⟨representative, hrepresentative, hcheck x representative cert hcert⟩

end Search
end SpectralGraph
