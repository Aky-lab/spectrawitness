import SpectralGraph.Search.Dedup
import SpectralGraph.Search.Slices

/-!
# Exhaustive search through certified representatives

Coverage is directional: every admissible input reduces to a representative.
No equivalence relation, canonical labeling, minimality, uniqueness, or
admissibility of the representatives is assumed. The property being checked
must transport backwards along the chosen relation.
-/

namespace SpectralGraph.Search

variable {α : Type*}

/-- A finite cover of admissible objects along a relation. -/
structure Cover (admissible : α → Prop) (R : α → α → Prop) where
  representatives : List α
  exhaustive : ∀ x, admissible x → ∃ y ∈ representatives, R x y

/-- Exact enumeration is the equality instance of relational coverage. -/
def Certificate.toCover {admissible : α → Prop} (C : Certificate admissible) :
    Cover admissible Eq where
  representatives := C.candidates
  exhaustive x hx := ⟨x, C.exhaustive x hx, rfl⟩

/-- Certified deduplication preserves coverage, including multiple successive
reductions. Only transitivity and soundness of the relation checker are used. -/
def Cover.deduplicate {admissible : α → Prop} {R : α → α → Prop}
    (C : Cover admissible R) {κ : Type*}
    (check : α → α → κ → Bool)
    (sound : ∀ x y c, check x y c = true → R x y)
    (trans : ∀ {x y z}, R x y → R y z → R x z)
    (D : DedupCertificate α κ)
    (valid : dedupCertificateValid check C.representatives D = true) :
    Cover admissible R where
  representatives := D.representatives
  exhaustive x hx := by
    obtain ⟨y, hy, hxy⟩ := C.exhaustive x hx
    obtain ⟨z, hz, hyz⟩ := dedupCertificateValid_sound check R sound _ D valid y hy
    exact ⟨z, hz, trans hxy hyz⟩

/-- Lift a sound Boolean check on representatives to every admissible object.
Checker completeness is unnecessary: false negatives may prevent acceptance
but cannot prove a false universal statement. -/
theorem Cover.verify {admissible : α → Prop} {R : α → α → Prop}
    (C : Cover admissible R) (P : α → Prop) (check : α → Bool)
    (sound : ∀ x, check x = true → P x)
    (transport : ∀ x y, R x y → P y → P x)
    (checked : C.representatives.all check = true) :
    ∀ x, admissible x → P x := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := C.exhaustive x hx
  exact transport x y hxy (sound y ((List.all_eq_true.mp checked) y hy))

/-- Independently verified batches cover the full list when their total
length reaches its end. Batches may be empty or overrun the end. -/
theorem all_of_consecutiveSlices {xs : List α} (counts : List Nat)
    (cover : xs.length ≤ counts.sum) (check : α → Bool)
    (checked : (consecutiveSlices xs 0 counts).all check = true) :
    xs.all check = true := by
  have h := consecutiveSlices_eq_drop_of_length_le xs 0 counts (by simpa using cover)
  simpa [h] using checked

end SpectralGraph.Search
