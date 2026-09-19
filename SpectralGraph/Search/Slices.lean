import Mathlib.Data.List.TakeDrop

/-! Generic consecutive list slices, used to partition executable censuses. -/

namespace SpectralGraph
namespace Search

def consecutiveSlices {α : Type*} (xs : List α) : Nat → List Nat → List α
  | _, [] => []
  | start, count :: counts =>
      (xs.drop start).take count ++
        consecutiveSlices xs (start + count) counts

theorem consecutiveSlices_append_drop {α : Type*} (xs : List α)
    (start : Nat) (counts : List Nat) :
    consecutiveSlices xs start counts ++
        xs.drop (start + counts.sum) =
      xs.drop start := by
  induction counts generalizing start with
  | nil => simp [consecutiveSlices]
  | cons count counts ih =>
      simp only [consecutiveSlices, List.sum_cons]
      rw [List.append_assoc, ← Nat.add_assoc, ih]
      exact List.drop_take_append_drop xs start count

theorem consecutiveSlices_eq_drop_of_length_le {α : Type*} (xs : List α)
    (start : Nat) (counts : List Nat)
    (h : xs.length ≤ start + counts.sum) :
    consecutiveSlices xs start counts = xs.drop start := by
  have hpartition := consecutiveSlices_append_drop xs start counts
  rw [List.drop_eq_nil_iff.mpr h, List.append_nil] at hpartition
  exact hpartition

end Search
end SpectralGraph
