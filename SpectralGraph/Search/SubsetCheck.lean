import Mathlib.Data.List.Sublists
import Mathlib.Data.Finset.Card

/-! Verified streamed fixed-size subset checks and independent head buckets. -/
namespace SpectralGraph.Search
variable {α : Type*}
open List

/-- `List.all` fused with fixed-length sublist generation.  Unlike first
materializing `sublistsLen`, this keeps only the current recursion path. -/
def allSublistsLen (n : Nat) (xs : List α) (p : List α → Bool) : Bool :=
  match n, xs with
  | 0, _ => p []
  | _ + 1, [] => true
  | n + 1, x :: xs =>
      allSublistsLen (n + 1) xs p &&
        allSublistsLen n xs (fun tail ↦ p (x :: tail))
termination_by structural xs

theorem allSublistsLen_eq_all_sublistsLen
    (n : Nat) (xs : List α) (p : List α → Bool) :
    allSublistsLen n xs p = (xs.sublistsLen n).all p := by
  induction xs generalizing n p with
  | nil => cases n <;> simp [allSublistsLen]
  | cons x xs ih =>
      cases n with
      | zero => simp [allSublistsLen]
      | succ n =>
          simp [allSublistsLen, List.sublistsLen_succ_cons, ih]
          rfl

/-- The `k`th independent head-position bucket.  The definition skips preceding
buckets without evaluating them, so separate modules can certify buckets in
parallel. -/
def headBucketAt (n : Nat) : List α → (List α → Bool) → Nat → Bool
  | [], _, _ => true
  | x :: xs, p, 0 => allSublistsLen n xs (fun tail ↦ p (x :: tail))
  | _ :: xs, p, k + 1 => headBucketAt n xs p k

theorem allSublistsLen_eq_true_of_headBuckets
    {n : Nat} {xs : List α} {p : List α → Bool}
    (h : ∀ k < xs.length, headBucketAt n xs p k = true) :
    allSublistsLen (n + 1) xs p = true := by
  induction xs with
  | nil => simp [allSublistsLen]
  | cons x xs ih =>
      rw [allSublistsLen, Bool.and_eq_true]
      constructor
      · apply ih
        intro k hk
        simpa [headBucketAt] using h (k + 1) (by simp; omega)
      · simpa [headBucketAt] using h 0 (by simp)


/-- The streamed traversal checks precisely every sublist of the required length.
Repeated input elements are allowed: the statement is about positions in a list. -/
theorem allSublistsLen_eq_true_iff (n : Nat) (xs : List α) (p : List α → Bool) :
    allSublistsLen n xs p = true ↔
      ∀ ys, ys <+ xs → ys.length = n → p ys = true := by
  rw [allSublistsLen_eq_all_sublistsLen, List.all_eq_true]
  simp only [List.mem_sublistsLen, and_imp]

/-- A sound checker over streamed selections proves a universal semantic property. -/
theorem allSublistsLen_sound (n : Nat) (xs : List α) (check : List α → Bool)
    (P : List α → Prop) (sound : ∀ ys, check ys = true → P ys)
    (checked : allSublistsLen n xs check = true) :
    ∀ ys, ys <+ xs → ys.length = n → P ys := by
  intro ys hsub hlen
  exact sound ys ((allSublistsLen_eq_true_iff n xs check).mp checked ys hsub hlen)

/-- Reading all independent head buckets is equivalent to the monolithic stream. -/
theorem allSublistsLen_eq_true_iff_headBuckets (n : Nat)
    (xs : List α) (p : List α → Bool) :
    allSublistsLen (n + 1) xs p = true ↔
      ∀ k < xs.length, headBucketAt n xs p k = true := by
  constructor
  · intro h
    induction xs with
    | nil => simp
    | cons x xs ih =>
      rw [allSublistsLen, Bool.and_eq_true] at h
      intro k hk
      cases k with
      | zero => simpa [headBucketAt] using h.2
      | succ k => exact ih h.1 k (by simpa using hk)
  · exact allSublistsLen_eq_true_of_headBuckets

/-- Nonexistent buckets are vacuous. Use an exact batch manifest when missing
or repeated bucket indices must be rejected rather than silently accepted. -/
theorem headBucketAt_eq_true_of_length_le (n : Nat) (xs : List α)
    (p : List α → Bool) (k : Nat) (hk : xs.length ≤ k) :
    headBucketAt n xs p k = true := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih =>
    cases k with
    | zero => simp at hk
    | succ k => exact ih k (by simpa using hk)

/-- On a duplicate-free ground list, streamed list checking covers all finite
subsets of the requested cardinality, independently of their presentation. -/
theorem allSublistsLen_finset_sound [DecidableEq α] (n : Nat) (xs : List α)
    (hnodup : xs.Nodup) (check : Finset α → Bool) (P : Finset α → Prop)
    (sound : ∀ S, check S = true → P S)
    (checked : allSublistsLen n xs (fun ys ↦ check ys.toFinset) = true) :
    ∀ S : Finset α, S ⊆ xs.toFinset → S.card = n → P S := by
  intro S hS hcard
  let ys := xs.filter (fun x ↦ decide (x ∈ S))
  have hys : ys.toFinset = S := by
    ext x
    simp only [ys, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨List.mem_toFinset.mp (hS h), h⟩⟩
  have hylen : ys.length = n := by
    rw [← List.toFinset_card_of_nodup (hnodup.filter _), hys, hcard]
  have hp := (allSublistsLen_eq_true_iff n xs _).mp checked ys
    List.filter_sublist hylen
  rw [hys] at hp
  exact sound S hp

/-- Fixed-length sublists of a duplicate-free list enumerate precisely its
finite subsets of the specified cardinality. -/
theorem mem_toFinset_sublistsLen_iff [DecidableEq α] (xs : List α) (hnodup : xs.Nodup)
    (n : Nat) (S : Finset α) :
    S ∈ (xs.sublistsLen n).map List.toFinset ↔ S ⊆ xs.toFinset ∧ S.card = n := by
  constructor
  · intro h
    obtain ⟨ys, hys, rfl⟩ := List.mem_map.mp h
    obtain ⟨hsub, hlen⟩ := List.mem_sublistsLen.mp hys
    refine ⟨?_, ?_⟩
    · intro x hx
      exact List.mem_toFinset.mpr (hsub.subset (List.mem_toFinset.mp hx))
    · rw [List.toFinset_card_of_nodup (hnodup.sublist hsub), hlen]
  · rintro ⟨hS, hcard⟩
    let ys := xs.filter (fun x ↦ decide (x ∈ S))
    have hys : ys.toFinset = S := by
      ext x
      simp only [ys, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨List.mem_toFinset.mp (hS h), h⟩⟩
    refine List.mem_map.mpr ⟨ys, List.mem_sublistsLen.mpr ⟨List.filter_sublist, ?_⟩, hys⟩
    rw [← List.toFinset_card_of_nodup (hnodup.filter _), hys, hcard]

/-- Enumerate only nonempty subsets with size at most `maxSize`. Unlike generating
the full powerset first, this never creates a selection exceeding the bound. -/
def nonemptySubsetsAtMost [DecidableEq α] (maxSize : Nat) (xs : List α) :
    List (Finset α) :=
  (List.range maxSize).flatMap fun k ↦ (xs.sublistsLen (k + 1)).map List.toFinset

/-- Exact membership specification of bounded-size subset enumeration. -/
theorem mem_nonemptySubsetsAtMost [DecidableEq α] (maxSize : Nat) (xs : List α)
    (hnodup : xs.Nodup) (S : Finset α) :
    S ∈ nonemptySubsetsAtMost maxSize xs ↔
      S.Nonempty ∧ S ⊆ xs.toFinset ∧ S.card ≤ maxSize := by
  simp only [nonemptySubsetsAtMost, List.mem_flatMap, List.mem_range,
    mem_toFinset_sublistsLen_iff xs hnodup]
  constructor
  · rintro ⟨k, hk, hsub, hcard⟩
    exact ⟨Finset.card_pos.mp (by omega), hsub, by omega⟩
  · rintro ⟨hne, hsub, hcard⟩
    have hpos := Finset.card_pos.mpr hne
    exact ⟨S.card - 1, by omega, hsub, by omega⟩

/-- Stream all nonempty bounded-size selections without materializing the
selection family. The supplied checker is evaluated on one selection at a time. -/
def allNonemptySubsetsAtMost [DecidableEq α] (maxSize : Nat) (xs : List α)
    (check : Finset α → Bool) : Bool :=
  (List.range maxSize).all fun k ↦
    allSublistsLen (k + 1) xs (fun ys ↦ check ys.toFinset)

/-- The streamed checker agrees with the bounded-size list specification. -/
theorem allNonemptySubsetsAtMost_eq_all [DecidableEq α] (maxSize : Nat)
    (xs : List α) (check : Finset α → Bool) :
    allNonemptySubsetsAtMost maxSize xs check =
      (nonemptySubsetsAtMost maxSize xs).all check := by
  simp [allNonemptySubsetsAtMost, nonemptySubsetsAtMost,
    allSublistsLen_eq_all_sublistsLen, List.all_flatMap, List.all_map, Function.comp_def]

end SpectralGraph.Search


