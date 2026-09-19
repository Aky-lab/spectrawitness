import SpectralGraph.Search.SubsetCheck
import Mathlib.Data.List.Range

/-! Strict, executable batch manifests for independently checked searches.
An accepted manifest is an exact ordered partition: positive lengths, no gaps,
no overlaps, no missing final suffix, and no out-of-range work. -/
namespace SpectralGraph.Search

/-- A half-open interval of candidate indices `[start, start + count)`. -/
structure Batch where
  start : Nat
  count : Nat
  deriving DecidableEq, Repr

/-- Candidate indices belonging to a batch, in traversal order. -/
def Batch.indices (batch : Batch) : List Nat := List.range' batch.start batch.count

/-- Validate a manifest suffix against its expected start and global endpoint. -/
def batchManifestValidFrom (total : Nat) : Nat → List Batch → Bool
  | start, [] => start == total
  | start, batch :: rest =>
      decide (batch.start = start ∧ 0 < batch.count ∧ batch.start + batch.count ≤ total) &&
        batchManifestValidFrom total (start + batch.count) rest

/-- Strict manifest validation. Empty searches require an empty manifest. -/
def batchManifestValid (total : Nat) (batches : List Batch) : Bool :=
  batchManifestValidFrom total 0 batches

/-- Short-circuit an interval traversal without allocating its index list. -/
def allRange (start : Nat) : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | count + 1, check => check start && allRange (start + 1) count check

/-- The streamed interval traversal agrees with its ordinary list specification. -/
theorem allRange_eq_all_range' (start count : Nat) (check : Nat → Bool) :
    allRange start count check = (List.range' start count).all check := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp [allRange, List.range', ih]

/-- Evaluate one batch without materializing its index list. -/
def Batch.check (batch : Batch) (check : Nat → Bool) : Bool :=
  allRange batch.start batch.count check

@[simp] theorem Batch.check_eq_all (batch : Batch) (check : Nat → Bool) :
    batch.check check = batch.indices.all check :=
  allRange_eq_all_range' _ _ _

/-- Validate the partition and evaluate every batch against the supplied checker.
No externally supplied success flag is accepted as evidence. -/
def checkBatches (total : Nat) (batches : List Batch) (check : Nat → Bool) : Bool :=
  batchManifestValid total batches && batches.all (fun batch ↦ batch.check check)

/-- Acceptance identifies the concatenated batch indices with the entire
requested interval. This proves exact coverage and exact multiplicity together. -/
theorem batchManifestValidFrom_indices {total start : Nat} {batches : List Batch}
    (h : batchManifestValidFrom total start batches = true) :
    batches.flatMap Batch.indices = List.range' start (total - start) := by
  induction batches generalizing start with
  | nil =>
    have hs : start = total := by simpa [batchManifestValidFrom] using h
    subst start
    simp
  | cons batch rest ih =>
    simp only [batchManifestValidFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hs, hpositive, hbound⟩, hrest⟩ := h
    simp only [List.flatMap_cons, Batch.indices]
    rw [ih hrest, hs, List.range'_append_1]
    congr 1
    omega

/-- An accepted manifest checks each index exactly once. -/
theorem batchManifestValid_indices {total : Nat} {batches : List Batch}
    (h : batchManifestValid total batches = true) :
    batches.flatMap Batch.indices = List.range total := by
  simpa [List.range_eq_range'] using batchManifestValidFrom_indices h

/-- Exact coverage also prohibits any duplicated candidate index. -/
theorem batchManifestValid_nodup {total : Nat} {batches : List Batch}
    (h : batchManifestValid total batches = true) :
    (batches.flatMap Batch.indices).Nodup := by
  rw [batchManifestValid_indices h]
  exact List.nodup_range

/-- Every accepted interval is nonempty and lies within the requested search. -/
theorem batchManifestValidFrom_bounds {total start : Nat} {batches : List Batch}
    (h : batchManifestValidFrom total start batches = true) :
    ∀ batch ∈ batches, 0 < batch.count ∧ batch.start + batch.count ≤ total := by
  induction batches generalizing start with
  | nil => simp
  | cons b bs ih =>
    simp only [batchManifestValidFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    intro batch hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact h.1.2
    · exact ih h.2 batch hb

/-- Independent kernel proofs for every batch combine to a proof for every
candidate, once the complete manifest itself has been checked. -/
theorem all_of_checked_batches {total : Nat} {batches : List Batch} (check : Nat → Bool)
    (valid : batchManifestValid total batches = true)
    (checked : ∀ batch ∈ batches, batch.check check = true) :
    ∀ i < total, check i = true := by
  have hall : (batches.flatMap Batch.indices).all check = true := by
    rw [List.all_flatMap, List.all_eq_true]
    simpa using checked
  rw [batchManifestValid_indices valid] at hall
  intro i hi
  exact List.all_eq_true.mp hall i (List.mem_range.mpr hi)

/-- Soundness of the combined executable manifest-and-batch checker. -/
theorem checkBatches_sound {total : Nat} {batches : List Batch} (check : Nat → Bool)
    (checked : checkBatches total batches check = true) :
    ∀ i < total, check i = true := by
  rw [checkBatches, Bool.and_eq_true] at checked
  exact all_of_checked_batches check checked.1 (List.all_eq_true.mp checked.2)

/-- A well-formed manifest accepts exactly when every candidate passes. -/
theorem checkBatches_eq_true_iff {total : Nat} {batches : List Batch} (check : Nat → Bool) :
    checkBatches total batches check = true ↔
      batchManifestValid total batches = true ∧ ∀ i < total, check i = true := by
  constructor
  · intro h
    have hparts := h
    rw [checkBatches, Bool.and_eq_true] at hparts
    exact ⟨hparts.1, checkBatches_sound check h⟩
  · rintro ⟨hvalid, hcheck⟩
    rw [checkBatches, Bool.and_eq_true]
    refine ⟨hvalid, ?_⟩
    have hall : (batches.flatMap Batch.indices).all check = true := by
      rw [batchManifestValid_indices hvalid, List.all_eq_true]
      intro i hi
      exact hcheck i (List.mem_range.mp hi)
    simpa [List.all_flatMap] using hall

/-- Checker soundness transports the batched computation to a semantic property. -/
theorem checkBatches_verify {total : Nat} {batches : List Batch}
    (check : Nat → Bool) (P : Nat → Prop)
    (sound : ∀ i < total, check i = true → P i)
    (checked : checkBatches total batches check = true) :
    ∀ i < total, P i := by
  intro i hi
  exact sound i hi (checkBatches_sound check checked i hi)

/-- Verified manifests can distribute fixed-size subset checks by the position
of their first element. Every required head bucket must be present exactly once. -/
theorem allSublistsLen_of_checked_head_batches {α : Type*}
    (n : Nat) (xs : List α) (check : List α → Bool) (batches : List Batch)
    (checked : checkBatches xs.length batches (headBucketAt n xs check) = true) :
    allSublistsLen (n + 1) xs check = true :=
  allSublistsLen_eq_true_of_headBuckets (checkBatches_sound _ checked)

end SpectralGraph.Search

