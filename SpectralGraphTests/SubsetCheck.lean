import SpectralGraph.Search.SubsetCheck
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace SpectralGraphTests.SubsetCheck
open SpectralGraph.Search

-- The empty selection is checked once, even on empty input.
example : allSublistsLen 0 ([] : List Nat) (fun _ ↦ false) = false := by decide
-- There are no selections when the requested cardinality exceeds the input length.
example : allSublistsLen 4 [1, 2, 3] (fun _ ↦ false) = true := by decide
-- Duplicate elements refer to distinct positions, so the list semantics remain exact.
example : allSublistsLen 2 [1, 1] (fun ys ↦ decide (ys = [1, 1])) = true := by decide
example : allSublistsLen 2 [1, 2, 3] (fun ys ↦ decide (ys.sum ≤ 4)) = false := by decide
example : headBucketAt 1 [1, 2, 3] (fun ys ↦ decide (ys.sum ≤ 4)) 0 = true := by decide
example : headBucketAt 1 [1, 2, 3] (fun ys ↦ decide (ys.sum ≤ 4)) 1 = false := by decide
example : headBucketAt 1 [1, 2, 3] (fun _ ↦ false) 3 = true := by decide

-- Transfer actual streamed Boolean evaluation to a statement about every finite subset.
example (S : Finset Nat) (hS : S ⊆ (List.range 6).toFinset) (hcard : S.card = 3) :
    S.sum id ≤ 12 := by
  apply allSublistsLen_finset_sound 3 (List.range 6) List.nodup_range
    (fun S ↦ decide (S.sum id ≤ 12)) (fun S ↦ S.sum id ≤ 12)
    (fun _ h ↦ of_decide_eq_true h) (by decide) S hS hcard

#print axioms allSublistsLen_finset_sound
#print axioms allSublistsLen_eq_true_iff_headBuckets
end SpectralGraphTests.SubsetCheck
