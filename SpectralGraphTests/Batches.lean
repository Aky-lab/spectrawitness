import SpectralGraph.Search.Batches

namespace SpectralGraphTests.Batches
open SpectralGraph.Search

def manifest : List Batch := [⟨0, 2⟩, ⟨2, 3⟩]
example : batchManifestValid 5 manifest = true := by decide
-- Strict contract: gaps, overlap, missing suffix, overshoot, empty batch and disorder fail.
example : batchManifestValid 5 [⟨0, 2⟩, ⟨3, 2⟩] = false := by decide
example : batchManifestValid 5 [⟨0, 3⟩, ⟨2, 3⟩] = false := by decide
example : batchManifestValid 5 [⟨0, 2⟩] = false := by decide
example : batchManifestValid 5 [⟨0, 6⟩] = false := by decide
example : batchManifestValid 5 [⟨0, 0⟩, ⟨0, 5⟩] = false := by decide
example : batchManifestValid 5 [⟨2, 3⟩, ⟨0, 2⟩] = false := by decide
example : batchManifestValid 0 [] = true := by decide
example : batchManifestValid 0 [⟨0, 0⟩] = false := by decide
example : checkBatches 5 manifest (fun i ↦ decide (i < 4)) = false := by decide

-- Independent streamed head buckets combine through an exactly checked manifest.
example : allSublistsLen 2 (List.range 5) (fun ys ↦ decide (ys.sum ≤ 7)) = true := by
  apply allSublistsLen_of_checked_head_batches 1 (List.range 5) _ manifest
  decide

-- A manifest omitting a failing bucket is rejected, even when supplied buckets all pass.
example : checkBatches 3 [⟨0, 1⟩]
    (headBucketAt 1 [1, 2, 3] (fun ys ↦ decide (ys.sum ≤ 4))) = false := by decide

#print axioms batchManifestValid_indices
#print axioms checkBatches_eq_true_iff
#print axioms allSublistsLen_of_checked_head_batches
end SpectralGraphTests.Batches
