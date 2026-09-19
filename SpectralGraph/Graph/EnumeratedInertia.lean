import SpectralGraph.Graph.PackedEnumeration
import SpectralGraph.Graph.PackedInertia
import SpectralGraph.Graph.InertiaIso
import SpectralGraph.Graph.Search

/-!
# From complete executable graph enumeration to spectral theorems

The coverage theorem may come from the reference generator, certified
deduplication, or another proved enumerator. Strict packed checks and
isomorphism invariance connect it to a universal real inertia statement.
-/

namespace SpectralGraph.Graph

/-- Reduce a proved covering census using untrusted representative indices
and strict permutation certificates. The resulting cover is directly usable
by `CoversConnectedDegree.verifyInertia`. -/
theorem CoversConnectedDegree.deduplicateChecked {n d : Nat}
    {rows : List PackedAdjacencyRows} (cover : CoversConnectedDegree n d rows)
    (certificate : Search.DedupCertificate PackedAdjacencyRows (List Nat))
    (checked : Search.dedupCertificateValid
      (fun a b p ↦ checkIsomorphism (graphOfPackedRows n a) (graphOfPackedRows n b) p)
      rows certificate = true) :
    CoversConnectedDegree n d certificate.representatives := by
  apply cover.deduplicate
  exact Search.dedupCertificateValid_sound _ _
    (fun a b p h ↦ checkIsomorphism_sound (graphOfPackedRows n a) (graphOfPackedRows n b) p h)
    rows certificate checked

/-- A checked inertia predicate on a covering census holds for every connected
graph of that order and degree bound. No external completeness assumption
is required when the cover comes from `packedConnectedDegreeGraphs_complete`. -/
theorem CoversConnectedDegree.verifyInertia {n d : Nat}
    {rows : List PackedAdjacencyRows} (cover : CoversConnectedDegree n d rows)
    (t : Int) (test : Inertia → Bool)
    (checked : rows.all (fun r ↦ checkPackedInertiaProperty n r t test) = true)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (connected : G.Connected) (degree : HasDegreeAtMost G d) :
    test (matrixInertia (G.adjMatrix ℝ - (t : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))) = true := by
  obtain ⟨r, hr, ⟨e⟩⟩ := cover G connected degree
  have h := checkPackedInertiaProperty_sound n r t test
    ((List.all_eq_true.mp checked) r hr)
  rw [inertia_shift_eq_of_iso e]
  exact h

end SpectralGraph.Graph
