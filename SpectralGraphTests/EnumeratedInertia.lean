import SpectralGraph.Graph.EnumeratedInertia

namespace SpectralGraphTests.EnumeratedInertia
open SpectralGraph SpectralGraph.Graph

/-- The reference generator's complete order-three census satisfies the
spectral predicate. This is a kernel computation, including validity checks. -/
theorem orderThree_check :
    (packedConnectedDegreeGraphs 3 2).all (fun rows ↦
      checkPackedInertiaProperty 3 rows 0 (fun I ↦ decide (I.signature ≤ 0))) = true := by
  decide +kernel

/-- A universal statement about arbitrary mathlib graphs, obtained from the
proved generator and integer checker, without a hand-supplied census. -/
theorem orderThree_signature_nonpositive (G : SimpleGraph (Fin 3))
    [DecidableRel G.Adj] (hG : G.Connected) (hd : HasDegreeAtMost G 2) :
    matrixSignature (G.adjMatrix ℝ) ≤ 0 := by
  have h := (packedConnectedDegreeGraphs_complete 3 2).verifyInertia 0
    (fun I ↦ decide (I.signature ≤ 0)) orderThree_check G hG hd
  simpa [matrixSignature] using of_decide_eq_true h

/-- An external canonicalizer's proposed two representatives and assignments. -/
def orderThreeDedup : Search.DedupCertificate PackedAdjacencyRows (List Nat) :=
  ⟨[#[2, 4, 0], #[6, 4, 0]],
    [(0, [1, 0, 2]), (0, [0, 1, 2]), (1, [0, 1, 2])]⟩

/-- Same universal theorem, now with a checked reduction from three generated
labelings to two isomorphism representatives before spectral computation. -/
theorem orderThree_signature_via_dedup (G : SimpleGraph (Fin 3))
    [DecidableRel G.Adj] (hG : G.Connected) (hd : HasDegreeAtMost G 2) :
    matrixSignature (G.adjMatrix ℝ) ≤ 0 := by
  have cover := (packedConnectedDegreeGraphs_complete 3 2).deduplicateChecked
    orderThreeDedup (by decide +kernel)
  have h := cover.verifyInertia 0 (fun I ↦ decide (I.signature ≤ 0))
    (by decide +kernel) G hG hd
  simpa [matrixSignature] using of_decide_eq_true h

#print axioms orderThree_signature_nonpositive
#print axioms orderThree_signature_via_dedup

end SpectralGraphTests.EnumeratedInertia
