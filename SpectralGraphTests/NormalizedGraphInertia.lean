import SpectralGraph.Graph.NormalizedInertia

namespace SpectralGraphTests.NormalizedGraphInertia
open SpectralGraph SpectralGraph.Graph SpectralGraph.Certificate

-- The same path in oriented and full symmetric storage.
example : checkPackedNormalizedInertia 3 #[2, 4, 0] 0 ⟨1, 1, 1⟩ = true := by decide +kernel
example : checkPackedNormalizedInertia 3 #[2, 5, 2] 0 ⟨1, 1, 1⟩ = true := by decide +kernel
example : checkPackedNormalizedInertia 3 #[2, 4, 0] (-1) ⟨2, 0, 1⟩ = true := by decide +kernel

-- K₄: integral thresholds exercise negative pivots, normalization, and an
-- eigenvalue of multiplicity three exactly at the threshold.
example : checkPackedNormalizedInertia 4 #[14, 12, 8, 0] 0 ⟨1, 0, 3⟩ = true := by decide +kernel
example : checkPackedNormalizedInertia 4 #[14, 12, 8, 0] (-1) ⟨1, 3, 0⟩ = true := by decide +kernel
example : checkPackedNormalizedInertia 4 #[14, 12, 8, 0] 3 ⟨0, 1, 3⟩ = true := by decide +kernel

-- C₄ at and between its extreme eigenvalues.
example : checkPackedNormalizedInertia 4 #[10, 4, 8, 0] 0 ⟨1, 2, 1⟩ = true := by decide +kernel
example : checkPackedNormalizedInertia 4 #[10, 4, 8, 0] 2 ⟨0, 1, 3⟩ = true := by decide +kernel
example : checkPackedNormalizedInertia 4 #[10, 4, 8, 0] (-2) ⟨3, 1, 0⟩ = true := by decide +kernel

example : matrixInertia ((graphOfPackedRows 4 #[14, 12, 8, 0]).adjMatrix ℝ -
    (-1 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ)) = ⟨1, 3, 0⟩ := by
  simpa using checkPackedNormalizedInertia_sound 4 #[14, 12, 8, 0] (-1)
    ⟨1, 3, 0⟩ (by decide +kernel)

-- Exact representation boundaries and false claims are rejected.
example : checkPackedNormalizedInertia 3 #[2, 4] 0 ⟨1, 1, 1⟩ = false := by decide +kernel
example : checkPackedNormalizedInertia 3 #[2, 4, 0, 0] 0 ⟨1, 1, 1⟩ = false := by decide +kernel
example : checkPackedNormalizedInertia 3 #[3, 4, 0] 0 ⟨1, 1, 1⟩ = false := by decide +kernel
example : checkPackedNormalizedInertia 3 #[10, 4, 0] 0 ⟨1, 1, 1⟩ = false := by decide +kernel
example : checkPackedNormalizedInertia 3 #[2, 4, 0] 0 ⟨3, 0, 0⟩ = false := by decide +kernel
example : checkPackedNormalizedInertia 0 #[] (-7) ⟨0, 0, 0⟩ = true := by decide +kernel
example : checkPackedNormalizedInertia 0 #[0] 0 ⟨0, 0, 0⟩ = false := by decide +kernel
-- Asymmetric raw matrices are invalid. Asymmetric packed rows above are valid
-- oriented edge encodings, whose constructed matrix is symmetric.
example : (⟨2, #[0, 1, 0, 0]⟩ : DenseIntMatrix).checkNormalizedInertia ⟨1, 0, 1⟩ = false := by
  decide +kernel

def atMostOneNegative (I : Inertia) : Bool := decide (I.neg ≤ 1)

example : checkPackedNormalizedInertiaProperty 4 #[10, 4, 8, 0] 0 atMostOneNegative = true := by
  decide +kernel
example : checkPackedNormalizedInertiaProperty 4 #[14, 12, 8, 0] 0 atMostOneNegative = false := by
  decide +kernel
example : checkPackedNormalizedInertiaProperty 3 #[2, 4] 0 (fun _ ↦ true) = false := by
  decide +kernel

-- A finite family check exposes semantic bounds on every supplied graph.
example : ∀ rows ∈ [#[10, 4, 8, 0], #[2, 0, 0, 0]],
    (matrixInertia ((graphOfPackedRows 4 rows).adjMatrix ℝ -
      (0 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ))).neg ≤ 1 := by
  intro rows hmem
  have hall : [#[10, 4, 8, 0], #[2, 0, 0, 0]].all
      (fun r ↦ checkPackedNormalizedInertiaProperty 4 r 0 atMostOneNegative) = true := by
    decide +kernel
  have hs := checkPackedNormalizedInertiaProperty_sound 4 rows 0 atMostOneNegative
    (List.all_eq_true.mp hall rows hmem)
  simpa [atMostOneNegative] using hs

#print axioms checkPackedNormalizedInertia_sound
#print axioms checkPackedNormalizedInertia_eq_checkPackedInertia
#print axioms checkPackedNormalizedInertiaProperty_sound

end SpectralGraphTests.NormalizedGraphInertia
