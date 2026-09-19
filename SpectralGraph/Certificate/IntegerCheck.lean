import SpectralGraph.Certificate.IntegerSound

/-!
# Checked dense integer input

The internal matrix interpretation pads missing entries with zeros. This
public boundary instead rejects malformed lengths and nonsymmetric input
before accepting a claimed inertia. Integer elimination itself is proved
correct, so acceptance does not rerun a rational diagonalizer.
-/

namespace SpectralGraph.Certificate

/-- Validate the representation and compare the proved algorithm to a claim. -/
def DenseIntMatrix.checkInertia (A : DenseIntMatrix) (target : Inertia) : Bool :=
  decide (A.entries.size = A.order * A.order) &&
    decide (∀ i j : Fin A.order, A.entry i j = A.entry j i) &&
    decide (discoverIntegerInertiaV2 A = target)

/-- Accepted integer input has the claimed semantic real inertia. -/
theorem DenseIntMatrix.checkInertia_sound (A : DenseIntMatrix) (target : Inertia)
    (h : A.checkInertia target = true) :
    matrixInertia (ratCastMatrix A.toRatMatrix) = target := by
  simp only [DenseIntMatrix.checkInertia, Bool.and_eq_true, decide_eq_true_eq] at h
  have hs : A.toRatMatrix.IsSymm := by
    ext i j
    change (A.entry j i : ℚ) = (A.entry i j : ℚ)
    rw [h.1.2 j i]
  exact (matrixInertia_eq_discoverIntegerInertiaV2 A hs).trans h.2

/-- Acceptance guarantees that no implicit padding or ignored tail is used. -/
theorem DenseIntMatrix.checkInertia_size (A : DenseIntMatrix) (target : Inertia)
    (h : A.checkInertia target = true) : A.entries.size = A.order * A.order := by
  simp only [DenseIntMatrix.checkInertia, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

end SpectralGraph.Certificate
