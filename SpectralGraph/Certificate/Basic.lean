import SpectralGraph.Certificate.ExactInertia

/-!
# Portable rational congruence certificates

The producer may be any external program. A certificate is plain rational
data; acceptance recomputes a left inverse, diagonality, and sign counts.
No symmetry assumption is needed for soundness about quadratic-form inertia.
For spectral applications the caller uses a symmetric matrix.
-/

namespace SpectralGraph.Certificate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Data supplied by an untrusted congruence producer. -/
structure InertiaCertificate (ι : Type*) where
  change : Matrix ι ι ℚ
  inverse : Matrix ι ι ℚ
  target : Inertia

/-- Exact executable acceptance test, including the claimed inertia. -/
def InertiaCertificate.check (c : InertiaCertificate ι)
    (A : Matrix ι ι ℚ) : Bool :=
  decide (c.inverse * c.change = 1 ∧
    (∀ i j, i ≠ j → (c.change.transpose * A * c.change) i j = 0) ∧
    rationalDiagonalInertia (fun i ↦ (c.change.transpose * A * c.change) i i) =
      c.target)

/-- Acceptance implies semantic real inertia, independently of the producer. -/
theorem InertiaCertificate.sound (c : InertiaCertificate ι)
    (A : Matrix ι ι ℚ) (h : c.check A = true) :
    matrixInertia (ratCastMatrix A) = c.target := by
  apply matrixInertia_eq_of_certifiesInertiaWithInverse A c.change c.inverse c.target
  simpa [InertiaCertificate.check, CertifiesInertiaWithInverse] using h

/-- A certificate with the wrong total dimension cannot be accepted. -/
theorem InertiaCertificate.order_eq (c : InertiaCertificate ι)
    (A : Matrix ι ι ℚ) (h : c.check A = true) :
    c.target.order = Fintype.card ι := by
  rw [← c.sound A h]
  exact matrixInertia_order _

end SpectralGraph.Certificate
