import SpectralGraph.Certificate.Basic

/-!
# Congruence certificates with a checked matrix product

The producer supplies `image = A * change` and the diagonal entries. Checking
three separate products avoids repeatedly expanding a nested matrix product
for every entry. The extra data is untrusted and checked exactly.
-/

namespace SpectralGraph.Certificate
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An inverse-carrying congruence certificate with a supplied intermediate. -/
structure ProductInertiaCertificate (ι : Type*) where
  change : Matrix ι ι ℚ
  inverse : Matrix ι ι ℚ
  image : Matrix ι ι ℚ
  diagonal : ι → ℚ
  target : Inertia

/-- Each checked matrix expression has only one matrix multiplication. -/
def ProductInertiaCertificate.check (c : ProductInertiaCertificate ι)
    (A : Matrix ι ι ℚ) : Bool :=
  decide (c.inverse * c.change = 1 ∧ A * c.change = c.image ∧
    c.change.transpose * c.image = Matrix.diagonal c.diagonal ∧
    rationalDiagonalInertia c.diagonal = c.target)

/-- The auxiliary product and diagonal cannot alter the certified real inertia. -/
theorem ProductInertiaCertificate.sound (c : ProductInertiaCertificate ι)
    (A : Matrix ι ι ℚ) (h : c.check A = true) :
    matrixInertia (ratCastMatrix A) = c.target := by
  have hc : c.inverse * c.change = 1 ∧ A * c.change = c.image ∧
      c.change.transpose * c.image = Matrix.diagonal c.diagonal ∧
      rationalDiagonalInertia c.diagonal = c.target := of_decide_eq_true h
  have hd : c.change.transpose * A * c.change = Matrix.diagonal c.diagonal := by
    rw [Matrix.mul_assoc, hc.2.1, hc.2.2.1]
  apply matrixInertia_eq_of_certifiesInertiaWithInverse A c.change c.inverse c.target
  refine ⟨hc.1, ?_, ?_⟩
  · intro i j hij
    rw [hd]
    exact Matrix.diagonal_apply_ne _ hij
  · simpa [hd] using hc.2.2.2

/-- Checked certificates always account for the entire ambient dimension. -/
theorem ProductInertiaCertificate.order_eq (c : ProductInertiaCertificate ι)
    (A : Matrix ι ι ℚ) (h : c.check A = true) :
    c.target.order = Fintype.card ι := by
  rw [← c.sound A h]
  exact matrixInertia_order _

end SpectralGraph.Certificate
