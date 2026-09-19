import SpectralGraph.Certificate.Basic
import SpectralGraph.Inertia.OrderedSpectrum

/-!
# Exact eigenvalue interval certificates

Two rational shifted-inertia certificates count the eigenvalues in `(a,b]`.
No floating-point eigenvalue approximation or eigenvector computation is
trusted. The semantic theorem requires Hermitian input and counts repeated
eigenvalues with their multiplicities.
-/

namespace SpectralGraph.Certificate
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- Scalar shifts commute with exact rational embedding. -/
theorem ratCast_shift (A : Matrix ι ι ℚ) (t : ℚ) :
    ratCastMatrix (A - t • 1) = ratCastMatrix A - (t : ℝ) • 1 := by
  ext i j
  by_cases hij : i = j <;>
    simp [ratCastMatrix, hij]

/-- Check an interval count by exact inertia at its two endpoints. -/
def checkEigenvaluesIoc (A : Matrix ι ι ℚ) (a b : ℚ)
    (left right : InertiaCertificate ι) (count : Nat) : Bool :=
  decide (a ≤ b) && left.check (A - a • 1) && right.check (A - b • 1) &&
    decide (count + right.target.pos = left.target.pos)

/-- Accepted endpoint certificates give the exact number of eigenvalues in
the half-open interval, including when endpoints are eigenvalues. -/
theorem checkEigenvaluesIoc_sound (A : Matrix ι ι ℚ)
    (hA : (ratCastMatrix A).IsHermitian) (a b : ℚ)
    (left right : InertiaCertificate ι) (count : Nat)
    (h : checkEigenvaluesIoc A a b left right count = true) :
    (Finset.univ.filter fun i ↦ (a : ℝ) < hA.eigenvalues i ∧ hA.eigenvalues i ≤ (b : ℝ)).card = count := by
  have hc : a ≤ b ∧ left.check (A - a • 1) = true ∧
      right.check (A - b • 1) = true ∧ count + right.target.pos = left.target.pos := by
    simpa [checkEigenvaluesIoc, Bool.and_assoc] using h
  have hl : matrixInertia (ratCastMatrix A - (a : ℝ) • 1) = left.target := by
    rw [← ratCast_shift]
    exact left.sound _ hc.2.1
  have hr : matrixInertia (ratCastMatrix A - (b : ℝ) • 1) = right.target := by
    rw [← ratCast_shift]
    exact right.sound _ hc.2.2.1
  have hi := Inertia.eigenvalue_count_Ioc_add_pos_eq (ratCastMatrix A) hA
    (a : ℝ) (b : ℝ) (by exact_mod_cast hc.1)
  rw [hl, hr] at hi
  omega

/-- Check a bracket for the zero-based `k`th largest eigenvalue. The index bound
is checked explicitly, so malformed external indices are rejected. -/
def checkEigenvalueBracket (A : Matrix ι ι ℚ) (a b : ℚ)
    (left right : InertiaCertificate ι) (k : Nat) : Bool :=
  decide (k < Fintype.card ι) && decide (a ≤ b) &&
    left.check (A - a • 1) && right.check (A - b • 1) &&
    decide (k < left.target.pos ∧ right.target.pos ≤ k)

/-- Accepted brackets refer to mathlib's descending eigenvalue list. -/
theorem checkEigenvalueBracket_sound (A : Matrix ι ι ℚ)
    (hA : (ratCastMatrix A).IsHermitian) (a b : ℚ)
    (left right : InertiaCertificate ι) (k : Fin (Fintype.card ι))
    (h : checkEigenvalueBracket A a b left right k.val = true) :
    (a : ℝ) < hA.eigenvalues₀ k ∧ hA.eigenvalues₀ k ≤ (b : ℝ) := by
  have hc : k.val < Fintype.card ι ∧ a ≤ b ∧
      left.check (A - a • 1) = true ∧ right.check (A - b • 1) = true ∧
      (k.val < left.target.pos ∧ right.target.pos ≤ k.val) := by
    simpa [checkEigenvalueBracket, Bool.and_assoc] using h
  apply (Inertia.eigenvalues₀_mem_Ioc_iff _ hA _ _ k).mpr
  have hl := left.sound _ hc.2.2.1
  have hr := right.sound _ hc.2.2.2.1
  rw [ratCast_shift] at hl hr
  rw [hl, hr]
  exact hc.2.2.2.2

end SpectralGraph.Certificate
