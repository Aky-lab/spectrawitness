import SpectralGraph.Certificate.NormalizedInteger
import SpectralGraph.Inertia.OrderedSpectrum

/-!
# Integer eigenvalue certificates at rational thresholds

For `t = p/q`, with `q > 0`, the integer matrix `qA - pI` has the same
inertia as the real shifted matrix `A - tI`. Normalized integer elimination
therefore certifies rational spectral intervals without change-of-basis data.
-/

namespace SpectralGraph.Certificate

/-- Clear the positive denominator of a rational scalar shift. -/
def DenseIntMatrix.rationalShift (A : DenseIntMatrix) (t : ℚ) : DenseIntMatrix :=
  DenseIntMatrix.ofFn A.order fun i j ↦
    (t.den : Int) * A.entry i j - if i = j then t.num else 0

@[simp] theorem DenseIntMatrix.rationalShift_order (A : DenseIntMatrix) (t : ℚ) :
    (A.rationalShift t).order = A.order := rfl

/-- Denominator clearing is exactly positive real rescaling of a shifted matrix. -/
theorem DenseIntMatrix.rationalShift_cast (A : DenseIntMatrix) (t : ℚ) :
    ratCastMatrix (A.rationalShift t).toRatMatrix =
      (t.den : ℝ) • (ratCastMatrix A.toRatMatrix -
        (t : ℝ) • (1 : Matrix (Fin A.order) (Fin A.order) ℝ)) := by
  refine Matrix.ext fun (i : Fin A.order) (j : Fin A.order) ↦ ?_
  have hd : (t.den : ℝ) ≠ 0 := by exact_mod_cast t.den_nz
  have ht : (t.den : ℝ) * (t : ℝ) = (t.num : ℝ) := by
    rw [Rat.cast_def]
    field_simp
  change (((DenseIntMatrix.ofFn A.order (fun i j ↦
    (t.den : Int) * A.entry i j - if i = j then t.num else 0)).entry i j : Int) : ℝ) = _
  rw [DenseIntMatrix.entry_ofFn A.order _ i j i.isLt j.isLt]
  have hij : (i.val = j.val) ↔ i = j := Fin.val_inj
  by_cases heq : i = j <;>
    simp [ratCastMatrix, DenseIntMatrix.toRatMatrix, hij, heq,
      mul_sub, ht]

/-- Integer denominator clearing preserves all shifted inertia indices. -/
theorem DenseIntMatrix.matrixInertia_rationalShift (A : DenseIntMatrix) (t : ℚ) :
    matrixInertia (ratCastMatrix (A.rationalShift t).toRatMatrix) =
      matrixInertia (ratCastMatrix A.toRatMatrix - (t : ℝ) • 1) := by
  rw [A.rationalShift_cast]
  exact Inertia.matrixInertia_pos_smul _ (by exact_mod_cast t.den_pos)

/-- Certify inertia at an arbitrary rational threshold. Original storage must
be well formed; the normalized shifted checker also checks symmetry. -/
def DenseIntMatrix.checkInertiaAt (A : DenseIntMatrix) (t : ℚ) (target : Inertia) : Bool :=
  decide (A.entries.size = A.order * A.order) &&
    (A.rationalShift t).checkNormalizedInertia target

theorem DenseIntMatrix.checkInertiaAt_sound (A : DenseIntMatrix) (t : ℚ) (target : Inertia)
    (h : A.checkInertiaAt t target = true) :
    matrixInertia (ratCastMatrix A.toRatMatrix - (t : ℝ) • 1) = target := by
  have hc : decide (A.entries.size = A.order * A.order) = true ∧
      (A.rationalShift t).checkNormalizedInertia target = true := by
    simpa only [DenseIntMatrix.checkInertiaAt, Bool.and_eq_true] using h
  rw [← A.matrixInertia_rationalShift t]
  exact (A.rationalShift t).checkNormalizedInertia_sound target hc.2

theorem DenseIntMatrix.checkInertiaAt_size (A : DenseIntMatrix) (t : ℚ) (target : Inertia)
    (h : A.checkInertiaAt t target = true) : A.entries.size = A.order * A.order := by
  simp only [DenseIntMatrix.checkInertiaAt, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- Count eigenvalues in `(a,b]` by two normalized integer computations at
arbitrary rational endpoints. No congruence matrices are needed. -/
def DenseIntMatrix.checkEigenvaluesIoc (A : DenseIntMatrix) (a b : ℚ)
    (left right : Inertia) (count : Nat) : Bool :=
  decide (a ≤ b) && A.checkInertiaAt a left && A.checkInertiaAt b right &&
    decide (count + right.pos = left.pos)

/-- Accepted rational endpoint computations count actual eigenvalues with
multiplicity and the stated strict/non-strict endpoint conventions. -/
theorem DenseIntMatrix.checkEigenvaluesIoc_sound (A : DenseIntMatrix)
    (hA : (ratCastMatrix A.toRatMatrix).IsHermitian) (a b : ℚ)
    (left right : Inertia) (count : Nat)
    (h : A.checkEigenvaluesIoc a b left right count = true) :
    (Finset.univ.filter fun i ↦ (a : ℝ) < hA.eigenvalues i ∧
      hA.eigenvalues i ≤ (b : ℝ)).card = count := by
  have hc : a ≤ b ∧ A.checkInertiaAt a left = true ∧
      A.checkInertiaAt b right = true ∧ count + right.pos = left.pos := by
    simpa [DenseIntMatrix.checkEigenvaluesIoc, Bool.and_assoc] using h
  have hi := Inertia.eigenvalue_count_Ioc_add_pos_eq (ratCastMatrix A.toRatMatrix) hA
    (a : ℝ) (b : ℝ) (by exact_mod_cast hc.1)
  rw [A.checkInertiaAt_sound a left hc.2.1,
    A.checkInertiaAt_sound b right hc.2.2.1] at hi
  omega

/-- Interval acceptance rejects both missing entries and surplus storage. -/
theorem DenseIntMatrix.checkEigenvaluesIoc_size (A : DenseIntMatrix) (a b : ℚ)
    (left right : Inertia) (count : Nat)
    (h : A.checkEigenvaluesIoc a b left right count = true) :
    A.entries.size = A.order * A.order := by
  have hc : a ≤ b ∧ A.checkInertiaAt a left = true ∧
      A.checkInertiaAt b right = true ∧ count + right.pos = left.pos := by
    simpa [DenseIntMatrix.checkEigenvaluesIoc, Bool.and_assoc] using h
  exact A.checkInertiaAt_size a left hc.2.1

/-- Check a bracket for the zero-based `k`th largest eigenvalue using normalized
integer elimination. The natural index is checked before any matrix computation. -/
def DenseIntMatrix.checkEigenvalueBracket (A : DenseIntMatrix) (a b : ℚ)
    (left right : Inertia) (k : Nat) : Bool :=
  decide (k < A.order) && decide (a ≤ b) &&
    A.checkInertiaAt a left && A.checkInertiaAt b right &&
    decide (k < left.pos ∧ right.pos ≤ k)

/-- Accepted integer brackets localize individual eigenvalues in mathlib's
descending order, retaining repeated eigenvalues at their distinct indices. -/
theorem DenseIntMatrix.checkEigenvalueBracket_sound (A : DenseIntMatrix)
    (hA : (ratCastMatrix A.toRatMatrix).IsHermitian) (a b : ℚ)
    (left right : Inertia) (k : Fin (Fintype.card (Fin A.order)))
    (h : A.checkEigenvalueBracket a b left right k.val = true) :
    (a : ℝ) < hA.eigenvalues₀ k ∧ hA.eigenvalues₀ k ≤ (b : ℝ) := by
  have hc : k.val < A.order ∧ a ≤ b ∧ A.checkInertiaAt a left = true ∧
      A.checkInertiaAt b right = true ∧ (k.val < left.pos ∧ right.pos ≤ k.val) := by
    simpa [DenseIntMatrix.checkEigenvalueBracket, Bool.and_assoc] using h
  apply (Inertia.eigenvalues₀_mem_Ioc_iff _ hA _ _ k).mpr
  rw [A.checkInertiaAt_sound a left hc.2.2.1,
    A.checkInertiaAt_sound b right hc.2.2.2.1]
  exact hc.2.2.2.2

/-- Malformed external eigenvalue indices are never accepted. -/
theorem DenseIntMatrix.checkEigenvalueBracket_index (A : DenseIntMatrix) (a b : ℚ)
    (left right : Inertia) (k : Nat)
    (h : A.checkEigenvalueBracket a b left right k = true) : k < A.order := by
  have hc : k < A.order ∧ a ≤ b ∧ A.checkInertiaAt a left = true ∧
      A.checkInertiaAt b right = true ∧ (k < left.pos ∧ right.pos ≤ k) := by
    simpa [DenseIntMatrix.checkEigenvalueBracket, Bool.and_assoc] using h
  exact hc.1

end SpectralGraph.Certificate
