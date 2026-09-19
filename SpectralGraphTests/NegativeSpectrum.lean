import SpectralGraph.Inertia.NegativeSpectrum
import SpectralGraph.Certificate.WitnessSubspace
import SpectralGraph.Certificate.SpectralInterval

namespace SpectralGraphTests.NegativeSpectrum
open SpectralGraph SpectralGraph.Inertia Matrix

-- Repeated threshold values are excluded from the strict final segment.
example : ¬((![3, 1, 1, -2] : Fin 4 → ℝ) 1 < 1) := by norm_num
example : (Finset.univ.filter fun i ↦ (![3, 1, 1, -2] : Fin 4 → ℝ) i < 1).card = 1 := by
  have hs : (Finset.univ.filter fun i ↦ (![3, 1, 1, -2] : Fin 4 → ℝ) i < 1) = {3} := by
    ext i
    fin_cases i <;> norm_num [Fin.ext_iff]
  rw [hs]
  rfl

-- Two certified negative directions localize the second eigenvalue in dimension three.
example (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.IsHermitian) (t : ℝ)
    (h : 2 ≤ (matrixInertia (A - t • 1)).neg) :
    hA.eigenvalues₀ ⟨1, by decide⟩ < t := by
  exact eigenvalues₀_lt_of_negative_index A hA t ⟨1, by decide⟩ 2 h (by decide)

-- The smallest eigenvalue needs only one negative direction.
example (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.IsHermitian) (t : ℝ)
    (h : 1 ≤ (matrixInertia (A - t • 1)).neg) :
    hA.eigenvalues₀ ⟨2, by decide⟩ < t := by
  exact eigenvalues₀_lt_of_negative_index A hA t ⟨2, by decide⟩ 1 h (by decide)

-- At an eigenvalue, the complementary lower bound uses a strict index inequality.
example (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.IsHermitian) (t : ℝ)
    (h : (matrixInertia (A - t • 1)).neg = 1) :
    t ≤ hA.eigenvalues₀ ⟨1, by decide⟩ := by
  apply (le_eigenvalues₀_iff A hA t ⟨1, by decide⟩).mpr
  simp [h]

#print axioms SpectralGraph.Inertia.eigenvalues₀_lt_iff
#print axioms SpectralGraph.Inertia.eigenvalues₀_lt_of_negDef_subspace

open SpectralGraph.Certificate

/-- Only a three-column witness is supplied for this six-dimensional problem. -/
def partialForm : Matrix (Fin 6) (Fin 6) ℚ := diagonal ![9, 5, 3, -2, -2, -2]
def negativeColumns : Matrix (Fin 6) (Fin 3) ℚ :=
  fun i j ↦ if i.val = j.val + 3 then 1 else 0

theorem partialForm_hermitian : (ratCastMatrix partialForm).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases hij : i = j <;> simp [ratCastMatrix, partialForm, hij, eq_comm]

/-- A partial negative Gram certificate bounds the fourth largest eigenvalue.
No complete inertia certificate or eigenvalue computation is used. -/
theorem fourth_eigenvalue_below_minus_one :
    partialForm_hermitian.eigenvalues₀ ⟨3, by decide⟩ < (-1 : ℝ) := by
  have hw := checkNegativeSubspace_sound (partialForm - (-1 : ℚ) • 1)
    negativeColumns (fun _ : Fin 3 ↦ (-1 : ℚ)) (by decide +kernel)
  rw [ratCast_shift] at hw
  apply eigenvalues₀_lt_of_negative_index (ratCastMatrix partialForm)
    partialForm_hermitian (-1) ⟨3, by decide⟩ 3 _ (by decide)
  simpa using hw

#print axioms fourth_eigenvalue_below_minus_one
end SpectralGraphTests.NegativeSpectrum
