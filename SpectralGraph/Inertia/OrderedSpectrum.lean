import SpectralGraph.Inertia.Spectrum
import Mathlib.Order.Interval.Finset.Fin

/-!
# Ordered eigenvalue localization

Threshold inertia localizes individual eigenvalues in mathlib's descending
ordering. Indices are zero based, and repeated eigenvalues keep multiplicity.
-/

namespace SpectralGraph.Inertia

/-- In a descending finite list, a strict threshold selects an initial segment. -/
theorem lt_antitone_iff_lt_card {n : Nat} (f : Fin n → ℝ) (hf : Antitone f)
    (t : ℝ) (k : Fin n) :
    t < f k ↔ k.val < (Finset.univ.filter fun i ↦ t < f i).card := by
  classical
  constructor
  · intro hk
    have hsub : Finset.Iic k ⊆ Finset.univ.filter (fun i ↦ t < f i) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_lt_of_le hk (hf (Finset.mem_Iic.mp hi))⟩
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hc
    omega
  · intro hc
    by_contra hk
    have hsub : Finset.univ.filter (fun i ↦ t < f i) ⊆ Finset.Iio k := by
      intro i hi
      apply Finset.mem_Iio.mpr
      by_contra hik
      have hki : k ≤ i := le_of_not_gt hik
      exact hk (lt_of_lt_of_le (Finset.mem_filter.mp hi).2 (hf hki))
    have hn := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hn
    omega

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Reindexing the spectral list does not change a threshold count. -/
theorem eigenvalues_card_lt_eq (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (t : ℝ) :
    (Finset.univ.filter fun i ↦ t < hA.eigenvalues i).card =
      (Finset.univ.filter fun i ↦ t < hA.eigenvalues₀ i).card := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := Fintype.equivOfCardEq (Fintype.card_fin _)
  apply Finset.card_bij (fun i _ ↦ e.symm i)
  · intro i hi
    simpa [Matrix.IsHermitian.eigenvalues, e] using hi
  · intro i hi j hj he
    exact e.symm.injective he
  · intro i hi
    refine ⟨e i, ?_, e.symm_apply_apply i⟩
    simpa [Matrix.IsHermitian.eigenvalues, e] using hi

/-- The `k`th largest eigenvalue lies strictly above a threshold exactly when
there are more than `k` positive directions after shifting by that threshold. -/
theorem lt_eigenvalues₀_iff (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (t : ℝ) (k : Fin (Fintype.card ι)) :
    t < hA.eigenvalues₀ k ↔ k.val < (matrixInertia (A - t • 1)).pos := by
  rw [matrixInertia_shift_eq_eigenvalue_counts, eigenvalues_card_lt_eq]
  exact lt_antitone_iff_lt_card _ hA.eigenvalues₀_antitone t k

/-- The complementary non-strict upper bound includes eigenvalues at the threshold. -/
theorem eigenvalues₀_le_iff (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (t : ℝ) (k : Fin (Fintype.card ι)) :
    hA.eigenvalues₀ k ≤ t ↔ (matrixInertia (A - t • 1)).pos ≤ k.val := by
  simpa only [not_lt] using not_congr (lt_eigenvalues₀_iff A hA t k)

/-- Two shifted inertia results localize one ordered eigenvalue in `(a,b]`. -/
theorem eigenvalues₀_mem_Ioc_iff (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (a b : ℝ) (k : Fin (Fintype.card ι)) :
    a < hA.eigenvalues₀ k ∧ hA.eigenvalues₀ k ≤ b ↔
      k.val < (matrixInertia (A - a • 1)).pos ∧
      (matrixInertia (A - b • 1)).pos ≤ k.val := by
  rw [lt_eigenvalues₀_iff, eigenvalues₀_le_iff]

end SpectralGraph.Inertia
