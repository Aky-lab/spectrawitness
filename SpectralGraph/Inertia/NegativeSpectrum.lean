import SpectralGraph.Inertia.OrderedSpectrum

/-!
# Strict upper spectral bounds from negative indices

Negative directions of `A - tI` count eigenvalues strictly below `t`.
This complements the positive-index API, whose upper endpoint is non-strict.
The descending ordering and multiplicities are retained throughout.
-/

namespace SpectralGraph.Inertia

/-- In a descending list, a strict upper threshold selects a final segment. -/
theorem antitone_lt_iff_sub_le_card {n : Nat} (f : Fin n → ℝ) (hf : Antitone f)
    (t : ℝ) (k : Fin n) :
    f k < t ↔ n - k.val ≤ (Finset.univ.filter fun i ↦ f i < t).card := by
  classical
  constructor
  · intro hk
    have hsub : Finset.Ici k ⊆ Finset.univ.filter (fun i ↦ f i < t) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        lt_of_le_of_lt (hf (Finset.mem_Ici.mp hi)) hk⟩
    have hc := Finset.card_le_card hsub
    rwa [Fin.card_Ici] at hc
  · intro hc
    by_contra hk
    have hsub : Finset.univ.filter (fun i ↦ f i < t) ⊆ Finset.Ioi k := by
      intro i hi
      apply Finset.mem_Ioi.mpr
      by_contra hik
      have hik' : i ≤ k := le_of_not_gt hik
      exact hk (lt_of_le_of_lt (hf hik') (Finset.mem_filter.mp hi).2)
    have hn := Finset.card_le_card hsub
    rw [Fin.card_Ioi] at hn
    have hkbound := k.isLt
    omega

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Any eigenvalue predicate has the same multiplicity count after reindexing
from the original finite type to the descending spectral list. -/
theorem eigenvalues_card_filter_eq (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (p : ℝ → Prop) [DecidablePred p] :
    (Finset.univ.filter fun i ↦ p (hA.eigenvalues i)).card =
      (Finset.univ.filter fun i ↦ p (hA.eigenvalues₀ i)).card := by
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

/-- The `k`th largest eigenvalue is strictly below `t` exactly when at least
`card ι - k` eigenvalues lie below `t`. Equality at the threshold is excluded. -/
theorem eigenvalues₀_lt_iff (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (t : ℝ) (k : Fin (Fintype.card ι)) :
    hA.eigenvalues₀ k < t ↔ Fintype.card ι - k.val ≤ (matrixInertia (A - t • 1)).neg := by
  rw [matrixInertia_shift_eq_eigenvalue_counts A hA t]
  change hA.eigenvalues₀ k < t ↔ Fintype.card ι - k.val ≤
    (Finset.univ.filter fun i ↦ hA.eigenvalues i < t).card
  rw [eigenvalues_card_filter_eq A hA (fun x ↦ x < t)]
  exact antitone_lt_iff_sub_le_card _ hA.eigenvalues₀_antitone t k

/-- Complementary lower bound from a strict bound on the negative index. -/
theorem le_eigenvalues₀_iff (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (t : ℝ) (k : Fin (Fintype.card ι)) :
    t ≤ hA.eigenvalues₀ k ↔ (matrixInertia (A - t • 1)).neg < Fintype.card ι - k.val := by
  simpa only [not_lt, not_le] using not_congr (eigenvalues₀_lt_iff A hA t k)

/-- Any certified lower bound on the negative index gives a strict upper
bound for the corresponding descending eigenvalue. -/
theorem eigenvalues₀_lt_of_negative_index (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (t : ℝ) (k : Fin (Fintype.card ι)) (d : Nat)
    (hd : d ≤ (matrixInertia (A - t • 1)).neg) (hk : Fintype.card ι - k.val ≤ d) :
    hA.eigenvalues₀ k < t :=
  (eigenvalues₀_lt_iff A hA t k).mpr (hk.trans hd)

/-- A negative-definite witness subspace localizes an ordered eigenvalue.
This allows sparse subspace certificates to avoid computing complete inertia. -/
theorem eigenvalues₀_lt_of_negDef_subspace (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (t : ℝ) (k : Fin (Fintype.card ι)) (W : Submodule ℝ (ι → ℝ))
    (hW : ((-(A - t • 1).toQuadraticForm').restrict W).PosDef)
    (hk : Fintype.card ι - k.val ≤ Module.finrank ℝ W) :
    hA.eigenvalues₀ k < t := by
  apply eigenvalues₀_lt_of_negative_index A hA t k (Module.finrank ℝ W) _ hk
  exact le_sigNeg_of_negDef (A - t • 1).toQuadraticForm' hW

end SpectralGraph.Inertia
