import SpectralGraphTests.Applications.PathEndpoint8Solve
import SpectralGraphTests.Applications.PathEndpoint8Inertia
import SpectralGraph.Inertia.NegativeSpectrum

/-! The exact endpoint-edge transition. `eigenvalues₀` is descending, so index 6 is second-smallest. -/
namespace SpectralGraphTests.Applications.PathEndpoint8
open Matrix SpectralGraph SpectralGraph.Certificate SpectralGraph.Inertia

private theorem balance (c : ℝ) (hc : c ≠ 0) :
    let I := matrixInertia (ratCastMatrix A8 + c • vecMulVec
      (fun i ↦ (endpoint8 i : ℝ)) (fun i ↦ (endpoint8 i : ℝ)))
    I.pos + (scalarInertia (-c⁻¹)).pos = (scalarInertia (-c⁻¹ + 2008/223)).pos + 6 ∧
    I.zero + (scalarInertia (-c⁻¹)).zero = (scalarInertia (-c⁻¹ + 2008/223)).zero ∧
    I.neg + (scalarInertia (-c⁻¹)).neg = (scalarInertia (-c⁻¹ + 2008/223)).neg + 2 := by
  letI : Invertible (ratCastMatrix A8) := A8Invertible
  have h := rankOne_inertia_balance (ratCastMatrix A8) A8_real_symm
    (fun i ↦ (endpoint8 i : ℝ)) c hc
  rw [inverse_value, A8_inertia] at h
  have hs : -c⁻¹ - (-2008 / 223 : ℝ) = -c⁻¹ + 2008 / 223 := by ring
  rw [hs] at h
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h

private theorem update_lt (c : ℝ) (h0 : 0 < c) (h : c < (223/2008 : ℝ)) :
    matrixInertia (ratCastMatrix A8 + c • vecMulVec (fun i ↦ (endpoint8 i : ℝ))
      (fun i ↦ (endpoint8 i : ℝ))) = ⟨6,0,2⟩ := by
  have hp : -c⁻¹ < 0 := neg_neg_of_pos (inv_pos.mpr h0)
  have hr : -c⁻¹ + 2008/223 < 0 := by
    have ha : (2008 / 223 : ℝ) * c < 1 := by norm_num at h ⊢; nlinarith
    have hi : (2008 / 223 : ℝ) < c⁻¹ := by
      have hi' : (2008 / 223 : ℝ) < c⁻¹ * 1 :=
        (lt_inv_mul_iff₀ h0).2 (by nlinarith)
      simpa using hi'
    linarith
  have hb := balance c (ne_of_gt h0)
  have hp0 : ¬ 0 < -c⁻¹ := not_lt_of_ge (le_of_lt hp)
  have hr0 : ¬ 0 < -c⁻¹ + 2008 / 223 := not_lt_of_ge (le_of_lt hr)
  simp only [scalarInertia, if_neg hp0, if_neg (ne_of_lt hp), if_pos hp,
    if_neg hr0, if_neg (ne_of_lt hr), if_pos hr] at hb
  cases hi : matrixInertia (ratCastMatrix A8 + c • vecMulVec
    (fun i ↦ (endpoint8 i : ℝ)) (fun i ↦ (endpoint8 i : ℝ)))
  simp_all only [Inertia.mk.injEq]
  omega

private theorem update_eq : matrixInertia (ratCastMatrix A8 + (223/2008 : ℝ) • vecMulVec
    (fun i ↦ (endpoint8 i : ℝ)) (fun i ↦ (endpoint8 i : ℝ))) = ⟨6,1,1⟩ := by
  have hb := balance (223/2008 : ℝ) (by norm_num)
  norm_num [scalarInertia] at hb
  cases hi : matrixInertia (ratCastMatrix A8 + (223/2008 : ℝ) • vecMulVec
    (fun i ↦ (endpoint8 i : ℝ)) (fun i ↦ (endpoint8 i : ℝ)))
  simp only [hi] at hb
  simp only [Inertia.mk.injEq]
  omega

private theorem update_gt (c : ℝ) (h : (223/2008 : ℝ) < c) :
    matrixInertia (ratCastMatrix A8 + c • vecMulVec (fun i ↦ (endpoint8 i : ℝ))
      (fun i ↦ (endpoint8 i : ℝ))) = ⟨7,0,1⟩ := by
  have h0 : 0 < c := lt_trans (by norm_num) h
  have hp : -c⁻¹ < 0 := neg_neg_of_pos (inv_pos.mpr h0)
  have hr : 0 < -c⁻¹ + 2008/223 := by
    have ha : 1 < (2008 / 223 : ℝ) * c := by norm_num at h ⊢; nlinarith
    have hi : c⁻¹ < (2008 / 223 : ℝ) := (inv_lt_iff_one_lt_mul₀ h0).2 ha
    linarith
  have hb := balance c (ne_of_gt h0)
  have hp0 : ¬ 0 < -c⁻¹ := not_lt_of_ge (le_of_lt hp)
  have hrn : ¬ -c⁻¹ + 2008 / 223 < 0 := not_lt_of_ge (le_of_lt hr)
  simp only [scalarInertia, if_neg hp0, if_neg (ne_of_lt hp), if_pos hp,
    if_pos hr, if_neg (ne_of_gt hr), if_neg hrn] at hb
  cases hi : matrixInertia (ratCastMatrix A8 + c • vecMulVec
    (fun i ↦ (endpoint8 i : ℝ)) (fun i ↦ (endpoint8 i : ℝ)))
  simp_all only [Inertia.mk.injEq]
  omega

/-- Complete shifted inertia for every nonnegative endpoint-edge weight. -/
theorem shifted_inertia (c : ℝ) (hc : 0 ≤ c) : matrixInertia (L8 c - (1/4 : ℝ) • 1) =
    if c < 223/2008 then ⟨6,0,2⟩ else if c = 223/2008 then ⟨6,1,1⟩ else ⟨7,0,1⟩ := by
  rw [shifted_update]
  rcases hc.eq_or_lt with rfl | hc0
  · norm_num [A8_inertia]
  by_cases hlt : c < (223/2008 : ℝ)
  · rw [if_pos hlt]
    exact update_lt c hc0 hlt
  by_cases heq : c = (223/2008 : ℝ)
  · rw [if_neg hlt, if_pos heq]
    subst c
    exact update_eq
  · have hgt : (223/2008 : ℝ) < c := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
    rw [if_neg hlt, if_neg heq]
    exact update_gt c hgt

theorem second_smallest_lt (c : ℝ) (hc : 0 ≤ c) (h : c < 223/2008) :
    (L8_isHermitian c).eigenvalues₀ ⟨6, by decide⟩ < (1/4 : ℝ) := by
  rw [eigenvalues₀_lt_iff, shifted_inertia c hc]
  simp [h]
theorem second_smallest_eq (c : ℝ) (hc : 0 ≤ c) (h : c = 223/2008) :
    (L8_isHermitian c).eigenvalues₀ ⟨6, by decide⟩ = (1/4 : ℝ) := by
  apply le_antisymm
  · rw [eigenvalues₀_le_iff, shifted_inertia c hc]; simp [h]
  · rw [le_eigenvalues₀_iff, shifted_inertia c hc]; simp [h]
theorem threshold_lt_second_smallest (c : ℝ) (hc : 0 ≤ c) (h : (223/2008 : ℝ) < c) :
    (1/4 : ℝ) < (L8_isHermitian c).eigenvalues₀ ⟨6, by decide⟩ := by
  rw [lt_eigenvalues₀_iff, shifted_inertia c hc]
  simp [not_lt_of_ge (le_of_lt h), ne_of_gt h]

end SpectralGraphTests.Applications.PathEndpoint8
