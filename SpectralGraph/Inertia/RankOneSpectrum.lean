import SpectralGraph.Inertia.SpectrumComparison
import SpectralGraph.Inertia.RankOneGeneral

/-!
# Ordered spectra under rank-one updates

The eigenvalue order is mathlib's descending, zero-based `eigenvalues₀`.
These weak bounds include zero update vectors, singular bases, and repeated
eigenvalues.
-/

namespace SpectralGraph.Inertia

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem vecMulVec_self_isHermitian (u : ι → ℝ) :
    (vecMulVec u u).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simp [vecMulVec_apply, mul_comm]

theorem rankOneUpdate_isHermitian (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (u : ι → ℝ) (c : ℝ) : (A + c • vecMulVec u u).IsHermitian := by
  exact hA.add ((vecMulVec_self_isHermitian u).smul (IsSelfAdjoint.all c))

/-- Increasing a rank-one coefficient weakly increases every descending
ordered eigenvalue. -/
theorem eigenvalues₀_rankOne_mono (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (u : ι → ℝ) {a b : ℝ} (hab : a ≤ b) (k : Fin (Fintype.card ι)) :
    (rankOneUpdate_isHermitian A hA u a).eigenvalues₀ k ≤
      (rankOneUpdate_isHermitian A hA u b).eigenvalues₀ k := by
  apply eigenvalues₀_le_of_pos_le_add
    (A + a • vecMulVec u u) (rankOneUpdate_isHermitian A hA u a)
    (A + b • vecMulVec u u) (rankOneUpdate_isHermitian A hA u b) 0 k k
  · omega
  · intro t
    have h := rankOne_inertia_mono (A - t • 1) u hab
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h.1

/-- A rank-one coefficient increase can move an eigenvalue by at most one
place in descending order. -/
theorem eigenvalues₀_rankOne_succ_le (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (u : ι → ℝ) {a b : ℝ} (hab : a ≤ b) (k : Fin (Fintype.card ι))
    (hk : k.val + 1 < Fintype.card ι) :
    (rankOneUpdate_isHermitian A hA u b).eigenvalues₀ ⟨k.val + 1, hk⟩ ≤
      (rankOneUpdate_isHermitian A hA u a).eigenvalues₀ k := by
  apply eigenvalues₀_le_of_pos_le_add
    (A + b • vecMulVec u u) (rankOneUpdate_isHermitian A hA u b)
    (A + a • vecMulVec u u) (rankOneUpdate_isHermitian A hA u a) 1 ⟨k.val + 1, hk⟩ k
  · change k.val + 1 ≤ k.val + 1
    rfl
  · intro t
    have h := rankOne_inertia_mono (A - t • 1) u hab
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h.2.1

end SpectralGraph.Inertia
