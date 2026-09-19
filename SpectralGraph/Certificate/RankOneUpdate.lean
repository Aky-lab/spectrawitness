import SpectralGraph.Certificate.LinearSolveReal
import SpectralGraph.Inertia.RankOneExact

/-!
# Exact rank-one update certificates

Given a previously proved base inertia, a checked inverse solution and one
rational scalar determine the updated inertia. The base inertia is an explicit
hypothesis of soundness, so it can be certified once and reused across updates.
-/

namespace SpectralGraph.Certificate
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Executable inertia of one rational pivot. -/
def rationalScalarInertia (x : ℚ) : Inertia :=
  ⟨if 0 < x then 1 else 0, if x = 0 then 1 else 0, if x < 0 then 1 else 0⟩

theorem scalarInertia_ratCast (x : ℚ) :
    Inertia.scalarInertia (x : ℝ) = rationalScalarInertia x := by
  simp [Inertia.scalarInertia, rationalScalarInertia]

/-- Check the change from a known base inertia for a nonzero rank-one update.
The matrix must be symmetric and the supplied inverse must be valid. -/
def checkRankOneUpdate (A Q : Matrix ι ι ℚ) (u x : ι → ℚ)
    (c value : ℚ) (base target : Inertia) : Bool :=
  let pivot := rationalScalarInertia (-c⁻¹)
  let correction := rationalScalarInertia (-c⁻¹ - value)
  decide (A.IsSymm ∧ c ≠ 0) && checkInverseBilinearWithInverse A Q u u x value &&
    decide (target.pos + pivot.pos = correction.pos + base.pos ∧
      target.zero + pivot.zero = correction.zero + base.zero ∧
      target.neg + pivot.neg = correction.neg + base.neg)

/-- A checked inverse quadratic value plus established base inertia determines
all three updated indices, even at the singular transition. -/
theorem checkRankOneUpdate_sound (A Q : Matrix ι ι ℚ) (u x : ι → ℚ)
    (c value : ℚ) (base target : Inertia)
    (hbase : matrixInertia (ratCastMatrix A) = base)
    (h : checkRankOneUpdate A Q u x c value base target = true) :
    matrixInertia (ratCastMatrix A + (c : ℝ) •
      vecMulVec (fun i ↦ (u i : ℝ)) (fun i ↦ (u i : ℝ))) = target := by
  have hc : (A.IsSymm ∧ c ≠ 0) ∧
      checkInverseBilinearWithInverse A Q u u x value = true ∧
      (target.pos + (rationalScalarInertia (-c⁻¹)).pos =
        (rationalScalarInertia (-c⁻¹ - value)).pos + base.pos ∧
       target.zero + (rationalScalarInertia (-c⁻¹)).zero =
        (rationalScalarInertia (-c⁻¹ - value)).zero + base.zero ∧
       target.neg + (rationalScalarInertia (-c⁻¹)).neg =
        (rationalScalarInertia (-c⁻¹ - value)).neg + base.neg) := by
    simpa [checkRankOneUpdate, Bool.and_assoc, and_assoc] using h
  have hs : Q * A = 1 ∧ A *ᵥ x = u ∧ u ⬝ᵥ x = value := of_decide_eq_true hc.2.1
  have hinv : ratCastMatrix Q * ratCastMatrix A = 1 := by
    unfold ratCastMatrix
    rw [← Matrix.map_mul, hs.1]
    simp
  letI : Invertible (ratCastMatrix A) := invertibleOfLeftInverse _ _ hinv
  have hv := checkInverseBilinearWithInverse_real_sound A Q u u x value hc.2.1
  have hb := Inertia.rankOne_inertia_balance (ratCastMatrix A) (hc.1.1.map _)
    (fun i ↦ (u i : ℝ)) (c : ℝ) (by exact_mod_cast hc.1.2)
  change (fun i ↦ (u i : ℝ)) ⬝ᵥ ((ratCastMatrix A)⁻¹ *ᵥ (fun i ↦ (u i : ℝ))) =
    (value : ℝ) at hv
  dsimp only at hb
  rw [hv, hbase] at hb
  have hp : Inertia.scalarInertia (-(c : ℝ)⁻¹) = rationalScalarInertia (-c⁻¹) := by
    simpa using scalarInertia_ratCast (-c⁻¹)
  have hr : Inertia.scalarInertia (-(c : ℝ)⁻¹ - (value : ℝ)) =
      rationalScalarInertia (-c⁻¹ - value) := by
    simpa using scalarInertia_ratCast (-c⁻¹ - value)
  rw [hp, hr] at hb
  have hpos := hb.1
  have hzero := hb.2.1
  have hneg := hb.2.2
  have hp' := hc.2.2.1
  have hz' := hc.2.2.2.1
  have hn' := hc.2.2.2.2
  cases ht : matrixInertia (ratCastMatrix A + (c : ℝ) •
    vecMulVec (fun i ↦ (u i : ℝ)) (fun i ↦ (u i : ℝ)))
  cases target
  simp_all only [Inertia.mk.injEq]
  omega

end SpectralGraph.Certificate
