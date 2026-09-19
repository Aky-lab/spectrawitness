import SpectralGraph.Certificate.Basic
import SpectralGraph.Inertia.NegativeWitness

/-!
# Exact vector witnesses for inertia lower bounds

Checking a vector or a two-dimensional Gram matrix can be much cheaper than
computing full inertia. The matrix and vectors share an arbitrary finite index
type, so there is no padding or truncation in this typed API. All arithmetic
in the checkers is rational; conclusions concern the real quadratic form.
Symmetry is checked where it is required for the claimed semantics.
-/

namespace SpectralGraph.Certificate
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact rational bilinear evaluation. -/
def witnessBilinear (A : Matrix ι ι ℚ) (u v : ι → ℚ) : ℚ := u ⬝ᵥ A *ᵥ v

/-- Coordinatewise embedding of a rational witness into the real space. -/
def ratCastVector (u : ι → ℚ) : ι → ℝ := fun i ↦ (u i : ℝ)

omit [DecidableEq ι] in
theorem ratCastVector_mulVec (A : Matrix ι ι ℚ) (u : ι → ℚ) :
    ratCastMatrix A *ᵥ ratCastVector u = ratCastVector (A *ᵥ u) := by
  ext i
  simp [ratCastMatrix, ratCastVector, Matrix.mulVec, dotProduct]

omit [DecidableEq ι] in
theorem ratCast_witnessBilinear (A : Matrix ι ι ℚ) (u v : ι → ℚ) :
    ratCastVector u ⬝ᵥ ratCastMatrix A *ᵥ ratCastVector v =
      (witnessBilinear A u v : ℝ) := by
  rw [ratCastVector_mulVec]
  simp [ratCastVector, witnessBilinear, dotProduct]

theorem ratCast_witnessQuadratic (A : Matrix ι ι ℚ) (u : ι → ℚ) :
    (ratCastMatrix A).toQuadraticForm' (ratCastVector u) =
      (witnessBilinear A u u : ℝ) := by
  simpa only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply'] using ratCast_witnessBilinear A u u

omit [Fintype ι] [DecidableEq ι] in
theorem ratCastVector_ne_zero {u : ι → ℚ} (h : u ≠ 0) : ratCastVector u ≠ 0 := by
  intro hz
  apply h
  ext i
  have hi := congrFun hz i
  simpa [ratCastVector] using hi

/-- One negative direction; no symmetry assumption is needed for this
quadratic-form statement. -/
def checkNegativeVector (A : Matrix ι ι ℚ) (u : ι → ℚ) : Bool :=
  decide (witnessBilinear A u u < 0)

theorem checkNegativeVector_sound (A : Matrix ι ι ℚ) (u : ι → ℚ)
    (h : checkNegativeVector A u = true) : 1 ≤ (matrixInertia (ratCastMatrix A)).neg := by
  apply Inertia.one_le_matrixInertia_neg_of_negative _ (ratCastVector u)
  rw [ratCast_witnessQuadratic]
  exact_mod_cast (of_decide_eq_true h : witnessBilinear A u u < 0)

/-- The two-vector Gram matrix is negative definite exactly when its first
diagonal entry is negative and its determinant is positive. Checking ambient
symmetry makes the single cross term sufficient. -/
def checkNegativePair (A : Matrix ι ι ℚ) (u v : ι → ℚ) : Bool :=
  decide (A.IsSymm ∧ witnessBilinear A u u < 0 ∧
    0 < witnessBilinear A u u * witnessBilinear A v v - (witnessBilinear A u v) ^ 2)

theorem checkNegativePair_sound (A : Matrix ι ι ℚ) (u v : ι → ℚ)
    (h : checkNegativePair A u v = true) :
    2 ≤ (matrixInertia (ratCastMatrix A)).neg := by
  have hc : A.IsSymm ∧ witnessBilinear A u u < 0 ∧
      0 < witnessBilinear A u u * witnessBilinear A v v -
        (witnessBilinear A u v) ^ 2 := of_decide_eq_true h
  have hs : (ratCastMatrix A).IsSymm := hc.1.map _
  apply Inertia.two_le_matrixInertia_neg_of_negative_pair (ratCastMatrix A) hs
    (ratCastVector u) (ratCastVector v)
  · rw [ratCast_witnessQuadratic]
    exact_mod_cast hc.2.1
  · rw [ratCast_witnessQuadratic, ratCast_witnessQuadratic, ratCast_witnessBilinear]
    exact_mod_cast hc.2.2

/-- A nonzero kernel witness. Symmetry is included because quadratic-form
nullity is matrix nullity only for symmetric input. -/
def checkKernelVector (A : Matrix ι ι ℚ) (u : ι → ℚ) : Bool :=
  decide (A.IsSymm ∧ u ≠ 0 ∧ A *ᵥ u = 0)

theorem checkKernelVector_sound (A : Matrix ι ι ℚ) (u : ι → ℚ)
    (h : checkKernelVector A u = true) :
    1 ≤ (matrixInertia (ratCastMatrix A)).zero := by
  have hc : A.IsSymm ∧ u ≠ 0 ∧ A *ᵥ u = 0 := of_decide_eq_true h
  change 1 ≤ Module.finrank ℝ ↥(QuadraticMap.radical (ratCastMatrix A).toQuadraticForm')
  have hs : (ratCastMatrix A).IsSymm := hc.1.map _
  rw [Inertia.radical_toQuadraticForm'_eq_ker_mulVecLin (ratCastMatrix A) hs]
  apply Nat.succ_le_iff.mpr
  rw [Module.finrank_pos_iff_exists_ne_zero]
  have hk : ratCastMatrix A *ᵥ ratCastVector u = 0 := by
    rw [ratCastVector_mulVec, hc.2.2]
    ext i
    norm_num [ratCastVector]
  exact ⟨⟨ratCastVector u, by simpa using hk⟩, by
    simpa using ratCastVector_ne_zero hc.2.1⟩

/-- The same accepted witness certifies singularity of the real matrix. -/
theorem checkKernelVector_not_isUnit (A : Matrix ι ι ℚ) (u : ι → ℚ)
    (h : checkKernelVector A u = true) : ¬ IsUnit (ratCastMatrix A) := by
  intro hu
  have hc : A.IsSymm ∧ u ≠ 0 ∧ A *ᵥ u = 0 := of_decide_eq_true h
  have hs : (ratCastMatrix A).IsSymm := hc.1.map _
  have hz := Inertia.matrixInertia_zero_eq_zero_of_isUnit (ratCastMatrix A) hs hu
  have hp := checkKernelVector_sound A u h
  omega

end SpectralGraph.Certificate


