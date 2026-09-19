import SpectralGraph.Certificate.Witness

/-!
# Arbitrary-dimensional negative subspace certificates

An untrusted producer supplies columns spanning a negative subspace and their
negative diagonal Gram entries. Checking `Uᵀ A U = diagonal d` proves both
independence of the columns and the ambient negative-index lower bound. No
left inverse, ambient diagonalization, or pre-existing independence proof is
required. For symmetric rational input, rational orthogonalization can construct
such data off the trusted path. The witness dimension and ambient dimension are independent finite types.
-/

namespace SpectralGraph.Certificate
open Matrix QuadraticForm

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- A negative subspace represented by an orthogonal rational basis. -/
def checkNegativeSubspace (A : Matrix ι ι ℚ) (U : Matrix ι κ ℚ) (d : κ → ℚ) : Bool :=
  decide (U.transpose * A * U = Matrix.diagonal d ∧ ∀ j, d j < 0)

/-- A successful negative Gram certificate bounds the negative inertia index
by the number of supplied columns. This is quadratic-form inertia, so ambient
symmetry is not needed (for symmetric input it is spectral inertia). -/
theorem checkNegativeSubspace_sound (A : Matrix ι ι ℚ) (U : Matrix ι κ ℚ) (d : κ → ℚ)
    (h : checkNegativeSubspace A U d = true) :
    Fintype.card κ ≤ (matrixInertia (ratCastMatrix A)).neg := by
  have hc : U.transpose * A * U = Matrix.diagonal d ∧ ∀ j, d j < 0 := of_decide_eq_true h
  let V := U.map (Rat.castHom ℝ)
  have hg : V.transpose * ratCastMatrix A * V = Matrix.diagonal (fun j ↦ (d j : ℝ)) := by
    have he := congrArg (fun M : Matrix κ κ ℚ ↦ M.map (Rat.castHom ℝ)) hc.1
    change (U.map (Rat.castHom ℝ)).transpose * A.map (Rat.castHom ℝ) *
      U.map (Rat.castHom ℝ) = _
    rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
    simpa using he
  have hd : IsUnit (Matrix.diagonal (fun j ↦ (d j : ℝ))) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [Matrix.det_diagonal]
    apply isUnit_iff_ne_zero.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact_mod_cast (ne_of_lt (hc.2 j))
  have hginj : Function.Injective (V.transpose * ratCastMatrix A * V).mulVec := by
    apply Matrix.mulVec_injective_iff_isUnit.mpr
    rwa [hg]
  have hinj : Function.Injective V.mulVecLin := by
    intro x y hxy
    apply hginj
    simp only [← Matrix.mulVec_mulVec]
    exact congrArg (fun z ↦ V.transpose *ᵥ (ratCastMatrix A *ᵥ z)) hxy
  have hcomp : (V.transpose * ratCastMatrix A * V).toQuadraticForm' =
      (ratCastMatrix A).toQuadraticForm'.comp V.mulVecLin := by
    ext x
    simp only [QuadraticMap.comp_apply, Matrix.mulVecLin_apply,
      Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply', ← Matrix.mulVec_mulVec]
    rw [dotProduct_mulVec, vecMul_transpose]
  have hbound := Inertia.sigNeg_comp_le (ratCastMatrix A).toQuadraticForm' V.mulVecLin hinj
  rw [← hcomp] at hbound
  change (matrixInertia (V.transpose * ratCastMatrix A * V)).neg ≤
    (matrixInertia (ratCastMatrix A)).neg at hbound
  rw [hg, matrixInertia_ratCast_diagonal] at hbound
  simpa [rationalDiagonalInertia, hc.2] using hbound

end SpectralGraph.Certificate
