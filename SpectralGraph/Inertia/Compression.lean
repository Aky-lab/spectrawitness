import SpectralGraph.Inertia.Restriction

/-!
# Rectangular compression

Positive-index bounds for the pullback of a real quadratic form along an
injective rectangular matrix.  The shifted identity pulls back to the full
Gram matrix `UᵀU`; it is not generally an identity matrix.
-/

namespace SpectralGraph.Inertia

open Matrix

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

/-- Matrix compression represents composition of the associated quadratic form. -/
theorem compression_toQuadraticForm'
    (A : Matrix V V ℝ) (U : Matrix V C ℝ) :
    (U.transpose * A * U).toQuadraticForm' =
      A.toQuadraticForm'.comp U.mulVecLin := by
  ext x
  simp only [QuadraticMap.comp_apply, Matrix.mulVecLin_apply,
    Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', ← Matrix.mulVec_mulVec]
  rw [dotProduct_mulVec, vecMul_transpose]

omit [Fintype C] [DecidableEq C] in
/-- Compressing a scalar shift uses the Gram matrix of the rectangular map. -/
theorem shifted_compression
    (A : Matrix V V ℝ) (U : Matrix V C ℝ) (t : ℝ) :
    U.transpose * (A - t • 1) * U =
      U.transpose * A * U - t • (U.transpose * U) := by
  simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- Positive inertia of an injective rectangular compression is bounded by
the ambient positive inertia, and loses at most the matrix codimension. -/
theorem compression_pos_bounds
    (A : Matrix V V ℝ) (U : Matrix V C ℝ)
    (hU : Function.Injective U.mulVecLin) (t : ℝ) :
    (matrixInertia (U.transpose * A * U - t • (U.transpose * U))).pos ≤
        (matrixInertia (A - t • 1)).pos ∧
      (matrixInertia (A - t • 1)).pos ≤
        (matrixInertia (U.transpose * A * U - t • (U.transpose * U))).pos +
          (Fintype.card V - Fintype.card C) := by
  rw [← shifted_compression]
  change sigPos _ ≤ sigPos _ ∧ sigPos _ ≤ sigPos _ + _
  rw [compression_toQuadraticForm']
  have hcard : Fintype.card C ≤ Fintype.card V := by
    simpa only [Module.finrank_fintype_fun_eq_card] using
      LinearMap.finrank_le_finrank_of_injective hU
  exact ⟨sigPos_comp_le _ _ hU,
    sigPos_le_comp_add_codim _ _ hU _ (by
      simp only [Module.finrank_fintype_fun_eq_card]
      omega)⟩

end SpectralGraph.Inertia
