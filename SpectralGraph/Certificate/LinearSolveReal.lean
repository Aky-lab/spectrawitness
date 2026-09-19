import SpectralGraph.Certificate.LinearSolve
import SpectralGraph.Certificate.ExactInertia
import SpectralGraph.Inertia.SchurComplement

/-! # Real semantics for exact solution certificates -/

namespace SpectralGraph.Certificate
open Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact inversion commutes with the rational embedding for nonsingular input. -/
theorem ratCast_inverse (A : Matrix ι ι ℚ) (hdet : A.det ≠ 0) :
    (ratCastMatrix A)⁻¹ = ratCastMatrix A⁻¹ := by
  apply Matrix.inv_eq_left_inv
  calc
    ratCastMatrix A⁻¹ * ratCastMatrix A = ratCastMatrix (A⁻¹ * A) := Matrix.map_mul.symm
    _ = 1 := by
      rw [Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hdet)]
      simp [ratCastMatrix]

/-- Arbitrary inverse bilinear certificates have real, not only rational,
semantics. Both input vectors are transported by the exact embedding. -/
theorem checkInverseBilinear_real_sound (A : Matrix ι ι ℚ)
    (u v x : ι → ℚ) (target : ℚ)
    (h : checkInverseBilinear A u v x target = true) :
    inverseBilinear (ratCastMatrix A) (fun i ↦ (u i : ℝ)) (fun i ↦ (v i : ℝ)) =
      (target : ℝ) := by
  have hc : A.det ≠ 0 ∧ A *ᵥ x = v ∧ u ⬝ᵥ x = target := of_decide_eq_true h
  have hs := checkInverseBilinear_sound A u v x target h
  rw [inverseBilinear, ratCast_inverse A hc.1]
  have hr := congrArg (fun q : ℚ ↦ (q : ℝ)) hs
  simpa [inverseBilinear, ratCastMatrix, Matrix.mulVec, dotProduct] using hr

/-- The left-inverse checker has real semantics without evaluating a determinant.
The same inverse certificate can be reused for many solution vectors. -/
theorem checkInverseBilinearWithInverse_real_sound (A Q : Matrix ι ι ℚ)
    (u v x : ι → ℚ) (target : ℚ)
    (h : checkInverseBilinearWithInverse A Q u v x target = true) :
    inverseBilinear (ratCastMatrix A) (fun i ↦ (u i : ℝ)) (fun i ↦ (v i : ℝ)) =
      (target : ℝ) := by
  have hc : Q * A = 1 ∧ A *ᵥ x = v ∧ u ⬝ᵥ x = target := of_decide_eq_true h
  letI : Invertible A := invertibleOfLeftInverse A Q hc.1
  have hdet : A.det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det A).mp (isUnit_of_invertible A))
  have hs := checkInverseBilinearWithInverse_sound A Q u v x target h
  rw [inverseBilinear, ratCast_inverse A hdet]
  have hr := congrArg (fun q : ℚ ↦ (q : ℝ)) hs
  simpa [inverseBilinear, ratCastMatrix, Matrix.mulVec, dotProduct] using hr

variable [Fintype κ] [DecidableEq κ]

/-- A rational Schur solve certificate gives an exact decomposition of real
quadratic-form inertia. This is spectral inertia when `D` is also symmetric.
Only the eliminated block must be symmetric here; its invertibility is
supplied by the checked left inverse. -/
theorem checkSchur_inertia (A Q : Matrix ι ι ℚ) (B X : Matrix ι κ ℚ)
    (D S : Matrix κ κ ℚ) (hA : A.IsSymm)
    (h : checkSchur A Q B X B.transpose D S = true) :
    matrixInertia (Matrix.fromBlocks (ratCastMatrix A) (B.map (Rat.castHom ℝ))
      (B.map (Rat.castHom ℝ)).transpose (ratCastMatrix D)) =
      { pos := (matrixInertia (ratCastMatrix S)).pos + (matrixInertia (ratCastMatrix A)).pos
        zero := (matrixInertia (ratCastMatrix S)).zero + (matrixInertia (ratCastMatrix A)).zero
        neg := (matrixInertia (ratCastMatrix S)).neg + (matrixInertia (ratCastMatrix A)).neg } := by
  have hc : Q * A = 1 ∧ A * X = B ∧ D - B.transpose * X = S := of_decide_eq_true h
  have hinv : ratCastMatrix Q * ratCastMatrix A = 1 := by
    unfold ratCastMatrix
    rw [← Matrix.map_mul]
    simp [hc.1]
  letI : Invertible (ratCastMatrix A) := invertibleOfLeftInverse _ _ hinv
  have hdet : A.det ≠ 0 := by
    letI : Invertible A := invertibleOfLeftInverse A Q hc.1
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det A).mp (isUnit_of_invertible A))
  have hs := checkSchur_sound A Q B X B.transpose D S h
  have hreal : ratCastMatrix D - (B.map (Rat.castHom ℝ)).transpose *
      ⅟ (ratCastMatrix A) * B.map (Rat.castHom ℝ) = ratCastMatrix S := by
    rw [Matrix.invOf_eq_nonsing_inv, ratCast_inverse A hdet]
    ext i j
    have he := congrArg (fun M : Matrix κ κ ℚ ↦ (M i j : ℝ)) hs
    simpa [ratCastMatrix, Matrix.mul_apply] using he
  have hi := Inertia.matrixInertia_fromBlocks_schur₁₁
    (ratCastMatrix A) (B.map (Rat.castHom ℝ)) (ratCastMatrix D) (hA.map _)
  rwa [hreal] at hi

end SpectralGraph.Certificate
