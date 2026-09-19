import SpectralGraph.Certificate.LinearSolveReal
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! A checked rational block solve gives real harmonic response and a Dirichlet minimum. -/

namespace SpectralGraph.Certificate
open Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

private theorem checkSchur_real_data (A Q : Matrix ι ι ℚ) (B X : Matrix ι κ ℚ)
    (D S : Matrix κ κ ℚ) (h : checkSchur A Q B X B.transpose D S = true) :
    ratCastMatrix Q * ratCastMatrix A = 1 ∧
    ratCastMatrix A * X.map (Rat.castHom ℝ) = B.map (Rat.castHom ℝ) ∧
    ratCastMatrix D - (B.map (Rat.castHom ℝ)).transpose * X.map (Rat.castHom ℝ) =
      ratCastMatrix S := by
  have hc : Q * A = 1 ∧ A * X = B ∧ D - B.transpose * X = S := of_decide_eq_true h
  constructor
  · unfold ratCastMatrix
    rw [← Matrix.map_mul, hc.1]
    simp
  constructor
  · ext i j
    have he := congrArg (fun M : Matrix ι κ ℚ ↦ (M i j : ℝ)) hc.2.1
    simpa [ratCastMatrix, Matrix.mul_apply] using he
  · ext i j
    have he := congrArg (fun M : Matrix κ κ ℚ ↦ (M i j : ℝ)) hc.2.2
    simpa [ratCastMatrix, Matrix.mul_apply] using he

private theorem checkSchur_real_solve (A Q : Matrix ι ι ℚ) (B X : Matrix ι κ ℚ)
    (D S : Matrix κ κ ℚ) (h : checkSchur A Q B X B.transpose D S = true) :
    ratCastMatrix A * X.map (Rat.castHom ℝ) = B.map (Rat.castHom ℝ) := by
  have hc : A * X = B := (of_decide_eq_true h :
    Q * A = 1 ∧ A * X = B ∧ D - B.transpose * X = S).2.1
  ext i j
  have he := congrArg (fun M : Matrix ι κ ℚ ↦ (M i j : ℝ)) hc
  simpa [ratCastMatrix, Matrix.mul_apply] using he

/-- A valid Schur certificate gives zero interior current and the exact real
terminal response at every real boundary voltage. -/
theorem checkSchur_harmonic_response (A Q : Matrix ι ι ℚ) (B X : Matrix ι κ ℚ)
    (D S : Matrix κ κ ℚ) (h : checkSchur A Q B X B.transpose D S = true)
    (y : κ → ℝ) :
    Matrix.fromBlocks (ratCastMatrix A) (B.map (Rat.castHom ℝ))
      (B.map (Rat.castHom ℝ)).transpose (ratCastMatrix D) *ᵥ
        Sum.elim (-(X.map (Rat.castHom ℝ) *ᵥ y)) y =
      Sum.elim (0 : ι → ℝ) (ratCastMatrix S *ᵥ y) := by
  have hc := checkSchur_real_data A Q B X D S h
  have hs := checkSchur_real_solve A Q B X D S h
  rw [Matrix.fromBlocks_mulVec]
  have hi : ratCastMatrix A *ᵥ (-(X.map (Rat.castHom ℝ) *ᵥ y)) +
      B.map (Rat.castHom ℝ) *ᵥ y = 0 := by
    rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, hs]
    simp
  have ht : (B.map (Rat.castHom ℝ)).transpose *ᵥ
      (-(X.map (Rat.castHom ℝ) *ᵥ y)) + ratCastMatrix D *ᵥ y =
      ratCastMatrix S *ᵥ y := by
    calc
      _ = ratCastMatrix D *ᵥ y -
          ((B.map (Rat.castHom ℝ)).transpose * X.map (Rat.castHom ℝ)) *ᵥ y := by
            rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec]
            abel
      _ = (ratCastMatrix D -
          (B.map (Rat.castHom ℝ)).transpose * X.map (Rat.castHom ℝ)) *ᵥ y := by
            rw [Matrix.sub_mulVec]
      _ = ratCastMatrix S *ᵥ y := by rw [hc.2.2]
  simpa only [Sum.elim_comp_inl, Sum.elim_comp_inr] using
    congrArg₂ (fun a b => Sum.elim a b) hi ht

private theorem checkSchur_completed_energy (A Q : Matrix ι ι ℚ)
    (B X : Matrix ι κ ℚ) (D S : Matrix κ κ ℚ)
    (h : checkSchur A Q B X B.transpose D S = true)
    (hA : (ratCastMatrix A).PosDef) (x : ι → ℝ) (y : κ → ℝ) :
    dotProduct (Sum.elim x y)
      (Matrix.fromBlocks (ratCastMatrix A) (B.map (Rat.castHom ℝ))
        (B.map (Rat.castHom ℝ)).transpose (ratCastMatrix D) *ᵥ Sum.elim x y) =
      dotProduct (x + X.map (Rat.castHom ℝ) *ᵥ y)
        (ratCastMatrix A *ᵥ (x + X.map (Rat.castHom ℝ) *ᵥ y)) +
      dotProduct y (ratCastMatrix S *ᵥ y) := by
  have hc := checkSchur_real_data A Q B X D S h
  have hs := checkSchur_real_solve A Q B X D S h
  letI : Invertible (ratCastMatrix A) := invertibleOfLeftInverse _ _ hc.1
  have hx : (ratCastMatrix A)⁻¹ * B.map (Rat.castHom ℝ) =
      X.map (Rat.castHom ℝ) := by
    exact (Matrix.inv_mul_eq_iff_eq_mul_of_invertible _ _ _).2 hs.symm
  have hschur : ratCastMatrix D -
      (B.map (Rat.castHom ℝ)).transpose * (ratCastMatrix A)⁻¹ *
        B.map (Rat.castHom ℝ) = ratCastMatrix S := by
    rw [Matrix.mul_assoc, hx]
    exact hc.2.2
  have hcomplete := Matrix.schur_complement_eq₁₁
    (B.map (Rat.castHom ℝ)) (ratCastMatrix D) x y hA.1
  simpa only [star_trivial, Matrix.conjTranspose_eq_transpose_of_trivial,
    ← dotProduct_mulVec, hx, hschur] using hcomplete

/-- The checked Schur value is a lower bound on energy for every real
interior competitor and every real terminal vector. -/
theorem checkSchur_energy_min (A Q : Matrix ι ι ℚ) (B X : Matrix ι κ ℚ)
    (D S : Matrix κ κ ℚ) (h : checkSchur A Q B X B.transpose D S = true)
    (hA : (ratCastMatrix A).PosDef) (y : κ → ℝ) (x : ι → ℝ) :
    dotProduct y (ratCastMatrix S *ᵥ y) ≤
      dotProduct (Sum.elim x y)
        (Matrix.fromBlocks (ratCastMatrix A) (B.map (Rat.castHom ℝ))
          (B.map (Rat.castHom ℝ)).transpose (ratCastMatrix D) *ᵥ Sum.elim x y) := by
  rw [checkSchur_completed_energy A Q B X D S h hA x y]
  have hz : 0 ≤ dotProduct (x + X.map (Rat.castHom ℝ) *ᵥ y)
      (ratCastMatrix A *ᵥ (x + X.map (Rat.castHom ℝ) *ᵥ y)) := by
    by_cases hv : x + X.map (Rat.castHom ℝ) *ᵥ y = 0
    · rw [hv]
      simp
    · exact le_of_lt (by simpa using hA.dotProduct_mulVec_pos hv)
  linarith

/-- Equality holds exactly at the unique harmonic interior extension. -/
theorem checkSchur_energy_eq_iff (A Q : Matrix ι ι ℚ) (B X : Matrix ι κ ℚ)
    (D S : Matrix κ κ ℚ) (h : checkSchur A Q B X B.transpose D S = true)
    (hA : (ratCastMatrix A).PosDef) (y : κ → ℝ) (x : ι → ℝ) :
    dotProduct (Sum.elim x y)
      (Matrix.fromBlocks (ratCastMatrix A) (B.map (Rat.castHom ℝ))
        (B.map (Rat.castHom ℝ)).transpose (ratCastMatrix D) *ᵥ Sum.elim x y) =
      dotProduct y (ratCastMatrix S *ᵥ y) ↔
      x = -(X.map (Rat.castHom ℝ) *ᵥ y) := by
  rw [checkSchur_completed_energy A Q B X D S h hA x y]
  constructor
  · intro he
    have hz : x + X.map (Rat.castHom ℝ) *ᵥ y = 0 := by
      by_contra hn
      have hp : 0 < dotProduct (x + X.map (Rat.castHom ℝ) *ᵥ y)
          (ratCastMatrix A *ᵥ (x + X.map (Rat.castHom ℝ) *ᵥ y)) := by
        simpa using hA.dotProduct_mulVec_pos hn
      linarith
    exact add_eq_zero_iff_eq_neg.mp hz
  · intro hx
    simp [hx]

end SpectralGraph.Certificate
