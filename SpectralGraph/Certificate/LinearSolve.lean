import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Block

/-!
# Exact certificates for inverse bilinear forms and Schur complements

An external solver supplies solutions, not a trusted inverse calculation.
Invertibility is an explicit obligation: a solution to a singular system
does not in general represent mathlib's totalized inverse.

This generalizes the all-ones inverse quadratic certificate
to arbitrary left/right vectors, arbitrary fields, and multiple right-hand
sides. The latter verifies Schur complements without computing an inverse.
-/

namespace SpectralGraph.Certificate
open Matrix

variable {K ι κ : Type*} [Field K]
variable [Fintype ι] [DecidableEq ι]

/-- The inverse bilinear form; setting `u = v` gives an inverse quadratic form. -/
noncomputable def inverseBilinear (A : Matrix ι ι K) (u v : ι → K) : K :=
  u ⬝ᵥ A⁻¹ *ᵥ v

/-- A checked solution is the inverse solution when the matrix is invertible. -/
theorem inverse_mulVec_eq_of_solve (A : Matrix ι ι K) (v x : ι → K)
    (unit : IsUnit A.det) (solve : A *ᵥ x = v) : A⁻¹ *ᵥ v = x := by
  rw [← solve, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A unit, Matrix.one_mulVec]

/-- Solution certificates need only a matrix-vector product and a scalar dot
product once invertibility has been established by any method. -/
theorem inverseBilinear_eq_of_solve (A : Matrix ι ι K) (u v x : ι → K)
    (target : K) (unit : IsUnit A.det)
    (solve : A *ᵥ x = v) (value : u ⬝ᵥ x = target) :
    inverseBilinear A u v = target := by
  rw [inverseBilinear, inverse_mulVec_eq_of_solve A v x unit solve, value]

/-- Self-contained determinant-based certificate checker. -/
def checkInverseBilinear [DecidableEq K] (A : Matrix ι ι K)
    (u v x : ι → K) (target : K) : Bool :=
  decide (A.det ≠ 0 ∧ A *ᵥ x = v ∧ u ⬝ᵥ x = target)

/-- Soundness of the self-contained inverse bilinear certificate. -/
theorem checkInverseBilinear_sound [DecidableEq K] (A : Matrix ι ι K)
    (u v x : ι → K) (target : K)
    (h : checkInverseBilinear A u v x target = true) :
    inverseBilinear A u v = target := by
  have h' : A.det ≠ 0 ∧ A *ᵥ x = v ∧ u ⬝ᵥ x = target := of_decide_eq_true h
  exact inverseBilinear_eq_of_solve A u v x target
    (isUnit_iff_ne_zero.mpr h'.1) h'.2.1 h'.2.2

/-- Check an alleged left inverse instead of expanding a determinant. This
alternative can amortize inverse data over many vectors. -/
def checkInverseBilinearWithInverse [DecidableEq K] (A Q : Matrix ι ι K)
    (u v x : ι → K) (target : K) : Bool :=
  decide (Q * A = 1 ∧ A *ᵥ x = v ∧ u ⬝ᵥ x = target)

/-- A left inverse certificate independently proves invertibility. -/
theorem checkInverseBilinearWithInverse_sound [DecidableEq K]
    (A Q : Matrix ι ι K) (u v x : ι → K) (target : K)
    (h : checkInverseBilinearWithInverse A Q u v x target = true) :
    inverseBilinear A u v = target := by
  have h' : Q * A = 1 ∧ A *ᵥ x = v ∧ u ⬝ᵥ x = target := of_decide_eq_true h
  letI : Invertible A := invertibleOfLeftInverse A Q h'.1
  exact inverseBilinear_eq_of_solve A u v x target
    ((Matrix.isUnit_iff_isUnit_det A).mp (isUnit_of_invertible A)) h'.2.1 h'.2.2

variable [Fintype κ] [DecidableEq κ]

omit [Fintype κ] [DecidableEq κ] in
/-- A multiple-right-hand-side solve identifies the inverse product. -/
theorem inverse_mul_eq_of_solve (A : Matrix ι ι K) (B X : Matrix ι κ K)
    (unit : IsUnit A.det) (solve : A * X = B) : A⁻¹ * B = X := by
  rw [← solve, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul A unit, Matrix.one_mul]

omit [Fintype κ] [DecidableEq κ] in
/-- Exact Schur complement certification by solving `A X = B`. No symmetry
is required, and the lower-left block `C` is independent of `B`. -/
theorem schur_eq_of_solve (A : Matrix ι ι K) (B X : Matrix ι κ K)
    (C : Matrix κ ι K) (D S : Matrix κ κ K)
    (unit : IsUnit A.det) (solve : A * X = B) (value : D - C * X = S) :
    D - C * A⁻¹ * B = S := by
  rw [Matrix.mul_assoc C, inverse_mul_eq_of_solve A B X unit solve, value]

/-- Executable verification of a claimed Schur complement using a left
inverse and a supplied block solution. -/
def checkSchur [DecidableEq K] (A Q : Matrix ι ι K) (B X : Matrix ι κ K)
    (C : Matrix κ ι K) (D S : Matrix κ κ K) : Bool :=
  decide (Q * A = 1 ∧ A * X = B ∧ D - C * X = S)

omit [DecidableEq κ] in
theorem checkSchur_sound [DecidableEq K] (A Q : Matrix ι ι K)
    (B X : Matrix ι κ K) (C : Matrix κ ι K) (D S : Matrix κ κ K)
    (h : checkSchur A Q B X C D S = true) : D - C * A⁻¹ * B = S := by
  have h' : Q * A = 1 ∧ A * X = B ∧ D - C * X = S := of_decide_eq_true h
  letI : Invertible A := invertibleOfLeftInverse A Q h'.1
  exact schur_eq_of_solve A B X C D S
    ((Matrix.isUnit_iff_isUnit_det A).mp (isUnit_of_invertible A)) h'.2.1 h'.2.2

end SpectralGraph.Certificate
