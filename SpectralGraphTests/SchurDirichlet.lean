import SpectralGraph.Certificate.SchurDirichlet
import SpectralGraphTests.Applications.WheatstoneDirichlet
import Mathlib.Data.Real.StarOrdered

/-! Dimension, sign, positivity, and strict-checker boundaries for Dirichlet elimination. -/

namespace SpectralGraphTests.SchurDirichlet
open Matrix SpectralGraph.Certificate

namespace EmptyInterior
def A : Matrix (Fin 0) (Fin 0) ℚ := 0
def Q : Matrix (Fin 0) (Fin 0) ℚ := 0
def B : Matrix (Fin 0) Bool ℚ := 0
def X : Matrix (Fin 0) Bool ℚ := 0
def D : Matrix Bool Bool ℚ := 1
def S : Matrix Bool Bool ℚ := 1
theorem checked : checkSchur A Q B X B.transpose D S = true := by decide +kernel
theorem pivot_posDef : (ratCastMatrix A).PosDef := by
  have hz : ratCastMatrix A = (1 : Matrix (Fin 0) (Fin 0) ℝ) := by
    ext i
    exact Fin.elim0 i
  rw [hz]
  exact Matrix.PosDef.one
theorem response (y : Bool → ℝ) :
    Matrix.fromBlocks (ratCastMatrix A) (B.map (Rat.castHom ℝ))
      (B.map (Rat.castHom ℝ)).transpose (ratCastMatrix D) *ᵥ
        Sum.elim (-(X.map (Rat.castHom ℝ) *ᵥ y)) y =
      Sum.elim (0 : Fin 0 → ℝ) (ratCastMatrix S *ᵥ y) :=
  checkSchur_harmonic_response A Q B X D S checked y
theorem energy (y : Bool → ℝ) (x : Fin 0 → ℝ) :
    dotProduct y (ratCastMatrix S *ᵥ y) ≤
      dotProduct (Sum.elim x y)
        (Matrix.fromBlocks (ratCastMatrix A) (B.map (Rat.castHom ℝ))
          (B.map (Rat.castHom ℝ)).transpose (ratCastMatrix D) *ᵥ Sum.elim x y) :=
  checkSchur_energy_min A Q B X D S checked pivot_posDef y x
theorem unique (y : Bool → ℝ) (x : Fin 0 → ℝ) :
    dotProduct (Sum.elim x y)
      (Matrix.fromBlocks (ratCastMatrix A) (B.map (Rat.castHom ℝ))
        (B.map (Rat.castHom ℝ)).transpose (ratCastMatrix D) *ᵥ Sum.elim x y) =
      dotProduct y (ratCastMatrix S *ᵥ y) := by
  apply (checkSchur_energy_eq_iff A Q B X D S checked pivot_posDef y x).2
  exact Subsingleton.elim _ _
end EmptyInterior

namespace EmptyTerminal
def A : Matrix (Fin 1) (Fin 1) ℚ := 1
def Q : Matrix (Fin 1) (Fin 1) ℚ := 1
def B : Matrix (Fin 1) (Fin 0) ℚ := 0
def X : Matrix (Fin 1) (Fin 0) ℚ := 0
def D : Matrix (Fin 0) (Fin 0) ℚ := 0
def S : Matrix (Fin 0) (Fin 0) ℚ := 0
theorem checked : checkSchur A Q B X B.transpose D S = true := by decide +kernel
theorem pivot_posDef : (ratCastMatrix A).PosDef := by
  have hz : ratCastMatrix A = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [ratCastMatrix, A, Matrix.natCast_apply]
  rw [hz]
  exact Matrix.PosDef.one
theorem unique_zero (x : Fin 1 → ℝ) (y : Fin 0 → ℝ) :
    dotProduct (Sum.elim x y)
      (Matrix.fromBlocks (ratCastMatrix A) (B.map (Rat.castHom ℝ))
        (B.map (Rat.castHom ℝ)).transpose (ratCastMatrix D) *ᵥ Sum.elim x y) =
      dotProduct y (ratCastMatrix S *ᵥ y) ↔ x = 0 := by
  simpa [X] using checkSchur_energy_eq_iff A Q B X D S checked pivot_posDef y x
end EmptyTerminal

namespace Rectangular
def A : Matrix (Fin 1) (Fin 1) ℚ := !![2]
def Q : Matrix (Fin 1) (Fin 1) ℚ := !![1/2]
def B : Matrix (Fin 1) Bool ℚ := fun _ _ => -1
def X : Matrix (Fin 1) Bool ℚ := fun _ _ => -1/2
def D : Matrix Bool Bool ℚ := 1
def S : Matrix Bool Bool ℚ := fun i j => if i = j then 1/2 else -1/2
theorem checked : checkSchur A Q B X B.transpose D S = true := by decide +kernel
theorem pivot_posDef : (ratCastMatrix A).PosDef := by
  have hz : ratCastMatrix A = (2 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [ratCastMatrix, A, Matrix.ofNat_apply]
  rw [hz]
  exact Matrix.PosDef.natCast 2 (by decide)
theorem response (y : Bool → ℝ) :
    Matrix.fromBlocks (ratCastMatrix A) (B.map (Rat.castHom ℝ))
      (B.map (Rat.castHom ℝ)).transpose (ratCastMatrix D) *ᵥ
        Sum.elim (-(X.map (Rat.castHom ℝ) *ᵥ y)) y =
      Sum.elim (0 : Fin 1 → ℝ) (ratCastMatrix S *ᵥ y) :=
  checkSchur_harmonic_response A Q B X D S checked y
theorem energy (y : Bool → ℝ) (x : Fin 1 → ℝ) :
    dotProduct y (ratCastMatrix S *ᵥ y) ≤
      dotProduct (Sum.elim x y)
        (Matrix.fromBlocks (ratCastMatrix A) (B.map (Rat.castHom ℝ))
          (B.map (Rat.castHom ℝ)).transpose (ratCastMatrix D) *ᵥ Sum.elim x y) :=
  checkSchur_energy_min A Q B X D S checked pivot_posDef y x
theorem equality (y : Bool → ℝ) (x : Fin 1 → ℝ) :
    dotProduct (Sum.elim x y)
      (Matrix.fromBlocks (ratCastMatrix A) (B.map (Rat.castHom ℝ))
        (B.map (Rat.castHom ℝ)).transpose (ratCastMatrix D) *ᵥ Sum.elim x y) =
      dotProduct y (ratCastMatrix S *ᵥ y) ↔
        x = -(X.map (Rat.castHom ℝ) *ᵥ y) :=
  checkSchur_energy_eq_iff A Q B X D S checked pivot_posDef y x
end Rectangular

namespace ZeroCoupling
def A : Matrix (Fin 1) (Fin 1) ℚ := 1
def Q : Matrix (Fin 1) (Fin 1) ℚ := 1
def B : Matrix (Fin 1) (Fin 1) ℚ := 0
def X : Matrix (Fin 1) (Fin 1) ℚ := 0
def D : Matrix (Fin 1) (Fin 1) ℚ := -1
def S : Matrix (Fin 1) (Fin 1) ℚ := -1
theorem checked : checkSchur A Q B X B.transpose D S = true := by decide +kernel
theorem pivot_posDef : (ratCastMatrix A).PosDef := by
  have hz : ratCastMatrix A = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [ratCastMatrix, A]
  rw [hz]
  exact Matrix.PosDef.one
theorem unique_zero (y x : Fin 1 → ℝ) :
    dotProduct (Sum.elim x y)
      (Matrix.fromBlocks (ratCastMatrix A) (B.map (Rat.castHom ℝ))
        (B.map (Rat.castHom ℝ)).transpose (ratCastMatrix D) *ᵥ Sum.elim x y) =
      dotProduct y (ratCastMatrix S *ᵥ y) ↔ x = 0 := by
  simpa [X] using checkSchur_energy_eq_iff A Q B X D S checked pivot_posDef y x
end ZeroCoupling

namespace NegativePivot
def A : Matrix (Fin 1) (Fin 1) ℚ := -1
def Q : Matrix (Fin 1) (Fin 1) ℚ := -1
def B : Matrix (Fin 1) (Fin 1) ℚ := 0
def X : Matrix (Fin 1) (Fin 1) ℚ := 0
def D : Matrix (Fin 1) (Fin 1) ℚ := 0
def S : Matrix (Fin 1) (Fin 1) ℚ := 0
theorem checked : checkSchur A Q B X B.transpose D S = true := by decide +kernel
theorem response (y : Fin 1 → ℝ) :
    Matrix.fromBlocks (ratCastMatrix A) (B.map (Rat.castHom ℝ))
      (B.map (Rat.castHom ℝ)).transpose (ratCastMatrix D) *ᵥ
        Sum.elim (-(X.map (Rat.castHom ℝ) *ᵥ y)) y =
      Sum.elim (0 : Fin 1 → ℝ) (ratCastMatrix S *ᵥ y) :=
  checkSchur_harmonic_response A Q B X D S checked y
theorem below_false_minimum :
    dotProduct (Sum.elim ![1] ![0])
      (Matrix.fromBlocks (ratCastMatrix A) (B.map (Rat.castHom ℝ))
        (B.map (Rat.castHom ℝ)).transpose (ratCastMatrix D) *ᵥ Sum.elim ![1] ![0]) = -1 ∧
    dotProduct ![0] (ratCastMatrix S *ᵥ ![0]) = (0 : ℝ) := by
  constructor <;> norm_num [A, B, D, S, ratCastMatrix, Matrix.fromBlocks,
    Matrix.mulVec, dotProduct, Matrix.of_apply, Matrix.vecHead, Matrix.vecTail]
end NegativePivot

namespace SingularPivot
def A : Matrix (Fin 1) (Fin 1) ℚ := 0
def Q : Matrix (Fin 1) (Fin 1) ℚ := 0
def B : Matrix (Fin 1) (Fin 1) ℚ := 0
def X : Matrix (Fin 1) (Fin 1) ℚ := 0
def D : Matrix (Fin 1) (Fin 1) ℚ := 0
def S : Matrix (Fin 1) (Fin 1) ℚ := 0
theorem consistent_solve : A * X = B := by decide +kernel
theorem rejected : checkSchur A Q B X B.transpose D S = false := by decide +kernel
end SingularPivot

namespace BothEmpty
def A : Matrix (Fin 0) (Fin 0) ℚ := 0
def Q : Matrix (Fin 0) (Fin 0) ℚ := 0
def B : Matrix (Fin 0) (Fin 0) ℚ := 0
def X : Matrix (Fin 0) (Fin 0) ℚ := 0
def D : Matrix (Fin 0) (Fin 0) ℚ := 0
def S : Matrix (Fin 0) (Fin 0) ℚ := 0
theorem checked : checkSchur A Q B X B.transpose D S = true := by decide +kernel
theorem pivot_posDef : (ratCastMatrix A).PosDef := by
  have hz : ratCastMatrix A = (1 : Matrix (Fin 0) (Fin 0) ℝ) := by
    ext i
    exact Fin.elim0 i
  rw [hz]
  exact Matrix.PosDef.one
theorem response (y : Fin 0 → ℝ) :
    Matrix.fromBlocks (ratCastMatrix A) (B.map (Rat.castHom ℝ))
      (B.map (Rat.castHom ℝ)).transpose (ratCastMatrix D) *ᵥ
        Sum.elim (-(X.map (Rat.castHom ℝ) *ᵥ y)) y =
      Sum.elim (0 : Fin 0 → ℝ) (ratCastMatrix S *ᵥ y) :=
  checkSchur_harmonic_response A Q B X D S checked y
end BothEmpty

namespace Boundaries
open SpectralGraphTests.Dirichlet
theorem wrong_Q_rejected :
    checkSchur A (0 : Matrix (Fin 2) (Fin 2) ℚ) B X B.transpose D S = false := by
  decide +kernel
theorem wrong_X_rejected :
    checkSchur A Q B (0 : Matrix (Fin 2) (Fin 2) ℚ) B.transpose D S = false := by
  decide +kernel
theorem wrong_S_rejected :
    checkSchur A Q B X B.transpose D (0 : Matrix (Fin 2) (Fin 2) ℚ) = false := by
  decide +kernel
theorem unit_interior_edge_current_nonzero :
    ((5/11 : ℝ) - (4/11 : ℝ)) ≠ 0 := by norm_num
theorem bridge_full_singular :
    ∃ z : V → ℝ, z ≠ 0 ∧ weightedBridge *ᵥ z = 0 :=
  ⟨fun _ => 1, weightedBridge_nonzero_constant, constant_kernel⟩
theorem equal_boundary_zero (a : ℝ) :
    dotProduct (Sum.elim (harmonic a a) ![a,a])
      (weightedBridge *ᵥ Sum.elim (harmonic a a) ![a,a]) = 0 ∧
    weightedBridge *ᵥ Sum.elim (harmonic a a) ![a,a] = 0 :=
  ⟨equal_terminal_energy a, equal_terminal_current a⟩
theorem negative_terminal_value :
    dotProduct ![(1:ℝ)] (ratCastMatrix ZeroCoupling.S *ᵥ ![(1:ℝ)]) = -1 := by
  norm_num [ZeroCoupling.S, ratCastMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]
end Boundaries

end SpectralGraphTests.SchurDirichlet
