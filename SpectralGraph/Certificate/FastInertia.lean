import Mathlib.LinearAlgebra.Matrix.Transvection
import SpectralGraph.Certificate.ExactDiagonalization
import SpectralGraph.Inertia.Restriction

/-!
# Fast, proof-producing rational inertia elimination

The full change-of-basis certificate is useful for auditing isolated matrices,
but carrying its increasingly large rational entries is too expensive in a
million-candidate census.  Here we prove the two elementary form operations
once.  The bulk checker then carries only the current symmetric form and
checks that the final result is diagonal.
-/

namespace SpectralGraph
namespace Certificate

/-- Congruence update obtained by replacing basis vector `target` by itself
plus `c` times basis vector `source`.  The entrywise formula is substantially
faster to execute than two generic matrix products. -/
def basisAddForm {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ)
    (source target : Fin n) (c : ℚ) : Matrix (Fin n) (Fin n) ℚ := fun i j ↦
  A i j +
    (if i = target then c * A source j else 0) +
    (if j = target then c * A i source else 0) +
    (if i = target ∧ j = target then c * c * A source source else 0)

/-- Simultaneously swap a row and its matching column. -/
def swapForm {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ) (a b : Fin n) :
    Matrix (Fin n) (Fin n) ℚ :=
  A.submatrix (Equiv.swap a b) (Equiv.swap a b)

private theorem transpose_transvection {n : Nat} (source target : Fin n) (c : ℝ) :
    (Matrix.transvection source target c).transpose =
      Matrix.transvection target source c := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases h : source = i ∧ target = i
    · simp [Matrix.transvection, Matrix.single, Matrix.transpose, h]
    · have h' : ¬(target = i ∧ source = i) := fun h' ↦ h ⟨h'.2, h'.1⟩
      simp [Matrix.transvection, Matrix.single, Matrix.transpose, h, h']
  · simp [Matrix.transvection, Matrix.single, Matrix.transpose, hij,
      Ne.symm hij, and_comm]

/-- One basis-addition update preserves semantic inertia. -/
theorem matrixInertia_basisAddForm {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℚ) (source target : Fin n) (c : ℚ)
    (hst : source ≠ target) :
    matrixInertia (ratCastMatrix (basisAddForm A source target c)) =
      matrixInertia (ratCastMatrix A) := by
  let AR : Matrix (Fin n) (Fin n) ℝ := ratCastMatrix A
  let E : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.transvection source target (c : ℝ)
  have hdetE : E.det = 1 := by
    exact Matrix.det_transvection_of_ne source target hst (c : ℝ)
  letI : Invertible E :=
    Matrix.invertibleOfIsUnitDet E (by rw [hdetE]; exact isUnit_one)
  have hcongr : ratCastMatrix (basisAddForm A source target c) =
      E.transpose * AR * E := by
    ext i j
    rw [show E.transpose = Matrix.transvection target source (c : ℝ) by
      exact transpose_transvection source target (c : ℝ)]
    change ratCastMatrix (basisAddForm A source target c) i j =
      ((Matrix.transvection target source (c : ℝ) * AR) *
        Matrix.transvection source target (c : ℝ)) i j
    by_cases hi : i = target
    · subst i
      by_cases hj : j = target
      · subst j
        rw [Matrix.mul_transvection_apply_same source target target,
          Matrix.transvection_mul_apply_same target source target,
          Matrix.transvection_mul_apply_same target source source]
        simp [basisAddForm, ratCastMatrix, AR]
        ring
      · rw [Matrix.mul_transvection_apply_of_ne source target target j hj,
          Matrix.transvection_mul_apply_same target source j]
        simp [basisAddForm, ratCastMatrix, AR, hj]
    · by_cases hj : j = target
      · subst j
        rw [Matrix.mul_transvection_apply_same source target i,
          Matrix.transvection_mul_apply_of_ne target source i target hi,
          Matrix.transvection_mul_apply_of_ne target source i source hi]
        simp [basisAddForm, ratCastMatrix, AR, hi]
      · rw [Matrix.mul_transvection_apply_of_ne source target i j hj,
          Matrix.transvection_mul_apply_of_ne target source i j hi]
        simp [basisAddForm, ratCastMatrix, AR, hi, hj]
  exact (matrixInertia_eq_of_congr AR
    (ratCastMatrix (basisAddForm A source target c)) E hcongr).symm

/-- A simultaneous coordinate swap preserves semantic inertia. -/
theorem matrixInertia_swapForm {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℚ) (a b : Fin n) :
    matrixInertia (ratCastMatrix (swapForm A a b)) =
      matrixInertia (ratCastMatrix A) := by
  simpa [swapForm, ratCastMatrix] using
    (Inertia.matrixInertia_submatrix_equiv (ratCastMatrix A) (Equiv.swap a b))

/-- Guarded basis addition.  The guard makes inertia preservation unconditional
and is erased to a cheap index comparison in native execution. -/
def safeBasisAddForm {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ)
    (source target : Fin n) (c : ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  if source = target then A else basisAddForm A source target c

theorem matrixInertia_safeBasisAddForm {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℚ) (source target : Fin n) (c : ℚ) :
    matrixInertia (ratCastMatrix (safeBasisAddForm A source target c)) =
      matrixInertia (ratCastMatrix A) := by
  by_cases h : source = target
  · simp [safeBasisAddForm, h]
  · simpa [safeBasisAddForm, h] using
      matrixInertia_basisAddForm A source target c h

def fastFindDiagonalPivot {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ)
    (k : Fin n) : Option (Fin n) :=
  (activeIndices k).find? fun i ↦ A i i ≠ 0

def fastFindOffDiagonalPivot {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ)
    (k : Fin n) : Option (Fin n × Fin n) :=
  ((activeIndices k).product (activeIndices k)).find? fun ij ↦
    ij.1 < ij.2 ∧ A ij.1 ij.2 ≠ 0

/-- Clear one pivot row using guarded elementary congruences. -/
def fastClearPivotRow {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ)
    (k : Fin n) : Matrix (Fin n) (Fin n) ℚ :=
  (laterIndices k).foldl (fun B j ↦
    if B k k = 0 then B
    else safeBasisAddForm B k j (-B k j / B k k)) A

private theorem matrixInertia_fastClearList {n : Nat} (k : Fin n)
    (js : List (Fin n)) (A : Matrix (Fin n) (Fin n) ℚ) :
    matrixInertia (ratCastMatrix
      (js.foldl (fun B j ↦ if B k k = 0 then B
        else safeBasisAddForm B k j (-B k j / B k k)) A)) =
      matrixInertia (ratCastMatrix A) := by
  induction js generalizing A with
  | nil => rfl
  | cons j js ih =>
      simp only [List.foldl_cons]
      let B := if A k k = 0 then A
        else safeBasisAddForm A k j (-A k j / A k k)
      calc
        matrixInertia (ratCastMatrix
            (js.foldl (fun B j ↦ if B k k = 0 then B
              else safeBasisAddForm B k j (-B k j / B k k)) B)) =
            matrixInertia (ratCastMatrix B) := ih B
        _ = matrixInertia (ratCastMatrix A) := by
          dsimp [B]
          by_cases h : A k k = 0
          · simp [h]
          · simpa [h] using matrixInertia_safeBasisAddForm
              A k j (-A k j / A k k)

theorem matrixInertia_fastClearPivotRow {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℚ) (k : Fin n) :
    matrixInertia (ratCastMatrix (fastClearPivotRow A k)) =
      matrixInertia (ratCastMatrix A) := by
  exact matrixInertia_fastClearList k (laterIndices k) A

/-- One fast symmetric pivot step. -/
def fastDiagonalizationStep {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ)
    (k : Fin n) : Matrix (Fin n) (Fin n) ℚ :=
  match fastFindDiagonalPivot A k with
  | some i => fastClearPivotRow (swapForm A k i) k
  | none =>
      match fastFindOffDiagonalPivot A k with
      | some (i, j) =>
          fastClearPivotRow (swapForm (safeBasisAddForm A j i 1) k i) k
      | none => A

theorem matrixInertia_fastDiagonalizationStep {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℚ) (k : Fin n) :
    matrixInertia (ratCastMatrix (fastDiagonalizationStep A k)) =
      matrixInertia (ratCastMatrix A) := by
  unfold fastDiagonalizationStep
  split
  · rename_i i hi
    rw [matrixInertia_fastClearPivotRow, matrixInertia_swapForm]
  · split
    · rename_i pair hp
      rcases pair with ⟨i, j⟩
      rw [matrixInertia_fastClearPivotRow, matrixInertia_swapForm,
        matrixInertia_safeBasisAddForm]
    · rfl

/-- Fast rational diagonalization carrying only the current form. -/
def fastDiagonalization {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  (finIndices n).foldl fastDiagonalizationStep A

private theorem matrixInertia_fastDiagonalizationList {n : Nat}
    (ks : List (Fin n)) (A : Matrix (Fin n) (Fin n) ℚ) :
    matrixInertia (ratCastMatrix (ks.foldl fastDiagonalizationStep A)) =
      matrixInertia (ratCastMatrix A) := by
  induction ks generalizing A with
  | nil => rfl
  | cons k ks ih =>
      simp only [List.foldl_cons]
      rw [ih, matrixInertia_fastDiagonalizationStep]

theorem matrixInertia_fastDiagonalization {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    matrixInertia (ratCastMatrix (fastDiagonalization A)) =
      matrixInertia (ratCastMatrix A) := by
  exact matrixInertia_fastDiagonalizationList (finIndices n) A

def matrixIsDiagonal {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ) : Prop :=
  ∀ i j, i ≠ j → A i j = 0

def matrixIsDiagonalBool {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ) : Bool :=
  decide (∀ i j, i ≠ j → A i j = 0)

theorem matrixIsDiagonalBool_eq_true_iff {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    matrixIsDiagonalBool A = true ↔ matrixIsDiagonal A := by
  simp [matrixIsDiagonalBool, matrixIsDiagonal]

def fastComputedInertia {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ) : Inertia :=
  rationalDiagonalInertia fun i ↦ (fastDiagonalization A) i i

def fastInertiaCertificateBool {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℚ) : Bool :=
  matrixIsDiagonalBool (fastDiagonalization A)

/-- Soundness theorem for the high-volume checker. -/
theorem matrixInertia_eq_fastComputedInertia {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℚ)
    (h : fastInertiaCertificateBool A = true) :
    matrixInertia (ratCastMatrix A) = fastComputedInertia A := by
  let D := fastDiagonalization A
  have hdiag : matrixIsDiagonal D :=
    (matrixIsDiagonalBool_eq_true_iff D).mp h
  have hDdiag : D = Matrix.diagonal (fun i ↦ D i i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · rw [hdiag i j hij]
      simp [hij]
  have hcast : ratCastMatrix D =
      Matrix.diagonal (fun i ↦ ((D i i : ℚ) : ℝ)) := by
    calc
      ratCastMatrix D = D.map (Rat.castHom ℝ) := rfl
      _ = (Matrix.diagonal fun i ↦ D i i).map (Rat.castHom ℝ) :=
        congrArg (fun M ↦ M.map (Rat.castHom ℝ)) hDdiag
      _ = Matrix.diagonal (fun i ↦ ((D i i : ℚ) : ℝ)) := by
        simp
  calc
    matrixInertia (ratCastMatrix A) = matrixInertia (ratCastMatrix D) :=
      (matrixInertia_fastDiagonalization A).symm
    _ = matrixInertia (Matrix.diagonal fun i ↦ ((D i i : ℚ) : ℝ)) := by
      rw [hcast]
    _ = rationalDiagonalInertia (fun i ↦ D i i) :=
      matrixInertia_ratCast_diagonal _
    _ = fastComputedInertia A := rfl

end Certificate
end SpectralGraph
