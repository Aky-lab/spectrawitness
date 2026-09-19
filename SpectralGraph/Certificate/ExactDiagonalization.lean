import SpectralGraph.Certificate.ExactInertia

/-!
# Executable rational congruence diagonalization

This module supplies the untrusted certificate generator used by the finite
searches.  It performs symmetric Gaussian elimination over `ℚ`, carrying a
change-of-basis matrix and its alleged inverse.  Soundness never depends on
the implementation below: `CertifiesInertiaWithInverse` recomputes and checks
both matrix identities exactly before its theorem can be applied.
-/

namespace SpectralGraph
namespace Certificate

/-- Working state for exact symmetric elimination. -/
structure DiagonalizationState (n : Nat) where
  form : Matrix (Fin n) (Fin n) ℚ
  change : Matrix (Fin n) (Fin n) ℚ
  changeInv : Matrix (Fin n) (Fin n) ℚ

namespace DiagonalizationState

/-- Swap two basis coordinates. -/
def swap {n : Nat} (S : DiagonalizationState n) (a b : Fin n) :
    DiagonalizationState n :=
  let σ : Fin n → Fin n := fun i ↦ if i = a then b else if i = b then a else i
  { form := fun i j ↦ S.form (σ i) (σ j)
    change := fun i j ↦ S.change i (σ j)
    changeInv := fun i j ↦ S.changeInv (σ i) j }

/-- Replace basis vector `target` by itself plus `c` times basis vector
`source`, updating the form and the alleged inverse simultaneously. -/
def addBasis {n : Nat} (S : DiagonalizationState n)
    (source target : Fin n) (c : ℚ) : DiagonalizationState n :=
  { form := fun i j ↦
      S.form i j +
        (if i = target then c * S.form source j else 0) +
        (if j = target then c * S.form i source else 0) +
        (if i = target ∧ j = target then c * c * S.form source source else 0)
    change := fun i j ↦
      if j = target then S.change i j + c * S.change i source else S.change i j
    changeInv := fun i j ↦
      if i = source then S.changeInv i j - c * S.changeInv target j else S.changeInv i j }

end DiagonalizationState

/-- The ordered list of coordinates of `Fin n`. -/
def finIndices (n : Nat) : List (Fin n) := List.ofFn fun i ↦ i

/-- Coordinates at or after `k`. -/
def activeIndices {n : Nat} (k : Fin n) : List (Fin n) :=
  (finIndices n).filter fun i ↦ k ≤ i

/-- Coordinates strictly after `k`. -/
def laterIndices {n : Nat} (k : Fin n) : List (Fin n) :=
  (finIndices n).filter fun i ↦ k < i

/-- Find a nonzero diagonal entry in the active trailing block. -/
def findDiagonalPivot {n : Nat} (S : DiagonalizationState n) (k : Fin n) :
    Option (Fin n) :=
  (activeIndices k).find? fun i ↦ S.form i i ≠ 0

/-- If every active diagonal is zero, find a nonzero off-diagonal entry. -/
def findOffDiagonalPivot {n : Nat} (S : DiagonalizationState n) (k : Fin n) :
    Option (Fin n × Fin n) :=
  ((activeIndices k).product (activeIndices k)).find? fun ij ↦
    ij.1 < ij.2 ∧ S.form ij.1 ij.2 ≠ 0

/-- Clear the entries to the right of a verified nonzero diagonal pivot. -/
def clearPivotRow {n : Nat} (S : DiagonalizationState n) (k : Fin n) :
    DiagonalizationState n :=
  (laterIndices k).foldl (fun T j ↦
    if T.form k k = 0 then T
    else T.addBasis k j (-T.form k j / T.form k k)) S

/-- One pivot step.  A zero-diagonal nonzero trailing block is converted to
a diagonal pivot by replacing one basis vector with the sum of two basis
vectors. -/
def diagonalizationStep {n : Nat} (S : DiagonalizationState n) (k : Fin n) :
    DiagonalizationState n :=
  match findDiagonalPivot S k with
  | some i => clearPivotRow (S.swap k i) k
  | none =>
      match findOffDiagonalPivot S k with
      | some (i, j) => clearPivotRow ((S.addBasis j i 1).swap k i) k
      | none => S

/-- Produce an exact rational diagonalization proposal. -/
def exactDiagonalization {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ) :
    DiagonalizationState n :=
  (finIndices n).foldl diagonalizationStep
    { form := A, change := 1, changeInv := 1 }

/-- The inertia proposed by the executable diagonalization routine. -/
def computedRationalInertia {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ) : Inertia :=
  let S := exactDiagonalization A
  rationalDiagonalInertia fun i ↦ S.form i i

/-- The fully checked proposition emitted for one matrix by the executable
diagonalizer. -/
def exactDiagonalizationCertificate {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℚ) : Prop :=
  let S := exactDiagonalization A
  CertifiesInertiaWithInverse A S.change S.changeInv
    (computedRationalInertia A)

/-- Executable Boolean form of `exactDiagonalizationCertificate`. -/
def exactDiagonalizationCertificateBool {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℚ) : Bool :=
  let S := exactDiagonalization A
  decide (S.changeInv * S.change = 1 ∧
    (∀ i j, i ≠ j → (S.change.transpose * A * S.change) i j = 0) ∧
      rationalDiagonalInertia
        (fun i ↦ (S.change.transpose * A * S.change) i i) =
          computedRationalInertia A)

theorem exactDiagonalizationCertificateBool_eq_true_iff {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    exactDiagonalizationCertificateBool A = true ↔
      exactDiagonalizationCertificate A := by
  simp [exactDiagonalizationCertificateBool, exactDiagonalizationCertificate,
    CertifiesInertiaWithInverse]

/-- Once the executable proposal has passed the exact checker, its computed
inertia is the semantic inertia of the real matrix. -/
theorem matrixInertia_eq_computedRationalInertia {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℚ)
    (h : exactDiagonalizationCertificate A) :
    matrixInertia (ratCastMatrix A) = computedRationalInertia A := by
  exact matrixInertia_eq_of_certifiesInertiaWithInverse
    A (exactDiagonalization A).change (exactDiagonalization A).changeInv
      (computedRationalInertia A) h

end Certificate
end SpectralGraph
