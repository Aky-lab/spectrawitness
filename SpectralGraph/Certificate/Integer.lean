import SpectralGraph.Certificate.FastInertia

/-! # Fraction-free integer inertia

A total exact algorithm on symmetric integer matrices. Its semantic
correctness is proved in `IntegerSound`. Missing array entries default
to zero; the checked public boundary additionally validates storage.
-/

namespace SpectralGraph
namespace Certificate

/-- A dense square integer matrix stored row-major. -/
structure DenseIntMatrix where
  order : Nat
  entries : Array Int
  deriving Repr

def DenseIntMatrix.entry (A : DenseIntMatrix) (i j : Nat) : Int :=
  A.entries[i * A.order + j]?.getD 0

/-- Mathematical rational matrix represented by a dense integer array. -/
def DenseIntMatrix.toRatMatrix (A : DenseIntMatrix) :
    Matrix (Fin A.order) (Fin A.order) ℚ := fun i j ↦ A.entry i j

def DenseIntMatrix.ofFn (n : Nat) (f : Nat → Nat → Int) : DenseIntMatrix :=
  ⟨n, Array.ofFn fun k : Fin (n * n) ↦ f (k / n) (k % n)⟩

def DenseIntMatrix.firstDiagonalPivotFin? (A : DenseIntMatrix) :
    Option (Fin A.order) :=
  (finIndices A.order).find? fun i ↦ A.entry i i ≠ 0

def DenseIntMatrix.firstOffDiagonalPivotFin? (A : DenseIntMatrix) :
    Option (Fin A.order × Fin A.order) :=
  ((finIndices A.order).product (finIndices A.order)).find?
    fun ij ↦ A.entry ij.1 ij.2 ≠ 0

/-- Integral congruence update replacing `target` by `target + source`. -/
def DenseIntMatrix.basisAddOne (A : DenseIntMatrix)
    (source target : Nat) : DenseIntMatrix :=
  DenseIntMatrix.ofFn A.order fun i j ↦
    A.entry i j +
      (if i = target then A.entry source j else 0) +
      (if j = target then A.entry i source else 0) +
      (if i = target ∧ j = target then A.entry source source else 0)

/-- Integer-normalized one-dimensional Schur remainder.  For a nonzero pivot
`a`, this is exactly `|a|` times the rational Schur complement, so its
semantic inertia is unchanged without any gcd bookkeeping. -/
def DenseIntMatrix.signedDiagonalRemainder (A : DenseIntMatrix) (pivot : Nat) :
    DenseIntMatrix :=
  let a := A.entry pivot pivot
  DenseIntMatrix.ofFn (A.order - 1) fun i j ↦
    let ii := if i + 1 = pivot then 0 else i + 1
    let jj := if j + 1 = pivot then 0 else j + 1
    if 0 < a then
      a * A.entry ii jj - A.entry ii pivot * A.entry pivot jj
    else
      (-a) * A.entry ii jj + A.entry ii pivot * A.entry pivot jj

def inertiaAddPositive (inertia : Inertia) : Inertia :=
  ⟨inertia.pos + 1, inertia.zero, inertia.neg⟩

def inertiaAddNegative (inertia : Inertia) : Inertia :=
  ⟨inertia.pos, inertia.zero, inertia.neg + 1⟩

/-- One-coordinate-at-a-time integer implementation aligned with the simple
rational Schur specification.  A zero-diagonal off-diagonal pivot is first
turned into a nonzero diagonal pivot by an integral basis addition. -/
def discoverIntegerInertiaV2Aux : Nat → DenseIntMatrix → Inertia
  | 0, A => ⟨0, A.order, 0⟩
  | fuel + 1, A =>
      if A.order = 0 then ⟨0, 0, 0⟩
      else
        match A.firstDiagonalPivotFin? with
        | some pivot =>
            let a := A.entry pivot pivot
            let tail := discoverIntegerInertiaV2Aux fuel
              (A.signedDiagonalRemainder pivot)
            if 0 < a then inertiaAddPositive tail else inertiaAddNegative tail
        | none =>
            match A.firstOffDiagonalPivotFin? with
            | some (first, second) =>
                let B := A.basisAddOne second first
                let a := B.entry first first
                let tail := discoverIntegerInertiaV2Aux fuel
                  (B.signedDiagonalRemainder first)
                if 0 < a then inertiaAddPositive tail else inertiaAddNegative tail
            | none => ⟨0, A.order, 0⟩

def discoverIntegerInertiaV2 (A : DenseIntMatrix) : Inertia :=
  discoverIntegerInertiaV2Aux A.order A


end Certificate
end SpectralGraph
