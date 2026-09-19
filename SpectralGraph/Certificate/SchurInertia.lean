import SpectralGraph.Certificate.FastInertia
import SpectralGraph.Inertia.SchurComplement

/-!
# Exact recursive Schur inertia

A compact mathematical/executable specification for symmetric rational
elimination.  Each recursive call removes one coordinate; the optimized dense
integer implementation can refine this specification without exposing its
array or gcd-normalization details downstream.
-/

namespace SpectralGraph
namespace Certificate

open Matrix

def rationalSchurRemainder {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (pivot : Fin (n + 1)) :
    Matrix (Fin n) (Fin n) ℚ :=
  let B := swapForm A 0 pivot
  fun i j ↦ B i.succ j.succ - B i.succ 0 * B 0 j.succ / B 0 0

theorem rationalSchurRemainder_isSymm {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (pivot : Fin (n + 1))
    (hA : A.IsSymm) : (rationalSchurRemainder A pivot).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  have hB : (swapForm A 0 pivot).IsSymm := hA.submatrix _
  simp only [rationalSchurRemainder]
  rw [hB.apply i.succ j.succ, hB.apply i.succ 0,
    hB.apply 0 j.succ]
  ring

/-- Semantic inertia recurrence for a nonzero rational diagonal pivot. -/
theorem matrixInertia_rationalSchurRemainder {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (pivot : Fin (n + 1))
    (hA : A.IsSymm) (hpivot : A pivot pivot ≠ 0) :
    matrixInertia (ratCastMatrix A) =
      let tail := matrixInertia
        (ratCastMatrix (rationalSchurRemainder A pivot))
      if 0 < A pivot pivot then
        { pos := tail.pos + 1, zero := tail.zero, neg := tail.neg }
      else
        { pos := tail.pos, zero := tail.zero, neg := tail.neg + 1 } := by
  let Bq := swapForm A 0 pivot
  let B := ratCastMatrix Bq
  let a : ℝ := B 0 0
  let P : Matrix (Fin 1) (Fin 1) ℝ := Matrix.diagonal fun _ ↦ a
  let C : Matrix (Fin 1) (Fin n) ℝ := fun _ j ↦ B 0 j.succ
  let D : Matrix (Fin n) (Fin n) ℝ := fun i j ↦ B i.succ j.succ
  have ha : a ≠ 0 := by
    dsimp [a, B, Bq, ratCastMatrix, swapForm]
    simpa using hpivot
  letI : Invertible a := invertibleOfNonzero ha
  letI : Invertible (fun _ : Fin 1 => a) := {
    invOf := fun _ ↦ a⁻¹
    invOf_mul_self := by funext i; simp [ha]
    mul_invOf_self := by funext i; simp [ha] }
  letI : Invertible P := Matrix.diagonalInvertible _
  have hP : P.IsSymm := by
    simp [P]
  have hBsymm : B.IsSymm := by
    exact hA.submatrix _ |>.map (Rat.castHom ℝ)
  let e : Fin 1 ⊕ Fin n ≃ Fin (n + 1) :=
    finSumFinEquiv.trans (finCongr (Nat.one_add n))
  have heLeft (i : Fin 1) : e (Sum.inl i) = 0 := by
    fin_cases i
    apply Fin.ext
    simp [e]
  have heRight (i : Fin n) : e (Sum.inr i) = i.succ := by
    apply Fin.ext
    simp [e]
  have hblock : Matrix.fromBlocks P C C.transpose D =
      B.submatrix e e := by
    ext (i | i) (j | j)
    · fin_cases i
      fin_cases j
      simp [P, C, D, a, heLeft]
    · fin_cases i
      simp [P, C, D, heLeft, heRight]
    · fin_cases j
      simp [P, C, D, heLeft, heRight]
      exact hBsymm.apply i.succ 0
    · simp [P, C, D, heRight]
  have htail : D - C.transpose * ⅟ P * C =
      ratCastMatrix (rationalSchurRemainder A pivot) := by
    ext i j
    have hs := hBsymm.apply i.succ 0
    simp [B, Bq, ratCastMatrix] at hs
    simp [P, C, D, rationalSchurRemainder, B, Bq, a,
      ratCastMatrix, Matrix.mul_apply]
    rw [hs]
    ring
  have hschur := Inertia.matrixInertia_fromBlocks_schur₁₁ P C D hP
  rw [hblock, Inertia.matrixInertia_submatrix_equiv] at hschur
  rw [htail] at hschur
  have hswap : matrixInertia B = matrixInertia (ratCastMatrix A) :=
    matrixInertia_swapForm A 0 pivot
  rw [← hswap]
  rw [hschur]
  have hPpos : 0 < A pivot pivot →
      matrixInertia P = { pos := 1, zero := 0, neg := 0 } := by
    intro h
    have hz : A pivot pivot ≠ 0 := ne_of_gt h
    have hle : 0 ≤ A pivot pivot := h.le
    rw [matrixInertia_diagonal]
    simp [a, B, Bq, ratCastMatrix, swapForm, h, hz, hle]
  have hPneg : ¬ 0 < A pivot pivot →
      matrixInertia P = { pos := 0, zero := 0, neg := 1 } := by
    intro h
    have hn : A pivot pivot < 0 := lt_of_le_of_ne (not_lt.mp h) hpivot
    have hz : A pivot pivot ≠ 0 := ne_of_lt hn
    have hle : A pivot pivot ≤ 0 := hn.le
    rw [matrixInertia_diagonal]
    simp [a, B, Bq, ratCastMatrix, swapForm, hn, hz, hle]
  split
  · rename_i h
    rw [hPpos h]
    rfl
  · rename_i h
    rw [hPneg h]
    rfl

def firstRationalDiagonalPivot? {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℚ) : Option (Fin n) :=
  (finIndices n).find? fun i ↦ A i i ≠ 0

def firstRationalNonzeroEntry? {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℚ) : Option (Fin n × Fin n) :=
  ((finIndices n).product (finIndices n)).find? fun ij ↦ A ij.1 ij.2 ≠ 0

def addRationalPivotInertia (a : ℚ) (tail : Inertia) : Inertia :=
  if 0 < a then
    { pos := tail.pos + 1, zero := tail.zero, neg := tail.neg }
  else
    { pos := tail.pos, zero := tail.zero, neg := tail.neg + 1 }

/-- Exact recursive rational Schur elimination.  This is deliberately simple
enough to serve as the mathematical executable specification. -/
def discoverRationalSchurInertia : (n : Nat) →
    Matrix (Fin n) (Fin n) ℚ → Inertia
  | 0, _ => { pos := 0, zero := 0, neg := 0 }
  | n + 1, A =>
      match firstRationalDiagonalPivot? A with
      | some pivot =>
          addRationalPivotInertia (A pivot pivot)
            (discoverRationalSchurInertia n
              (rationalSchurRemainder A pivot))
      | none =>
          match firstRationalNonzeroEntry? A with
          | some (i, j) =>
              let B := basisAddForm A j i 1
              addRationalPivotInertia (B i i)
                (discoverRationalSchurInertia n
                  (rationalSchurRemainder B i))
          | none => { pos := 0, zero := n + 1, neg := 0 }

end Certificate
end SpectralGraph
