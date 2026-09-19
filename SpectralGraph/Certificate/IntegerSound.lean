import SpectralGraph.Certificate.Integer
import SpectralGraph.Certificate.SchurInertia

/-!
# Soundness of dense fraction-free integer inertia

The array implementation is proved against the recursive rational Schur
specification.  Downstream graph certificates depend only on the resulting
semantic `matrixInertia` theorem.
-/

namespace SpectralGraph
namespace Certificate

@[simp] theorem DenseIntMatrix.entry_ofFn (n : Nat) (f : Nat → Nat → Int)
    (i j : Nat) (hi : i < n) (hj : j < n) :
    (DenseIntMatrix.ofFn n f).entry i j = f i j := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i) hi
  have hk : i * n + j < n * n := by nlinarith
  change ((Array.ofFn fun k : Fin (n * n) ↦
    f (k / n) (k % n))[i * n + j]?).getD 0 = f i j
  have hk' : i * n + j < (Array.ofFn fun k : Fin (n * n) ↦
      f (k / n) (k % n)).size := by simpa using hk
  rw [Array.getElem?_eq_getElem hk']
  simp [Nat.mul_comm i n, Nat.mul_add_div hn, Nat.div_eq_of_lt hj,
    Nat.mod_eq_of_lt hj]

theorem DenseIntMatrix.basisAddOne_toRatMatrix {n : Nat}
    (entries : Array Int) (source target : Fin n) :
    let A : DenseIntMatrix := ⟨n, entries⟩
    (A.basisAddOne source target).toRatMatrix =
      basisAddForm A.toRatMatrix source target 1 := by
  dsimp
  ext i j
  unfold DenseIntMatrix.basisAddOne DenseIntMatrix.toRatMatrix
  rw [DenseIntMatrix.entry_ofFn n _ i j i.isLt j.isLt]
  have hiEq : (i.val = target.val) ↔ i = target :=
    ⟨Fin.ext, fun h ↦ congrArg Fin.val h⟩
  have hjEq : (j.val = target.val) ↔ j = target :=
    ⟨Fin.ext, fun h ↦ congrArg Fin.val h⟩
  simp only [basisAddForm, hiEq, hjEq]
  push_cast
  simp
  rfl

theorem DenseIntMatrix.signedDiagonalRemainder_toRatMatrix {n : Nat}
    (entries : Array Int) (pivot : Fin (n + 1))
    (hpivot : ({ order := n + 1, entries := entries } :
      DenseIntMatrix).entry pivot pivot ≠ 0) :
    let A : DenseIntMatrix := ⟨n + 1, entries⟩
    (A.signedDiagonalRemainder pivot).toRatMatrix =
      let a := A.entry pivot pivot
      ((if 0 < a then a else -a : Int) : ℚ) •
        rationalSchurRemainder A.toRatMatrix pivot := by
  dsimp
  ext i j
  simp only [DenseIntMatrix.signedDiagonalRemainder, Nat.add_sub_cancel,
    DenseIntMatrix.toRatMatrix]
  rw [DenseIntMatrix.entry_ofFn n _ i j i.isLt j.isLt]
  unfold rationalSchurRemainder swapForm
  have hpq : (({ order := n + 1, entries := entries } :
      DenseIntMatrix).entry pivot pivot : ℚ) ≠ 0 := by exact_mod_cast hpivot
  by_cases hi : i.succ = pivot <;> by_cases hj : j.succ = pivot <;>
    by_cases ha : 0 < ({ order := n + 1, entries := entries } :
      DenseIntMatrix).entry pivot pivot <;>
    simp_all [DenseIntMatrix.toRatMatrix, Equiv.swap_apply_def,
      Fin.ext_iff] <;> field_simp <;> ring_nf

theorem DenseIntMatrix.matrixInertia_signedDiagonalRemainder {n : Nat}
    (entries : Array Int) (pivot : Fin (n + 1))
    (hpivot : ({ order := n + 1, entries := entries } :
      DenseIntMatrix).entry pivot pivot ≠ 0) :
    let A : DenseIntMatrix := ⟨n + 1, entries⟩
    matrixInertia (ratCastMatrix
      (A.signedDiagonalRemainder pivot).toRatMatrix) =
      matrixInertia (ratCastMatrix
        (rationalSchurRemainder A.toRatMatrix pivot)) := by
  dsimp
  let A : DenseIntMatrix := ⟨n + 1, entries⟩
  let a := A.entry pivot pivot
  let c : Int := if 0 < a then a else -a
  have hc : 0 < c := by
    have ha0 : a ≠ 0 := by simpa [a, A] using hpivot
    by_cases h : 0 < a
    · simp [c, h]
    · have hn : a < 0 := lt_of_le_of_ne (not_lt.mp h) ha0
      simp [c, h, hn]
  have heq := DenseIntMatrix.signedDiagonalRemainder_toRatMatrix
    entries pivot hpivot
  have hcast : ratCastMatrix
      (A.signedDiagonalRemainder pivot).toRatMatrix =
      (c : ℝ) • ratCastMatrix
        (rationalSchurRemainder A.toRatMatrix pivot) := by
    ext i j
    rw [heq]
    by_cases h : 0 < A.entry pivot pivot <;>
      simp [ratCastMatrix, c, a, A, h, smul_eq_mul]
  rw [hcast]
  exact Inertia.matrixInertia_pos_smul _ (by exact_mod_cast hc)

theorem basisAddForm_isSymm {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℚ) (source target : Fin n)
    (hA : A.IsSymm) : (basisAddForm A source target 1).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  simp only [basisAddForm]
  rw [hA.apply i j, hA.apply source j, hA.apply i source]
  by_cases hi : i = target <;> by_cases hj : j = target <;>
    simp_all [mul_comm]
  ring

theorem DenseIntMatrix.basisAddOne_isSymm {n : Nat}
    (entries : Array Int) (source target : Fin n)
    (hA : ({ order := n, entries := entries } :
      DenseIntMatrix).toRatMatrix.IsSymm) :
    (({ order := n, entries := entries } : DenseIntMatrix).basisAddOne
      source target).toRatMatrix.IsSymm := by
  rw [DenseIntMatrix.basisAddOne_toRatMatrix]
  exact basisAddForm_isSymm _ _ _ hA

theorem DenseIntMatrix.signedDiagonalRemainder_isSymm {n : Nat}
    (entries : Array Int) (pivot : Fin (n + 1))
    (hA : ({ order := n + 1, entries := entries } :
      DenseIntMatrix).toRatMatrix.IsSymm)
    (hpivot : ({ order := n + 1, entries := entries } :
      DenseIntMatrix).entry pivot pivot ≠ 0) :
    (DenseIntMatrix.signedDiagonalRemainder
      ({ order := n + 1, entries := entries } : DenseIntMatrix)
      pivot).toRatMatrix.IsSymm := by
  rw [DenseIntMatrix.signedDiagonalRemainder_toRatMatrix entries pivot hpivot]
  exact (rationalSchurRemainder_isSymm _ _ hA).smul _

@[simp] theorem mem_finIndices_integerInertia {n : Nat} (i : Fin n) :
    i ∈ finIndices n := by
  simp [finIndices]

/-- Main soundness theorem for the high-volume dense integer implementation. -/
theorem matrixInertia_eq_discoverIntegerInertiaV2Aux :
    ∀ (n : Nat) (entries : Array Int),
      (DenseIntMatrix.toRatMatrix
        ({ order := n, entries := entries } : DenseIntMatrix)).IsSymm →
      matrixInertia (ratCastMatrix
        ({ order := n, entries := entries } : DenseIntMatrix).toRatMatrix) =
        discoverIntegerInertiaV2Aux n ⟨n, entries⟩ := by
  intro n
  induction n with
  | zero =>
      intro entries hsymm
      have hzero : ratCastMatrix
          ({ order := 0, entries := entries } : DenseIntMatrix).toRatMatrix =
          Matrix.diagonal (fun _ : Fin 0 ↦ (0 : ℝ)) := by
        ext i
        exact Fin.elim0 i
      rw [hzero, matrixInertia_diagonal]
      simp [discoverIntegerInertiaV2Aux]
  | succ n ih =>
      intro entries hsymm
      let A : DenseIntMatrix := ⟨n + 1, entries⟩
      cases hdiag : A.firstDiagonalPivotFin? with
      | some pivot =>
        have hpivot : A.entry pivot pivot ≠ 0 := by
          have hp : decide (A.entry pivot pivot ≠ 0) = true :=
            @List.find?_some _
              (fun i : Fin A.order ↦ decide (A.entry i i ≠ 0)) pivot _ (by
                simpa [DenseIntMatrix.firstDiagonalPivotFin?] using hdiag)
          exact of_decide_eq_true hp
        have htailSymm := DenseIntMatrix.signedDiagonalRemainder_isSymm
          entries pivot hsymm hpivot
        have ihtail := ih (A.signedDiagonalRemainder pivot).entries htailSymm
        have hstep := matrixInertia_rationalSchurRemainder
          A.toRatMatrix pivot hsymm (by
            simpa [DenseIntMatrix.toRatMatrix] using hpivot)
        have hnormalize := DenseIntMatrix.matrixInertia_signedDiagonalRemainder
          entries pivot hpivot
        dsimp [A] at hnormalize
        rw [← hnormalize] at hstep
        have ihtail' : matrixInertia (ratCastMatrix
            (A.signedDiagonalRemainder pivot).toRatMatrix) =
            discoverIntegerInertiaV2Aux n (A.signedDiagonalRemainder pivot) := by
          simpa [A, DenseIntMatrix.signedDiagonalRemainder] using ihtail
        rw [ihtail'] at hstep
        simpa [discoverIntegerInertiaV2Aux, A, hdiag,
          addRationalPivotInertia, inertiaAddPositive,
          inertiaAddNegative, DenseIntMatrix.toRatMatrix] using hstep
      | none =>
        cases hoff : A.firstOffDiagonalPivotFin? with
        | some pair =>
          rcases pair with ⟨i, j⟩
          have hentry : A.entry i j ≠ 0 := by
            have hp := List.find?_some (show
              ((finIndices A.order).product (finIndices A.order)).find?
                (fun ij ↦ A.entry ij.1 ij.2 ≠ 0) = some (i, j) by
                  simpa [DenseIntMatrix.firstOffDiagonalPivotFin?] using hoff)
            simpa using hp
          have hdiagZero (k : Fin (n + 1)) : A.entry k k = 0 := by
            have hdiagList : (finIndices A.order).find?
                (fun i ↦ A.entry i i ≠ 0) = none := by
              simpa [DenseIntMatrix.firstDiagonalPivotFin?] using hdiag
            have hk := (List.find?_eq_none.mp hdiagList) k
              (by simp)
            simpa using hk
          have hij : i ≠ j := by
            intro h
            subst j
            exact hentry (hdiagZero i)
          let B := A.basisAddOne j i
          have hsymmB := DenseIntMatrix.basisAddOne_isSymm
            entries j i hsymm
          have hsymmEntry : A.entry j i = A.entry i j := by
            have hrat := hsymm.apply i j
            change (A.entry j i : ℚ) = (A.entry i j : ℚ) at hrat
            exact_mod_cast hrat
          have hpivotB : B.entry i i ≠ 0 := by
            have hpivotBRat : B.toRatMatrix i i ≠ 0 := by
              have hii : A.toRatMatrix i i = 0 := by
                simpa [DenseIntMatrix.toRatMatrix] using hdiagZero i
              have hjj : A.toRatMatrix j j = 0 := by
                simpa [DenseIntMatrix.toRatMatrix] using hdiagZero j
              have hji : A.toRatMatrix j i = A.toRatMatrix i j :=
                hsymm.apply i j
              have hijRat : A.toRatMatrix i j ≠ 0 := by
                simpa [DenseIntMatrix.toRatMatrix] using hentry
              rw [DenseIntMatrix.basisAddOne_toRatMatrix]
              simp [basisAddForm]
              intro hz
              exact hijRat (by linarith)
            simpa [DenseIntMatrix.toRatMatrix] using hpivotBRat
          have htailSymm := DenseIntMatrix.signedDiagonalRemainder_isSymm
            B.entries i hsymmB hpivotB
          have ihtail := ih (B.signedDiagonalRemainder i).entries htailSymm
          have hstep := matrixInertia_rationalSchurRemainder
            B.toRatMatrix i hsymmB (by
              simpa [DenseIntMatrix.toRatMatrix] using hpivotB)
          have hnormalize := DenseIntMatrix.matrixInertia_signedDiagonalRemainder
            B.entries i hpivotB
          have hBeta : ({ order := n + 1, entries := B.entries } :
              DenseIntMatrix) = B := by
            calc
              ({ order := n + 1, entries := B.entries } : DenseIntMatrix) =
                  ⟨B.order, B.entries⟩ := by rfl
              _ = B := by cases B; rfl
          dsimp at hnormalize
          have hnormalize' : matrixInertia (ratCastMatrix
              (B.signedDiagonalRemainder i).toRatMatrix) =
              matrixInertia (ratCastMatrix
                (rationalSchurRemainder B.toRatMatrix i)) := by
            simpa only [hBeta] using hnormalize
          rw [← hnormalize'] at hstep
          have ihtail' : matrixInertia (ratCastMatrix
              (B.signedDiagonalRemainder i).toRatMatrix) =
              discoverIntegerInertiaV2Aux n (B.signedDiagonalRemainder i) := by
            simpa [B, A, DenseIntMatrix.signedDiagonalRemainder,
              DenseIntMatrix.basisAddOne] using ihtail
          rw [ihtail'] at hstep
          have hbasis : matrixInertia (ratCastMatrix B.toRatMatrix) =
              matrixInertia (ratCastMatrix A.toRatMatrix) := by
            rw [DenseIntMatrix.basisAddOne_toRatMatrix]
            exact matrixInertia_basisAddForm A.toRatMatrix j i 1 hij.symm
          rw [← hbasis]
          simpa [discoverIntegerInertiaV2Aux, A, B, hdiag, hoff,
            addRationalPivotInertia, inertiaAddPositive,
            inertiaAddNegative, DenseIntMatrix.toRatMatrix] using hstep
        | none =>
          have hentryZero (i j : Fin (n + 1)) : A.entry i j = 0 := by
            have hoffList : ((finIndices A.order).product
                (finIndices A.order)).find?
                (fun ij ↦ A.entry ij.1 ij.2 ≠ 0) = none := by
              simpa [DenseIntMatrix.firstOffDiagonalPivotFin?] using hoff
            have hij := (List.find?_eq_none.mp hoffList) (i, j)
              (by simp)
            simpa using hij
          have hzero : ratCastMatrix A.toRatMatrix =
              Matrix.diagonal (fun _ : Fin (n + 1) ↦ (0 : ℝ)) := by
            ext i j
            simp [ratCastMatrix, DenseIntMatrix.toRatMatrix, hentryZero]
          rw [hzero, matrixInertia_diagonal]
          simp [discoverIntegerInertiaV2Aux, A, hdiag, hoff]

theorem matrixInertia_eq_discoverIntegerInertiaV2 (A : DenseIntMatrix)
    (hA : A.toRatMatrix.IsSymm) :
    matrixInertia (ratCastMatrix A.toRatMatrix) =
      discoverIntegerInertiaV2 A := by
  rcases A with ⟨n, entries⟩
  exact matrixInertia_eq_discoverIntegerInertiaV2Aux n entries hA

end Certificate
end SpectralGraph
