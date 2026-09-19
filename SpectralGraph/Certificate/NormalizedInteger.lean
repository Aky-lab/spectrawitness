import SpectralGraph.Certificate.IntegerSound

/-!
# Verified content reduction for integer inertia

Fraction-free Schur elimination introduces common factors. Dividing them out
after every step controls coefficient growth without changing inertia. A gcd
candidate is checked for positivity and exact entrywise divisibility before use;
an invalid candidate safely falls back to one. No property of the gcd producer
is part of the semantic trust boundary.
-/

namespace SpectralGraph.Certificate

/-- Exact entrywise division. Its semantic theorem requires a positive common divisor. -/
def DenseIntMatrix.divideEntries (A : DenseIntMatrix) (d : Int) : DenseIntMatrix :=
  DenseIntMatrix.ofFn A.order fun i j ↦ A.entry i j / d

/-- A proposed divisor is accepted only when positive and exact on all entries. -/
def DenseIntMatrix.checkedDivisor (A : DenseIntMatrix) (d : Int) : Int :=
  if 0 < d ∧ ∀ i j : Fin A.order, d ∣ A.entry i j then d else 1

theorem DenseIntMatrix.checkedDivisor_spec (A : DenseIntMatrix) (d : Int) :
    0 < A.checkedDivisor d ∧ ∀ i j : Fin A.order, A.checkedDivisor d ∣ A.entry i j := by
  unfold DenseIntMatrix.checkedDivisor
  split
  · assumption
  · simp

/-- Candidate content of the stored integer array; zeros are harmless. -/
def DenseIntMatrix.contentCandidate (A : DenseIntMatrix) : Int :=
  (A.entries.foldl (fun g x ↦ Nat.gcd g x.natAbs) 0 : Nat)

/-- Divide by the checked gcd candidate. Zero matrices use divisor one. -/
def DenseIntMatrix.normalizeContent (A : DenseIntMatrix) : DenseIntMatrix :=
  A.divideEntries (A.checkedDivisor A.contentCandidate)

@[simp] theorem DenseIntMatrix.divideEntries_order (A : DenseIntMatrix) (d : Int) :
    (A.divideEntries d).order = A.order := rfl

@[simp] theorem DenseIntMatrix.normalizeContent_order (A : DenseIntMatrix) :
    A.normalizeContent.order = A.order := rfl

/-- Checked integer division is precisely positive rational rescaling. -/
theorem DenseIntMatrix.divideEntries_toRatMatrix (A : DenseIntMatrix) (d : Int)
    (hd : 0 < d) (hdiv : ∀ i j : Fin A.order, d ∣ A.entry i j) :
    (A.divideEntries d).toRatMatrix = (d : ℚ)⁻¹ • A.toRatMatrix := by
  ext i j
  change (((A.divideEntries d).entry i j : Int) : ℚ) = _
  change (((DenseIntMatrix.ofFn A.order (fun i j ↦ A.entry i j / d)).entry i j : Int) : ℚ) = _
  rw [DenseIntMatrix.entry_ofFn A.order _ i j i.isLt j.isLt]
  rw [Int.cast_div (hdiv i j) (by exact_mod_cast ne_of_gt hd)]
  simp [DenseIntMatrix.toRatMatrix, div_eq_mul_inv, mul_comm]

theorem DenseIntMatrix.normalizeContent_toRatMatrix (A : DenseIntMatrix) :
    A.normalizeContent.toRatMatrix =
      (A.checkedDivisor A.contentCandidate : ℚ)⁻¹ • A.toRatMatrix :=
  A.divideEntries_toRatMatrix _ (A.checkedDivisor_spec _).1 (A.checkedDivisor_spec _).2

/-- Content reduction preserves symmetry, including padded storage semantics. -/
theorem DenseIntMatrix.normalizeContent_isSymm (A : DenseIntMatrix)
    (hA : A.toRatMatrix.IsSymm) : A.normalizeContent.toRatMatrix.IsSymm := by
  rw [A.normalizeContent_toRatMatrix]
  exact hA.smul _

/-- Positive exact division preserves the complete real inertia triple. -/
theorem DenseIntMatrix.matrixInertia_normalizeContent (A : DenseIntMatrix) :
    matrixInertia (ratCastMatrix A.normalizeContent.toRatMatrix) =
      matrixInertia (ratCastMatrix A.toRatMatrix) := by
  have heq : ratCastMatrix A.normalizeContent.toRatMatrix =
      (A.checkedDivisor A.contentCandidate : ℝ)⁻¹ • ratCastMatrix A.toRatMatrix := by
    rw [A.normalizeContent_toRatMatrix]
    ext i j
    simp [ratCastMatrix]
  rw [heq]
  apply Inertia.matrixInertia_pos_smul
  exact inv_pos.mpr (by exact_mod_cast (A.checkedDivisor_spec A.contentCandidate).1)

/-- Fraction-free inertia with checked content division after each Schur step.
Fuel at least the matrix order is supplied by the public entry point. -/
def discoverNormalizedIntegerInertiaAux : Nat → DenseIntMatrix → Inertia
  | 0, A => ⟨0, A.order, 0⟩
  | fuel + 1, A =>
      if A.order = 0 then ⟨0, 0, 0⟩
      else
        match A.firstDiagonalPivotFin? with
        | some pivot =>
            let a := A.entry pivot pivot
            let tail := discoverNormalizedIntegerInertiaAux fuel
              (A.signedDiagonalRemainder pivot).normalizeContent
            if 0 < a then inertiaAddPositive tail else inertiaAddNegative tail
        | none =>
            match A.firstOffDiagonalPivotFin? with
            | some (first, second) =>
                let B := A.basisAddOne second first
                let a := B.entry first first
                let tail := discoverNormalizedIntegerInertiaAux fuel
                  (B.signedDiagonalRemainder first).normalizeContent
                if 0 < a then inertiaAddPositive tail else inertiaAddNegative tail
            | none => ⟨0, A.order, 0⟩

/-- Exact inertia discovery with gcd reduction of intermediate coefficients. -/
def discoverNormalizedIntegerInertia (A : DenseIntMatrix) : Inertia :=
  discoverNormalizedIntegerInertiaAux A.order A


set_option maxHeartbeats 800000 in
theorem matrixInertia_eq_discoverNormalizedIntegerInertiaAux :
    ∀ (n : Nat) (entries : Array Int),
      (DenseIntMatrix.toRatMatrix
        ({ order := n, entries := entries } : DenseIntMatrix)).IsSymm →
      matrixInertia (ratCastMatrix
        ({ order := n, entries := entries } : DenseIntMatrix).toRatMatrix) =
        discoverNormalizedIntegerInertiaAux n ⟨n, entries⟩ := by
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
      simp [discoverNormalizedIntegerInertiaAux]
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
        have ihtail := ih (A.signedDiagonalRemainder pivot).normalizeContent.entries ((A.signedDiagonalRemainder pivot).normalizeContent_isSymm htailSymm)
        have hstep := matrixInertia_rationalSchurRemainder
          A.toRatMatrix pivot hsymm (by
            simpa [DenseIntMatrix.toRatMatrix] using hpivot)
        have hnormalize := DenseIntMatrix.matrixInertia_signedDiagonalRemainder
          entries pivot hpivot
        dsimp [A] at hnormalize
        rw [← hnormalize] at hstep
        have ihtail' : matrixInertia (ratCastMatrix
            (A.signedDiagonalRemainder pivot).normalizeContent.toRatMatrix) =
            discoverNormalizedIntegerInertiaAux n (A.signedDiagonalRemainder pivot).normalizeContent := by
          exact ihtail
        rw [← DenseIntMatrix.matrixInertia_normalizeContent (A.signedDiagonalRemainder pivot), ihtail'] at hstep
        simpa [discoverNormalizedIntegerInertiaAux, A, hdiag,
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
          have ihtail := ih (B.signedDiagonalRemainder i).normalizeContent.entries ((B.signedDiagonalRemainder i).normalizeContent_isSymm htailSymm)
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
              (B.signedDiagonalRemainder i).normalizeContent.toRatMatrix) =
              discoverNormalizedIntegerInertiaAux n (B.signedDiagonalRemainder i).normalizeContent := by
            exact ihtail
          rw [← DenseIntMatrix.matrixInertia_normalizeContent (B.signedDiagonalRemainder i), ihtail'] at hstep
          have hbasis : matrixInertia (ratCastMatrix B.toRatMatrix) =
              matrixInertia (ratCastMatrix A.toRatMatrix) := by
            rw [DenseIntMatrix.basisAddOne_toRatMatrix]
            exact matrixInertia_basisAddForm A.toRatMatrix j i 1 hij.symm
          rw [← hbasis]
          simpa [discoverNormalizedIntegerInertiaAux, A, B, hdiag, hoff,
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
          simp [discoverNormalizedIntegerInertiaAux, A, hdiag, hoff]

theorem matrixInertia_eq_discoverNormalizedIntegerInertia (A : DenseIntMatrix)
    (hA : A.toRatMatrix.IsSymm) :
    matrixInertia (ratCastMatrix A.toRatMatrix) =
      discoverNormalizedIntegerInertia A := by
  rcases A with ⟨n, entries⟩
  exact matrixInertia_eq_discoverNormalizedIntegerInertiaAux n entries hA

/-- The optimized implementation agrees with the established integer algorithm. -/
theorem discoverNormalizedIntegerInertia_eq_v2 (A : DenseIntMatrix)
    (hA : A.toRatMatrix.IsSymm) :
    discoverNormalizedIntegerInertia A = discoverIntegerInertiaV2 A :=
  (matrixInertia_eq_discoverNormalizedIntegerInertia A hA).symm.trans
    (matrixInertia_eq_discoverIntegerInertiaV2 A hA)

/-- Strict input boundary using the normalized implementation. -/
def DenseIntMatrix.checkNormalizedInertia (A : DenseIntMatrix) (target : Inertia) : Bool :=
  decide (A.entries.size = A.order * A.order) &&
    decide (∀ i j : Fin A.order, A.entry i j = A.entry j i) &&
    decide (discoverNormalizedIntegerInertia A = target)

/-- Accepted normalized integer certificates have their claimed real inertia. -/
theorem DenseIntMatrix.checkNormalizedInertia_sound (A : DenseIntMatrix) (target : Inertia)
    (h : A.checkNormalizedInertia target = true) :
    matrixInertia (ratCastMatrix A.toRatMatrix) = target := by
  simp only [DenseIntMatrix.checkNormalizedInertia, Bool.and_eq_true, decide_eq_true_eq] at h
  have hs : A.toRatMatrix.IsSymm := by
    ext i j
    change (A.entry j i : ℚ) = (A.entry i j : ℚ)
    rw [h.1.2 j i]
  exact (matrixInertia_eq_discoverNormalizedIntegerInertia A hs).trans h.2

/-- Acceptance forbids implicit zero padding or ignored array tails. -/
theorem DenseIntMatrix.checkNormalizedInertia_size (A : DenseIntMatrix) (target : Inertia)
    (h : A.checkNormalizedInertia target = true) : A.entries.size = A.order * A.order := by
  simp only [DenseIntMatrix.checkNormalizedInertia, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

end SpectralGraph.Certificate
