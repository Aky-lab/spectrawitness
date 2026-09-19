import Mathlib.Data.Matrix.Basis
import SpectralGraph.Inertia.Restriction

namespace SpectralGraph
namespace Inertia

open QuadraticForm Matrix

variable {M : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]

theorem sigPos_le_of_forall_le (Q Q' : QuadraticForm ℝ M)
    (h : ∀ x, Q x ≤ Q' x) : sigPos Q ≤ sigPos Q' := by
  obtain ⟨W, hWdim, hWpos⟩ := exists_finrank_eq_sigPos_and_posDef Q
  calc
    sigPos Q = Module.finrank ℝ W := hWdim.symm
    _ ≤ sigPos Q' := by
      apply le_sigPos_of_posDef Q'
      intro x hx
      exact (hWpos x hx).trans_le (h x.1)

theorem sigNeg_le_of_forall_le (Q Q' : QuadraticForm ℝ M)
    (h : ∀ x, Q x ≤ Q' x) : sigNeg Q' ≤ sigNeg Q := by
  obtain ⟨W, hWdim, hWneg⟩ := exists_finrank_eq_sigNeg_and_negDef Q'
  calc
    sigNeg Q' = Module.finrank ℝ W := hWdim.symm
    _ ≤ sigNeg Q := by
      apply le_sigNeg_of_negDef Q
      intro x hx
      have hneg := hWneg x hx
      change 0 < -Q x.1
      change 0 < -Q' x.1 at hneg
      linarith [h x.1]

theorem signature_le_of_forall_le (Q Q' : QuadraticForm ℝ M)
    (h : ∀ x, Q x ≤ Q' x) :
    (sigPos Q : ℤ) - (sigNeg Q : ℤ) ≤
      (sigPos Q' : ℤ) - (sigNeg Q' : ℤ) := by
  have hp := sigPos_le_of_forall_le Q Q' h
  have hn := sigNeg_le_of_forall_le Q Q' h
  omega

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem matrixSignature_rankOne_update_mono
    (A : Matrix I I ℝ) (x : I) {a b : ℝ} (hab : a ≤ b) :
    matrixSignature (A + Matrix.single x x a) ≤
      matrixSignature (A + Matrix.single x x b) := by
  rw [matrixSignature_eq, matrixSignature_eq]
  apply signature_le_of_forall_le
  intro z
  have hsquare : 0 ≤ z x * z x := mul_self_nonneg (z x)
  have hsingle (c : ℝ) :
      (∑ i, ∑ j, z i * (z j * if x = i ∧ x = j then c else 0)) =
        c * (z x * z x) := by
    classical
    rw [Finset.sum_eq_single x]
    · rw [Finset.sum_eq_single x]
      · simp
        ring
      · intro j hj hjx
        simp [Ne.symm hjx]
      · simp
    · intro i hi hix
      simp [Ne.symm hix]
    · simp
  have hform (c : ℝ) :
      (A + Matrix.single x x c).toQuadraticForm' z =
        A.toQuadraticForm' z + c * (z x * z x) := by
    simp only [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply,
      LinearMap.BilinMap.toQuadraticMap_apply, Matrix.add_apply,
      Matrix.single_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
    rw [hsingle]
  rw [hform a, hform b]
  gcongr

theorem matrixSignature_rankOne_update_interlaces_two
    (A : Matrix I I ℝ) (x : I) (a b : ℝ) :
    matrixSignature (A + Matrix.single x x a) ≤
        matrixSignature (A + Matrix.single x x b) + 2 ∧
      matrixSignature (A + Matrix.single x x b) ≤
        matrixSignature (A + Matrix.single x x a) + 2 := by
  let e : {i : I // i ≠ x} ↪ I := Function.Embedding.subtype _
  let B := A.submatrix e e
  have hsub (c : ℝ) :
      (A + Matrix.single x x c).submatrix e e = B := by
    ext i j
    have hxi : x ≠ i.1 := fun h ↦ i.2 h.symm
    simp [B, e, hxi]
  have hcard : Fintype.card I = Fintype.card {i : I // i ≠ x} + 1 := by
    symm
    change Fintype.card {i : I // i ≠ x} + 1 = Fintype.card I
    rw [Fintype.card_subtype_compl (fun i : I ↦ i = x)]
    have hone : Fintype.card {i : I // i = x} = 1 := by
      apply Fintype.card_eq_one_iff.mpr
      exact ⟨⟨x, rfl⟩, fun i ↦ Subtype.ext i.2⟩
    rw [hone]
    have hpos : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨x⟩
    omega
  have ha := matrixSignature_submatrix_interlaces
    (A + Matrix.single x x a) e hcard
  have hb := matrixSignature_submatrix_interlaces
    (A + Matrix.single x x b) e hcard
  rw [hsub a] at ha
  rw [hsub b] at hb
  omega

end Inertia
end SpectralGraph
