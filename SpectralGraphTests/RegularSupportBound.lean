import SpectralGraph.Inertia.RegularSupportBound
import SpectralGraph.Inertia.BlockDiagonal
import SpectralGraph.Inertia.Diagonal

/-! Matrix-only boundaries for the division-free constant-row-sum bound. -/

namespace SpectralGraphTests.RegularSupportBound

open Matrix SpectralGraph SpectralGraph.Inertia

theorem empty_ambient_core :
    (0 - (-1 : ℝ)) * ((∅ : Finset (Fin 0)).card : ℝ) ≤
      (-(-1 : ℝ)) * (Fintype.card (Fin 0) : ℝ) := by
  let A : Matrix (Fin 0) (Fin 0) ℝ := 0
  have hs : A.IsSymm := by simp [A]
  have hr : A *ᵥ (fun _ => (1 : ℝ)) = (0 : ℝ) • (fun _ => (1 : ℝ)) := by
    funext i
    exact i.elim0
  have hp : (A - (-1 : ℝ) • 1).PosSemidef := by
    have hi : (1 : Matrix (Fin 0) (Fin 0) ℝ).PosSemidef := by
      apply matrix_posSemidef_of_matrixInertia_neg_eq_zero _ Matrix.isSymm_one
      rw [Inertia.matrixInertia_one]
    simpa [A] using hi
  have hz : ∀ i ∈ (∅ : Finset (Fin 0)), ∀ j ∈ (∅ : Finset (Fin 0)), A i j = 0 := by
    simp
  exact card_mul_sub_le_of_zero_principal_of_posSemidef A hs 0 (-1)
    hr (by norm_num) hp ∅ hz

theorem noncontiguous_zero_block_core :
    (0 - (-1 : ℝ)) * (({0, 2} : Finset (Fin 3)).card : ℝ) ≤
      (-(-1 : ℝ)) * (Fintype.card (Fin 3) : ℝ) := by
  let A : Matrix (Fin 3) (Fin 3) ℝ := 0
  have hs : A.IsSymm := by simp [A]
  have hr : A *ᵥ (fun _ => (1 : ℝ)) = (0 : ℝ) • (fun _ => (1 : ℝ)) := by
    simp [A]
  have hp : (A - (-1 : ℝ) • 1).PosSemidef := by
    have hi : (1 : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
      apply matrix_posSemidef_of_matrixInertia_neg_eq_zero _ Matrix.isSymm_one
      rw [Inertia.matrixInertia_one]
    simpa [A] using hi
  have hz : ∀ i ∈ ({0, 2} : Finset (Fin 3)),
      ∀ j ∈ ({0, 2} : Finset (Fin 3)), A i j = 0 := by
    simp [A]
  exact card_mul_sub_le_of_zero_principal_of_posSemidef A hs 0 (-1)
    hr (by norm_num) hp {0, 2} hz

theorem identity_shift_psd :
    ((1 : Matrix (Fin 1) (Fin 1) ℝ) - (-1 : ℝ) • 1).PosSemidef := by
  have hs : ((1 : Matrix (Fin 1) (Fin 1) ℝ) - (-1 : ℝ) • 1).IsSymm :=
    Matrix.isSymm_one.sub (Matrix.isSymm_one.smul _)
  have heq : ((1 : Matrix (Fin 1) (Fin 1) ℝ) - (-1 : ℝ) • 1) =
      Matrix.diagonal (fun _ : Fin 1 => (2 : ℝ)) := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [Matrix.diagonal_apply, Matrix.one_apply]
  have hn : (matrixInertia
      ((1 : Matrix (Fin 1) (Fin 1) ℝ) - (-1 : ℝ) • 1)).neg = 0 := by
    rw [heq, matrixInertia_diagonal]
    norm_num
  exact matrix_posSemidef_of_matrixInertia_neg_eq_zero _ hs hn

theorem identity_row_sum :
    (1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (fun _ => (1 : ℝ)) =
      (1 : ℝ) • (fun _ : Fin 1 => (1 : ℝ)) := by
  simp

theorem identity_bad_zero_premise :
    ¬ (∀ i ∈ ({0} : Finset (Fin 1)), ∀ j ∈ ({0} : Finset (Fin 1)),
      (1 : Matrix (Fin 1) (Fin 1) ℝ) i j = 0) := by
  intro h
  norm_num at h

theorem identity_false_omitting_diagonal :
    ¬ ((1 : ℝ) - (-1)) * (({0} : Finset (Fin 1)).card : ℝ) ≤
      (-(-1 : ℝ)) * (Fintype.card (Fin 1) : ℝ) := by
  norm_num

end SpectralGraphTests.RegularSupportBound
