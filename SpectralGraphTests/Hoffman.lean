import SpectralGraph.Graph.Hoffman
import SpectralGraphTests.Applications.RookHoffman
import SpectralGraphTests.Hoffman.RookReport
import SpectralGraph.Inertia.BlockDiagonal

namespace SpectralGraphTests.Hoffman

open SpectralGraph SpectralGraph.Graph SpectralGraphTests.Hoffman

/-! Strict negativity excludes the otherwise zero denominator. -/
theorem singleton_zero_cutoff_bad_ratio :
    ¬ ((1 : ℝ) ≤ (Fintype.card (Fin 1) : ℝ) * (-0) / ((0 : ℝ) - 0)) := by
  norm_num

theorem singleton_zero_cutoff_no_neg :
    (matrixInertia ((⊥ : SimpleGraph (Fin 1)).adjMatrix ℝ - (0 : ℝ) • 1)).neg = 0 := by
  have hi : matrixInertia ((⊥ : SimpleGraph (Fin 1)).adjMatrix ℝ - (0 : ℝ) • 1) =
      ⟨0, 1, 0⟩ := by
    simpa using checkAdjacencyInertiaAt_sound (⊥ : SimpleGraph (Fin 1)) 0 ⟨0, 1, 0⟩
      (by decide +kernel)
  rw [hi]

/-! The main cutoff is singular but has no negative inertia directions. -/
theorem rook_singular_nullity_four : (matrixInertia
    (Definitions.rook3.adjMatrix ℝ - (-2 : ℝ) • 1)).zero = 4 := by
  have h : matrixInertia (Definitions.rook3.adjMatrix ℝ - (-2 : ℝ) • 1) = ⟨5, 4, 0⟩ := by
    simpa [RookReport.graph, RookReport.endpoint_1] using RookReport.inertia_1
  rw [h]

theorem rook_singular_neg_zero :
    (matrixInertia (Definitions.rook3.adjMatrix ℝ - (-2 : ℝ) • 1)).neg = 0 := by
  have h : matrixInertia (Definitions.rook3.adjMatrix ℝ - (-2 : ℝ) • 1) = ⟨5, 4, 0⟩ := by
    simpa [RookReport.graph, RookReport.endpoint_1] using RookReport.inertia_1
  rw [h]

/-! A lower cutoff is required: without it the known triple exceeds 9/5. -/
theorem rook_neg_one_inertia :
    matrixInertia (Definitions.rook3.adjMatrix ℝ - (-1 : ℝ) • 1) = ⟨5, 0, 4⟩ := by
  simpa using checkAdjacencyInertiaAt_sound Definitions.rook3 (-1) ⟨5, 0, 4⟩
    (by decide +kernel)

theorem rook_neg_one_not_lower_cutoff :
    (matrixInertia (Definitions.rook3.adjMatrix ℝ - (-1 : ℝ) • 1)).neg = 4 := by
  rw [rook_neg_one_inertia]

theorem rook_neg_one_false_ratio :
    ¬ (((Definitions.diagonal.card : ℝ)) ≤
      (Fintype.card (Fin 9) : ℝ) * (-(-1 : ℝ)) / ((4 : ℝ) - (-1))) := by
  rw [Definitions.diagonal_card]
  norm_num

theorem singleton_indepNum_interface : ((⊥ : SimpleGraph (Fin 1)).indepNum : ℝ) ≤ 1 := by
  have hr : (⊥ : SimpleGraph (Fin 1)).IsRegularOfDegree 0 := by
    unfold SimpleGraph.IsRegularOfDegree
    decide +kernel
  have hi : matrixInertia ((⊥ : SimpleGraph (Fin 1)).adjMatrix ℝ - (-1 : ℝ) • 1) = ⟨1, 0, 0⟩ := by
    simpa using checkAdjacencyInertiaAt_sound (⊥ : SimpleGraph (Fin 1)) (-1) ⟨1, 0, 0⟩
      (by decide +kernel)
  have hn : (matrixInertia ((⊥ : SimpleGraph (Fin 1)).adjMatrix ℝ - (-1 : ℝ) • 1)).neg = 0 := by rw [hi]
  have h := indepNum_le_hoffman_of_inertia (⊥ : SimpleGraph (Fin 1)) 0 hr (-1) (by norm_num) hn
  convert h using 1; norm_num

theorem empty_indepSet_interface : ((∅ : Finset (Fin 0)).card : ℝ) ≤ 0 := by
  have hr : (⊥ : SimpleGraph (Fin 0)).IsRegularOfDegree 0 := by
    unfold SimpleGraph.IsRegularOfDegree
    decide +kernel
  have hi : matrixInertia ((⊥ : SimpleGraph (Fin 0)).adjMatrix ℝ - (-1 : ℝ) • 1) = ⟨0, 0, 0⟩ := by
    simpa using checkAdjacencyInertiaAt_sound (⊥ : SimpleGraph (Fin 0)) (-1) ⟨0, 0, 0⟩
      (by decide +kernel)
  have hn : (matrixInertia ((⊥ : SimpleGraph (Fin 0)).adjMatrix ℝ - (-1 : ℝ) • 1)).neg = 0 := by rw [hi]
  have h := indepSet_card_le_hoffman_of_inertia (⊥ : SimpleGraph (Fin 0)) 0 hr (-1) (by norm_num) hn
    (∅ : Finset (Fin 0)) (by decide +kernel)
  convert h using 1; norm_num

theorem empty_indepNum_interface : ((⊥ : SimpleGraph (Fin 0)).indepNum : ℝ) ≤ 0 := by
  have hr : (⊥ : SimpleGraph (Fin 0)).IsRegularOfDegree 0 := by
    unfold SimpleGraph.IsRegularOfDegree
    decide +kernel
  have hi : matrixInertia ((⊥ : SimpleGraph (Fin 0)).adjMatrix ℝ - (-1 : ℝ) • 1) =
      ⟨0, 0, 0⟩ := by
    simpa using checkAdjacencyInertiaAt_sound (⊥ : SimpleGraph (Fin 0)) (-1) ⟨0, 0, 0⟩
      (by decide +kernel)
  have hn : (matrixInertia ((⊥ : SimpleGraph (Fin 0)).adjMatrix ℝ - (-1 : ℝ) • 1)).neg = 0 := by
    rw [hi]
  have h := indepNum_le_hoffman_of_inertia (⊥ : SimpleGraph (Fin 0)) 0 hr (-1)
    (by norm_num) hn
  convert h using 1; norm_num

theorem singleton_indepSet_interface :
    (({0} : Finset (Fin 1)).card : ℝ) ≤ 1 := by
  have hr : (⊥ : SimpleGraph (Fin 1)).IsRegularOfDegree 0 := by
    unfold SimpleGraph.IsRegularOfDegree
    decide +kernel
  have hi : matrixInertia ((⊥ : SimpleGraph (Fin 1)).adjMatrix ℝ - (-1 : ℝ) • 1) =
      ⟨1, 0, 0⟩ := by
    simpa using checkAdjacencyInertiaAt_sound (⊥ : SimpleGraph (Fin 1)) (-1) ⟨1, 0, 0⟩
      (by decide +kernel)
  have hn : (matrixInertia ((⊥ : SimpleGraph (Fin 1)).adjMatrix ℝ - (-1 : ℝ) • 1)).neg = 0 := by
    rw [hi]
  have h := indepSet_card_le_hoffman_of_inertia (⊥ : SimpleGraph (Fin 1)) 0 hr (-1)
    (by norm_num) hn ({0} : Finset (Fin 1)) (by decide +kernel)
  convert h using 1; norm_num

theorem singleton_indepNum_exact : (⊥ : SimpleGraph (Fin 1)).indepNum = 1 := by
  have hu : (⊥ : SimpleGraph (Fin 1)).indepNum ≤ 1 := by
    exact_mod_cast singleton_indepNum_interface
  have hs : (⊥ : SimpleGraph (Fin 1)).IsIndepSet ({0} : Finset (Fin 1)) := by
    decide +kernel
  have hl := hs.card_le_indepNum
  have hc : ({0} : Finset (Fin 1)).card = 1 := by decide +kernel
  rw [hc] at hl
  omega

theorem singleton_zero_cutoff_fails_on_actual_indepNum :
    ¬ (((⊥ : SimpleGraph (Fin 1)).indepNum : ℝ) ≤
      (Fintype.card (Fin 1) : ℝ) * (-0) / ((0 : ℝ) - 0)) := by
  rw [singleton_indepNum_exact]
  norm_num

theorem bool_indepNum_interface : ((⊥ : SimpleGraph Bool).indepNum : ℝ) ≤ 2 := by
  have hr : (⊥ : SimpleGraph Bool).IsRegularOfDegree 0 := by
    unfold SimpleGraph.IsRegularOfDegree
    decide +kernel
  have heq : (⊥ : SimpleGraph Bool).adjMatrix ℝ - (-1 : ℝ) • 1 =
      (1 : Matrix Bool Bool ℝ) := by
    ext i j
    simp
  have hn : (matrixInertia ((⊥ : SimpleGraph Bool).adjMatrix ℝ - (-1 : ℝ) • 1)).neg = 0 := by
    rw [heq, Inertia.matrixInertia_one]
  have h := indepNum_le_hoffman_of_inertia (⊥ : SimpleGraph Bool) 0 hr (-1)
    (by norm_num) hn
  convert h using 1; norm_num

def star3 : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel (fun i j => i = 0 ∧ j ≠ 0)

instance : DecidableRel star3.Adj := by unfold star3; infer_instance

theorem star_leaves_independent :
    star3.IsIndepSet (↑({1, 2, 3} : Finset (Fin 4)) : Set (Fin 4)) := by
  decide +kernel

theorem star_leaves_card : ({1, 2, 3} : Finset (Fin 4)).card = 3 := by
  decide +kernel

theorem star_not_regular_two : ¬ star3.IsRegularOfDegree 2 := by
  unfold SimpleGraph.IsRegularOfDegree
  decide +kernel

theorem star_shift_inertia :
    matrixInertia (star3.adjMatrix ℝ - (-2 : ℝ) • 1) = ⟨4, 0, 0⟩ := by
  simpa using checkAdjacencyInertiaAt_sound star3 (-2) ⟨4, 0, 0⟩
    (by decide +kernel)

theorem star_shift_posDef :
    (star3.adjMatrix ℝ - (-2 : ℝ) • 1).PosDef := by
  have hs : (star3.adjMatrix ℝ - (-2 : ℝ) • 1).IsSymm :=
    star3.isSymm_adjMatrix.sub (Matrix.isSymm_one.smul _)
  apply matrix_posDef_of_matrixInertia_neg_zero_eq_zero _ hs
  · rw [star_shift_inertia]
  · rw [star_shift_inertia]

theorem star_false_guessed_degree_ratio :
    ¬ ((({1, 2, 3} : Finset (Fin 4)).card : ℝ) ≤
      (Fintype.card (Fin 4) : ℝ) * (-(-2 : ℝ)) / ((2 : ℝ) - (-2))) := by
  rw [star_leaves_card]
  norm_num



end SpectralGraphTests.Hoffman
