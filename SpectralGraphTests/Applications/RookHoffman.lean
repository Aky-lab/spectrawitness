import SpectralGraph.Graph.Hoffman
import SpectralGraph.Graph.Independence
import SpectralGraphTests.Hoffman.RookReport

/-! A sharp certificate-backed Hoffman result for the 3×3 rook graph. -/

namespace SpectralGraphTests.Applications.RookHoffman

open SpectralGraph SpectralGraph.Graph
open SpectralGraphTests.Hoffman

private theorem shifted_inertia_at_neg_two :
    matrixInertia (Definitions.rook3.adjMatrix ℝ - (-2 : ℝ) • 1) = ⟨5, 4, 0⟩ := by
  simpa [RookReport.graph, RookReport.endpoint_1] using RookReport.inertia_1

private theorem shifted_inertia_at_neg_four :
    matrixInertia (Definitions.rook3.adjMatrix ℝ - (-4 : ℝ) • 1) = ⟨9, 0, 0⟩ := by
  simpa [RookReport.graph, RookReport.endpoint_0] using RookReport.inertia_0

theorem indepSet_card_le_three (s : Finset (Fin 9))
    (hs : Definitions.rook3.IsIndepSet (↑s : Set (Fin 9))) : s.card ≤ 3 := by
  have hneg : (matrixInertia
      (Definitions.rook3.adjMatrix ℝ - (-2 : ℝ) • 1)).neg = 0 := by
    rw [shifted_inertia_at_neg_two]
  have h := indepSet_card_le_hoffman_of_inertia
    Definitions.rook3 4 Definitions.rook3_regular (-2) (by norm_num) hneg s hs
  have hreal : (s.card : ℝ) ≤ 3 := by
    convert h using 1; norm_num
  exact_mod_cast hreal

theorem indepNum_eq_three : Definitions.rook3.indepNum = 3 := by
  have hneg : (matrixInertia
      (Definitions.rook3.adjMatrix ℝ - (-2 : ℝ) • 1)).neg = 0 := by
    rw [shifted_inertia_at_neg_two]
  have hu := indepNum_le_hoffman_of_inertia
    Definitions.rook3 4 Definitions.rook3_regular (-2) (by norm_num) hneg
  have hu' : Definitions.rook3.indepNum ≤ 3 := by
    have hreal : (Definitions.rook3.indepNum : ℝ) ≤ 3 := by
      convert hu using 1; norm_num
    exact_mod_cast hreal
  have hl := Definitions.diagonal_independent.card_le_indepNum
  rw [Definitions.diagonal_card] at hl
  exact Nat.le_antisymm hu' hl

theorem ordinary_adjacency_inertia :
    matrixInertia (Definitions.rook3.adjMatrix ℝ) = ⟨5, 0, 4⟩ := by
  simpa [RookReport.graph, RookReport.endpoint_2] using RookReport.inertia_2

theorem ordinary_inertia_bound_eq_four :
    (matrixInertia (Definitions.rook3.adjMatrix ℝ)).zero +
      min (matrixInertia (Definitions.rook3.adjMatrix ℝ)).pos
          (matrixInertia (Definitions.rook3.adjMatrix ℝ)).neg = 4 := by
  simp [ordinary_adjacency_inertia]

theorem looser_ratio_eq_nine_halves :
    (Fintype.card (Fin 9) : ℝ) * (-(-4 : ℝ)) / ((4 : ℝ) - (-4)) = 9 / 2 := by
  norm_num

theorem looser_shift_posDef :
    (Definitions.rook3.adjMatrix ℝ - (-4 : ℝ) • 1).PosDef := by
  have hs : (Definitions.rook3.adjMatrix ℝ - (-4 : ℝ) • 1).IsSymm :=
    Definitions.rook3.isSymm_adjMatrix.sub (Matrix.isSymm_one.smul _)
  apply matrix_posDef_of_matrixInertia_neg_zero_eq_zero _ hs
  · rw [shifted_inertia_at_neg_four]
  · rw [shifted_inertia_at_neg_four]

theorem indepNum_le_four_at_neg_four : Definitions.rook3.indepNum ≤ 4 := by
  have hneg : (matrixInertia
      (Definitions.rook3.adjMatrix ℝ - (-4 : ℝ) • 1)).neg = 0 := by
    rw [shifted_inertia_at_neg_four]
  have hu := indepNum_le_hoffman_of_inertia
    Definitions.rook3 4 Definitions.rook3_regular (-4) (by norm_num) hneg
  have hreal : (Definitions.rook3.indepNum : ℝ) ≤ 9 / 2 := by
    convert hu using 1; norm_num
  have hlt : (Definitions.rook3.indepNum : ℝ) < 5 := by linarith
  have hnat : Definitions.rook3.indepNum < 5 := by exact_mod_cast hlt
  omega

end SpectralGraphTests.Applications.RookHoffman
