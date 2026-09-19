import SpectralGraph.Inertia.ZeroPrincipal
import SpectralGraphTests.Applications.SignedC4Independence

namespace SpectralGraphTests.ZeroPrincipal

open Matrix SpectralGraph SpectralGraph.Inertia
open SpectralGraphTests.Applications.SignedC4Independence

/-! Focused boundary checks for the zero-principal-block theorem. -/

def noncontiguous : (Fin 2) ↪ Fin 4 where
  toFun i := if i = 0 then 0 else 2
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

example : Fintype.card (Fin 2) ≤
    (matrixInertia (0 : Matrix (Fin 4) (Fin 4) ℝ)).zero +
      min (matrixInertia (0 : Matrix (Fin 4) (Fin 4) ℝ)).pos
        (matrixInertia (0 : Matrix (Fin 4) (Fin 4) ℝ)).neg := by
  apply card_le_matrixInertia_zero_add_min_of_submatrix_eq_zero
    (e := noncontiguous)
  ext i j
  simp

-- The ordinary C4 certificate exposes why the nullity summand is essential.
example : (matrixInertia (C4.adjMatrix ℝ)).zero +
      min (matrixInertia (C4.adjMatrix ℝ)).pos
        (matrixInertia (C4.adjMatrix ℝ)).neg = 3 :=
  ordinary_bound_eq_three

example : min (matrixInertia (C4.adjMatrix ℝ)).pos
      (matrixInertia (C4.adjMatrix ℝ)).neg = 1 := by
  rw [ordinary_adjacency_inertia]
  decide

end SpectralGraphTests.ZeroPrincipal
