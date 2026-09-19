import SpectralGraph.Inertia.RankOneSpectrum

namespace SpectralGraphTests.RankOneSpectrum

open Matrix SpectralGraph.Inertia

private def D : Matrix (Fin 2) (Fin 2) ℝ := !![(0 : ℝ), 0; 0, 0]
private theorem hD : D.IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [D]

private def offDiagonalVector : Fin 2 → ℝ := ![1, 1]

/-- The zero vector is a genuine equality case, ruling out strict monotonicity. -/
example (a b : ℝ) (k : Fin 2) :
    (rankOneUpdate_isHermitian D hD 0 a).eigenvalues₀ k =
      (rankOneUpdate_isHermitian D hD 0 b).eigenvalues₀ k := by
  congr 1 <;> simp [rankOneUpdate_isHermitian]

example (k : Fin 2) :
    (rankOneUpdate_isHermitian D hD offDiagonalVector (-1)).eigenvalues₀ k ≤
      (rankOneUpdate_isHermitian D hD offDiagonalVector 2).eigenvalues₀ k := by
  exact eigenvalues₀_rankOne_mono D hD offDiagonalVector (by norm_num) k

-- The same singular, off-diagonal update exercises the adjacent-index bound
-- while its coefficient crosses zero.
example :
    (rankOneUpdate_isHermitian D hD offDiagonalVector 2).eigenvalues₀ ⟨1, by decide⟩ ≤
      (rankOneUpdate_isHermitian D hD offDiagonalVector (-1)).eigenvalues₀
        ⟨0, by decide⟩ := by
  exact eigenvalues₀_rankOne_succ_le D hD offDiagonalVector (by norm_num)
    ⟨0, by decide⟩ (by decide)

-- Equal coefficients give the same spectrum without a strictness assumption.
example (c : ℝ) (k : Fin 2) :
    (rankOneUpdate_isHermitian D hD offDiagonalVector c).eigenvalues₀ k =
      (rankOneUpdate_isHermitian D hD offDiagonalVector c).eigenvalues₀ k := rfl

-- A nonzero rank-one update leaves an orthogonal direction exactly fixed.
example (c : ℝ) :
    let u : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0
    let z : Fin 2 → ℝ := fun i => if i = 1 then 1 else 0
    Matrix.mulVec (c • vecMulVec u u) z = 0 := by
  dsimp
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, Matrix.vecMulVec_apply, Fin.sum_univ_two]

#print axioms SpectralGraph.Inertia.eigenvalues₀_rankOne_mono
#print axioms SpectralGraph.Inertia.eigenvalues₀_rankOne_succ_le

end SpectralGraphTests.RankOneSpectrum
