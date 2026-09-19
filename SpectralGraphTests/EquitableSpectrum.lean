import SpectralGraph.Graph.EquitableSpectrum

namespace SpectralGraphTests.EquitableSpectrum

open Matrix SpectralGraph.Graph

def K3 : SimpleGraph (Fin 3) := SimpleGraph.completeGraph (Fin 3)

instance : DecidableRel K3.Adj := by
  dsimp only [K3]
  infer_instance

def centreAndOuter (v : Fin 3) : Fin 2 := if v = 0 then 0 else 1

theorem centreAndOuter_surjective : Function.Surjective centreAndOuter := by
  intro c
  fin_cases c
  · exact ⟨0, by simp [centreAndOuter]⟩
  · exact ⟨1, by simp [centreAndOuter]⟩

/-- The ordinary equitable neighbour-count matrix for unequal cells is not
symmetric: the centre sees two outer vertices, while each outer vertex sees
one centre. -/
def K3Count : Matrix (Fin 2) (Fin 2) ℝ := !![0, 2; 1, 1]

private def K3CountNat : Matrix (Fin 2) (Fin 2) ℕ := !![0, 2; 1, 1]

private theorem K3_counts_nat (v : Fin 3) (c : Fin 2) :
    (Finset.univ.filter fun w ↦ K3.Adj v w ∧ centreAndOuter w = c).card =
      K3CountNat (centreAndOuter v) c := by
  decide +kernel +revert

theorem K3Count_not_symmetric : ¬ K3Count.IsSymm := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ ↦ M 0 1) h
  norm_num [Matrix.IsSymm, Matrix.transpose_apply, K3Count] at h01

theorem K3_equitable : IsEquitable K3 centreAndOuter K3Count := by
  intro v c
  rw [K3_counts_nat]
  fin_cases v <;> fin_cases c <;>
    norm_num [K3CountNat, K3Count, centreAndOuter]

def K3PerronVector : Fin 2 → ℝ := ![1, 1]

theorem K3PerronVector_ne_zero : K3PerronVector ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [K3PerronVector] at h0

theorem K3PerronVector_eigenpair :
    K3Count *ᵥ K3PerronVector = (2 : ℝ) • K3PerronVector := by
  funext i
  fin_cases i <;> norm_num [K3Count, K3PerronVector, Matrix.mulVec, dotProduct]

/-- The graph-facing lifting API accepts the concrete nonsymmetric count
matrix and returns an occurrence in the actual adjacency spectrum. -/
theorem K3_two_occurs :
    ∃ k : Fin (Fintype.card (Fin 3)),
      (adjMatrix_isHermitian K3).eigenvalues₀ k = 2 := by
  exact eigenvalues₀_eq_of_equitable_eigenpair K3 centreAndOuter
    centreAndOuter_surjective K3Count K3_equitable 2 K3PerronVector
    K3PerronVector_ne_zero K3PerronVector_eigenpair

def wrongK3Count : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 1]

/-- A wrong concrete neighbour count fails the equitable hypothesis. -/
theorem K3_not_equitable_for_wrong_count :
    ¬ IsEquitable K3 centreAndOuter wrongK3Count := by
  intro h
  have h01 := h 0 1
  rw [K3_counts_nat] at h01
  norm_num [K3CountNat, centreAndOuter, wrongK3Count] at h01

def phantomCell (_ : Fin 1) : Fin 2 := 0

def phantomVector : Fin 2 → ℝ := ![0, 1]

theorem phantomVector_ne_zero : phantomVector ≠ 0 := by
  intro h
  have h1 := congrFun h 1
  norm_num [phantomVector] at h1

/-- The unused second cell is invisible to indicator lifting. -/
theorem phantomVector_lifts_to_zero :
    cellIndicator phantomCell *ᵥ phantomVector = 0 := by
  funext v
  fin_cases v
  norm_num [cellIndicator_mulVec, phantomCell, phantomVector]

/-- Without surjectivity, an unused cell makes the indicator lift
noninjective. -/
theorem phantom_cell_indicator_not_injective :
    ¬ Function.Injective (cellIndicator phantomCell).mulVecLin := by
  intro hinjective
  apply phantomVector_ne_zero
  apply hinjective
  simpa only [Matrix.mulVecLin_apply, LinearMap.map_zero] using
    phantomVector_lifts_to_zero

#print axioms K3_two_occurs
#print axioms K3_not_equitable_for_wrong_count
#print axioms phantom_cell_indicator_not_injective

end SpectralGraphTests.EquitableSpectrum
