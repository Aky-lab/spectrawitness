import SpectralGraph.Certificate.FastInertia
import SpectralGraph.Inertia.NegativeSpectrum

namespace SpectralGraphTests.Applications.PathEndpointSupporting
open Matrix SpectralGraph SpectralGraph.Certificate SpectralGraph.Inertia

def pathEdge6 (i : Fin 5) : Fin 6 → ℚ := fun j ↦
  if j = i.castSucc then 1 else if j = i.succ then -1 else 0
def pathL6 : Matrix (Fin 6) (Fin 6) ℚ := ∑ i : Fin 5, vecMulVec (pathEdge6 i) (pathEdge6 i)
def endpoint6 : Fin 6 → ℚ := fun i ↦ if i = 0 then 1 else if i = 5 then -1 else 0
def B6 (c : ℚ) : Matrix (Fin 6) (Fin 6) ℚ :=
  pathL6 - ((4 / 9 : ℚ) • 1) + c • vecMulVec endpoint6 endpoint6
noncomputable def L6 (c : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  ratCastMatrix pathL6 + c • vecMulVec (fun i ↦ (endpoint6 i : ℝ)) (fun i ↦ (endpoint6 i : ℝ))
theorem pathL6_isSymm : pathL6.IsSymm := by
  unfold Matrix.IsSymm
  ext i j
  change (∑ k : Fin 5, pathEdge6 k j * pathEdge6 k i) =
    ∑ k : Fin 5, pathEdge6 k i * pathEdge6 k j
  apply Finset.sum_congr rfl
  intro k _
  ring
theorem L6_isSymm (c : ℝ) : (L6 c).IsSymm := by
  have hu : (vecMulVec (fun i ↦ (endpoint6 i : ℝ))
      (fun i ↦ (endpoint6 i : ℝ))).IsSymm := by
    ext i j
    simp [Matrix.transpose_apply, vecMulVec_apply, mul_comm]
  exact (pathL6_isSymm.map _).add (hu.smul c)
theorem L6_isHermitian (c : ℝ) : (L6 c).IsHermitian := L6_isSymm c
theorem L6_shifted (c : ℚ) : L6 (c : ℝ) - (4 / 9 : ℝ) • 1 = ratCastMatrix (B6 c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [L6, B6, pathL6, pathEdge6, endpoint6,
    ratCastMatrix, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, vecMulVec_apply] <;> push_cast <;> ring
def c6 : ℚ := 329 / 2169

theorem B6_inertia_zero : matrixInertia (ratCastMatrix (B6 0)) = ⟨4,0,2⟩ := by
  rw [matrixInertia_eq_fastComputedInertia _ (by decide +kernel)]; decide +kernel
theorem B6_inertia_half : matrixInertia (ratCastMatrix (B6 (c6/2))) = ⟨4,0,2⟩ := by
  rw [matrixInertia_eq_fastComputedInertia _ (by decide +kernel)]; decide +kernel
theorem B6_inertia_transition : matrixInertia (ratCastMatrix (B6 c6)) = ⟨4,1,1⟩ := by
  rw [matrixInertia_eq_fastComputedInertia _ (by decide +kernel)]; decide +kernel
theorem B6_reject_incorrect_transition :
    matrixInertia (ratCastMatrix (B6 c6)) ≠ ⟨4,0,2⟩ := by
  rw [B6_inertia_transition]
  decide
theorem B6_inertia_double : matrixInertia (ratCastMatrix (B6 (2*c6))) = ⟨5,0,1⟩ := by
  rw [matrixInertia_eq_fastComputedInertia _ (by decide +kernel)]; decide +kernel

theorem L6_second_smallest_zero_lt :
    (L6_isHermitian 0).eigenvalues₀ ⟨4, by decide⟩ < (4/9 : ℝ) := by
  rw [eigenvalues₀_lt_iff]
  have hs := L6_shifted 0
  norm_num at hs
  rw [hs]
  simp [B6_inertia_zero]
theorem L6_second_smallest_half_lt :
    (L6_isHermitian ((c6/2 : ℚ) : ℝ)).eigenvalues₀ ⟨4, by decide⟩ < (4/9 : ℝ) := by
  rw [eigenvalues₀_lt_iff, L6_shifted (c6/2)]; simp [B6_inertia_half]
theorem L6_second_smallest_transition_eq :
    (L6_isHermitian (c6 : ℝ)).eigenvalues₀ ⟨4, by decide⟩ = (4/9 : ℝ) := by
  apply le_antisymm
  · rw [eigenvalues₀_le_iff, L6_shifted c6]; simp [B6_inertia_transition]
  · rw [le_eigenvalues₀_iff, L6_shifted c6]; simp [B6_inertia_transition]
theorem L6_threshold_lt_second_smallest_double :
    (4/9 : ℝ) < (L6_isHermitian ((2*c6 : ℚ) : ℝ)).eigenvalues₀ ⟨4, by decide⟩ := by
  rw [lt_eigenvalues₀_iff, L6_shifted (2*c6)]; simp [B6_inertia_double]

end SpectralGraphTests.Applications.PathEndpointSupporting
