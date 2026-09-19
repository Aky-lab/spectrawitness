import SpectralGraph.Certificate.SpectralInterval

namespace SpectralGraphTests.Applications.PathEndpointSupporting
open Matrix SpectralGraph SpectralGraph.Certificate

def pathEdge12 (i : Fin 11) : Fin 12 → ℚ := fun j ↦
  if j = i.castSucc then 1 else if j = i.succ then -1 else 0
def pathL12 : Matrix (Fin 12) (Fin 12) ℚ := ∑ i : Fin 11, vecMulVec (pathEdge12 i) (pathEdge12 i)
def endpoint12 : Fin 12 → ℚ := fun i ↦ if i = 0 then 1 else if i = 11 then -1 else 0
def B12 (c : ℚ) : Matrix (Fin 12) (Fin 12) ℚ :=
  pathL12 - ((1 / 9 : ℚ) • 1) + c • vecMulVec endpoint12 endpoint12
noncomputable def L12 (c : ℝ) : Matrix (Fin 12) (Fin 12) ℝ :=
  ratCastMatrix pathL12 + c • vecMulVec (fun i ↦ (endpoint12 i : ℝ)) (fun i ↦ (endpoint12 i : ℝ))
theorem pathL12_isSymm : pathL12.IsSymm := by
  unfold Matrix.IsSymm
  ext i j
  change (∑ k : Fin 11, pathEdge12 k j * pathEdge12 k i) =
    ∑ k : Fin 11, pathEdge12 k i * pathEdge12 k j
  apply Finset.sum_congr rfl
  intro k _
  ring
theorem L12_isSymm (c : ℝ) : (L12 c).IsSymm := by
  have hu : (vecMulVec (fun i ↦ (endpoint12 i : ℝ))
      (fun i ↦ (endpoint12 i : ℝ))).IsSymm := by
    ext i j
    simp [Matrix.transpose_apply, vecMulVec_apply, mul_comm]
  exact (pathL12_isSymm.map _).add (hu.smul c)
theorem L12_isHermitian (c : ℝ) : (L12 c).IsHermitian := L12_isSymm c
theorem L12_shifted (c : ℚ) : L12 (c : ℝ) - (1/9 : ℝ) • 1 = ratCastMatrix (B12 c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [L12, B12, pathL12, pathEdge12, endpoint12,
    ratCastMatrix, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, vecMulVec_apply] <;> push_cast <;> ring
def c12 : ℚ := 225679 / 3072159

end SpectralGraphTests.Applications.PathEndpointSupporting
