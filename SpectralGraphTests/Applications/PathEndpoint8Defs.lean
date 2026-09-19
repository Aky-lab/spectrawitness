import SpectralGraph.Certificate.SpectralInterval

/-! Canonical edge-sum definition for the eight-vertex endpoint-edge application. -/
namespace SpectralGraphTests.Applications.PathEndpoint8
open Matrix SpectralGraph SpectralGraph.Certificate

def pathEdge8 (i : Fin 7) : Fin 8 → ℚ := fun j ↦
  if j.val = i.val then 1 else if j.val = i.val + 1 then -1 else 0
def pathL8 : Matrix (Fin 8) (Fin 8) ℚ :=
  ∑ i : Fin 7, vecMulVec (pathEdge8 i) (pathEdge8 i)
def endpoint8 : Fin 8 → ℚ := fun i ↦
  if i = 0 then 1 else if i = 7 then -1 else 0

def pathL8Literal : Matrix (Fin 8) (Fin 8) ℚ := !![
  1,-1,0,0,0,0,0,0; -1,2,-1,0,0,0,0,0; 0,-1,2,-1,0,0,0,0;
  0,0,-1,2,-1,0,0,0; 0,0,0,-1,2,-1,0,0; 0,0,0,0,-1,2,-1,0;
  0,0,0,0,0,-1,2,-1; 0,0,0,0,0,0,-1,1]

theorem pathL8_eq_literal : pathL8 = pathL8Literal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pathL8, pathL8Literal, pathEdge8, vecMulVec_apply, Fin.sum_univ_succ]

def A8 : Matrix (Fin 8) (Fin 8) ℚ := pathL8 - (1 / 4 : ℚ) • 1
def A8Literal : Matrix (Fin 8) (Fin 8) ℚ := !![
  3/4,-1,0,0,0,0,0,0; -1,7/4,-1,0,0,0,0,0; 0,-1,7/4,-1,0,0,0,0;
  0,0,-1,7/4,-1,0,0,0; 0,0,0,-1,7/4,-1,0,0; 0,0,0,0,-1,7/4,-1,0;
  0,0,0,0,0,-1,7/4,-1; 0,0,0,0,0,0,-1,3/4]

theorem A8_eq_literal : A8 = A8Literal := by
  have h : pathL8Literal - (1 / 4 : ℚ) • 1 = A8Literal := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pathL8Literal, A8Literal, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply]
  simpa [A8, pathL8_eq_literal] using h

noncomputable def L8 (c : ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  ratCastMatrix pathL8 + c • vecMulVec (fun i ↦ (endpoint8 i : ℝ))
    (fun i ↦ (endpoint8 i : ℝ))

theorem pathL8_isSymm : pathL8.IsSymm := by rw [pathL8_eq_literal]; decide +kernel
theorem A8_symm : A8.IsSymm := by rw [A8_eq_literal]; decide +kernel
theorem A8_real_symm : (ratCastMatrix A8).IsSymm := A8_symm.map _

theorem L8_isSymm (c : ℝ) : (L8 c).IsSymm := by
  have hu : (vecMulVec (fun i ↦ (endpoint8 i : ℝ))
      (fun i ↦ (endpoint8 i : ℝ))).IsSymm := by
    ext i j
    simp [Matrix.transpose_apply, vecMulVec_apply, mul_comm]
  exact (pathL8_isSymm.map _).add (hu.smul c)

theorem L8_isHermitian (c : ℝ) : (L8 c).IsHermitian := L8_isSymm c
theorem shifted_update (c : ℝ) :
    L8 c - (1 / 4 : ℝ) • 1 = ratCastMatrix A8 + c •
      vecMulVec (fun i ↦ (endpoint8 i : ℝ)) (fun i ↦ (endpoint8 i : ℝ)) := by
  rw [A8, ratCast_shift]
  have hq : ((1 / 4 : ℚ) : ℝ) = (1 / 4 : ℝ) := by norm_num
  rw [hq]
  unfold L8
  abel

end SpectralGraphTests.Applications.PathEndpoint8
