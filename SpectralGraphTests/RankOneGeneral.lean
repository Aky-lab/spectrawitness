import SpectralGraph.Inertia.RankOneGeneral
import SpectralGraph.Inertia.BlockDiagonal

/-! Rank-one bounds for off-diagonal edge updates, zero vectors and sign changes. -/
namespace SpectralGraphTests.RankOneGeneral
open SpectralGraph SpectralGraph.Inertia Matrix

-- Adding a weighted graph edge adds an off-diagonal rank-one Laplacian block.
example (A : Matrix (Fin 2) (Fin 2) ℝ) {w : ℝ} (hw : 0 ≤ w) :
    (matrixInertia A).pos ≤ (matrixInertia (A + !![w, -w; -w, w])).pos ∧
    (matrixInertia (A + !![w, -w; -w, w])).neg ≤ (matrixInertia A).neg := by
  have h := rankOne_inertia_mono A ![1, -1] hw
  have hupdate : w • vecMulVec ![1, -1] ![1, -1] = !![w, -w; -w, w] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [vecMulVec]
  simp only [zero_smul, add_zero, hupdate] at h
  exact ⟨h.1, h.2.2.1⟩

-- The general API covers negative coefficients and does not require symmetry.
example (A : Matrix (Fin 5) (Fin 5) ℝ) (u : Fin 5 → ℝ) :
    (matrixInertia (A + (-7 : ℝ) • vecMulVec u u)).zero ≤
      (matrixInertia (A + (2 : ℝ) • vecMulVec u u)).zero + 1 :=
  (rankOne_zero_interlaces A u (-7) 2).1

-- The bound two for signature is sharp, even in dimension one.
example :
    matrixSignature ((-(1 : Matrix (Fin 1) (Fin 1) ℝ)) +
      (2 : ℝ) • vecMulVec (fun _ ↦ 1) (fun _ ↦ 1)) =
        matrixSignature (-(1 : Matrix (Fin 1) (Fin 1) ℝ)) + 2 := by
  have heq : (-(1 : Matrix (Fin 1) (Fin 1) ℝ)) +
      (2 : ℝ) • vecMulVec (fun _ ↦ 1) (fun _ ↦ 1) = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [vecMulVec]
  rw [heq]
  simp [matrixSignature, matrixInertia_neg, matrixInertia_one, Inertia.signature]

-- A zero update vector is valid for every coefficient, including negative ones.
example (A : Matrix (Fin 0) (Fin 0) ℝ) :
    (matrixInertia (A + (-3 : ℝ) • vecMulVec 0 0)).pos ≤
      (matrixInertia A).pos + 1 := by
  simpa only [zero_smul, add_zero] using (rankOne_pos_interlaces A 0 (-3) 0).1

#print axioms SpectralGraph.Inertia.rankOne_inertia_mono
#print axioms SpectralGraph.Inertia.rankOne_zero_interlaces
#print axioms SpectralGraph.Inertia.rankOne_signature_interlaces

end SpectralGraphTests.RankOneGeneral
