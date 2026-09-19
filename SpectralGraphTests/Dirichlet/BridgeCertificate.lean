import SpectralGraphTests.Dirichlet.Definitions
import SpectralGraph.Certificate.LinearSolveReal
import SpectralGraph.Certificate.IntegerCheck
import SpectralGraph.Inertia.PosSemidefinite

namespace SpectralGraphTests.Dirichlet

open Matrix SpectralGraph SpectralGraph.Certificate

set_option maxHeartbeats 1600000

def A : Matrix (Fin 2) (Fin 2) ℚ := !![3, -1; -1, 4]
def B : Matrix (Fin 2) (Fin 2) ℚ := !![-1, -1; -1, -2]
def D : Matrix (Fin 2) (Fin 2) ℚ := !![2, 0; 0, 3]
def Q : Matrix (Fin 2) (Fin 2) ℚ := !![4/11, 1/11; 1/11, 3/11]
def X : Matrix (Fin 2) (Fin 2) ℚ := !![-5/11, -6/11; -4/11, -7/11]
def S : Matrix (Fin 2) (Fin 2) ℚ := !![13/11, -13/11; -13/11, 13/11]

theorem schur_checked : checkSchur A Q B X B.transpose D S = true := by
  decide +kernel

def pivotInput : DenseIntMatrix := ⟨2, #[3, -1, -1, 4]⟩

theorem pivot_rat_binding : pivotInput.toRatMatrix = A := by
  decide +kernel

theorem pivot_checked : pivotInput.checkInertia ⟨2, 0, 0⟩ = true := by
  decide +kernel

theorem pivot_inertia : matrixInertia (ratCastMatrix A) = ⟨2, 0, 0⟩ := by
  rw [← pivot_rat_binding]
  exact DenseIntMatrix.checkInertia_sound _ _ pivot_checked

theorem pivot_isSymm : (ratCastMatrix A).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [A, ratCastMatrix]

theorem pivot_posDef : (ratCastMatrix A).PosDef := by
  apply matrix_posDef_of_matrixInertia_neg_zero_eq_zero _ pivot_isSymm
  · rw [pivot_inertia]
  · rw [pivot_inertia]

def e : V → ℚ := Pi.single (Sum.inl 1) 1 - Pi.single (Sum.inr 1) 1

theorem bridge_degrees : bridge.degree (Sum.inl 0) = 3 ∧
    bridge.degree (Sum.inl 1) = 3 ∧ bridge.degree (Sum.inr 0) = 2 ∧
    bridge.degree (Sum.inr 1) = 2 := by
  decide +kernel

theorem rational_block_binding : Matrix.fromBlocks A B B.transpose D =
    bridge.lapMatrix ℚ + vecMulVec e e := by
  decide +kernel

theorem real_block_binding : Matrix.fromBlocks (ratCastMatrix A)
    (B.map (Rat.castHom ℝ)) (B.map (Rat.castHom ℝ)).transpose (ratCastMatrix D) =
    weightedBridge := by
  rcases bridge_degrees with ⟨hu, hv, hs, ht⟩
  have huv : bridge.Adj (Sum.inl 0) (Sum.inl 1) := by decide +kernel
  have hus : bridge.Adj (Sum.inl 0) (Sum.inr 0) := by decide +kernel
  have hut : bridge.Adj (Sum.inl 0) (Sum.inr 1) := by decide +kernel
  have hvs : bridge.Adj (Sum.inl 1) (Sum.inr 0) := by decide +kernel
  have hvt : bridge.Adj (Sum.inl 1) (Sum.inr 1) := by decide +kernel
  have hst : ¬ bridge.Adj (Sum.inr 0) (Sum.inr 1) := by decide +kernel
  have hvu := (bridge.adj_comm _ _).mp huv
  have hsu := (bridge.adj_comm _ _).mp hus
  have htu := (bridge.adj_comm _ _).mp hut
  have hsv := (bridge.adj_comm _ _).mp hvs
  have htv := (bridge.adj_comm _ _).mp hvt
  have hts : ¬ bridge.Adj (Sum.inr 1) (Sum.inr 0) := by
    simpa [SimpleGraph.adj_comm] using hst
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [weightedBridge, SpectralGraph.Graph.laplacianUpdate,
      SpectralGraph.Graph.edgeVector_apply, A, B, D, ratCastMatrix,
      SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
      Matrix.vecMulVec_apply, hu, hv, hs, ht,
      huv, hus, hut, hvs, hvt, hst, hvu, hsu, htu, hsv, htv, hts] <;>
    norm_num

theorem rational_update_cast_binding :
    ratCastMatrix (bridge.lapMatrix ℚ + vecMulVec e e) = weightedBridge := by
  rw [← rational_block_binding]
  convert real_block_binding using 1
  ext (i | i) (j | j) <;> rfl

theorem energy_formula (p q a b : ℝ) :
    dotProduct (Sum.elim ![p, q] ![a, b])
      (weightedBridge *ᵥ Sum.elim ![p, q] ![a, b]) =
      (p-q)^2 + (p-a)^2 + (p-b)^2 + (q-a)^2 + 2*(q-b)^2 := by
  rw [← real_block_binding]
  simp [Matrix.fromBlocks, dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
  norm_num [A, B, D, ratCastMatrix]
  ring

theorem constant_kernel : weightedBridge *ᵥ (fun _ : V => (1 : ℝ)) = 0 := by
  rw [← real_block_binding]
  ext (i | i) <;> fin_cases i <;>
    norm_num [Matrix.fromBlocks, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      A, B, D, ratCastMatrix]

theorem weightedBridge_nonzero_constant : (fun _ : V => (1 : ℝ)) ≠ 0 := by
  intro h
  have := congrFun h (Sum.inl 0)
  norm_num at this

end SpectralGraphTests.Dirichlet
