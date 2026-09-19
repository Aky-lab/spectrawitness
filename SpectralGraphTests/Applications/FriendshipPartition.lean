import SpectralGraph.Graph.EquitableSpectrum
import SpectralGraph.Graph.Encoding
import SpectralGraph.Certificate.ProductInertia

/-!
# Unequal-cell friendship graph consumer

The five-vertex friendship graph consists of two triangles sharing vertex
`0`.  Its centre/outer partition has sizes `1` and `4`; the outer cell is not
independent.  We use equitability to lift two exact quotient roots and,
independently, an exact rational certificate for a strict ambient bound.
-/

namespace SpectralGraphTests.Applications.FriendshipPartition

open Matrix SpectralGraph SpectralGraph.Graph SpectralGraph.Inertia
open SpectralGraph.Certificate

def friendship : SimpleGraph (Fin 5) :=
  graphOfPackedRows 5 #[30, 4, 0, 16, 0]

instance : DecidableRel friendship.Adj := by
  dsimp only [friendship]
  infer_instance

def cells (v : Fin 5) : Fin 2 := if v = 0 then 0 else 1

theorem cells_surjective : Function.Surjective cells := by
  intro c
  fin_cases c
  · exact ⟨0, by simp [cells]⟩
  · exact ⟨1, by simp [cells]⟩

def adjacencyLiteral : Matrix (Fin 5) (Fin 5) ℚ :=
  !![0, 1, 1, 1, 1;
     1, 0, 1, 0, 0;
     1, 1, 0, 0, 0;
     1, 0, 0, 0, 1;
     1, 0, 0, 1, 0]

theorem friendship_adjMatrix_eq_literal :
    friendship.adjMatrix ℝ = ratCastMatrix adjacencyLiteral := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [friendship, adjacencyLiteral, ratCastMatrix,
      SimpleGraph.adjMatrix_apply, graphOfPackedRows_adj_iff,
      packedUndirectedAdjacencyBit, packedAdjacencyBit, packedAdjacencyRow] <;>
    decide +kernel

def quotient : Matrix (Fin 2) (Fin 2) ℝ := !![0, 4; 1, 1]
def sizeMetric : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 4]
def compressionLiteral : Matrix (Fin 2) (Fin 2) ℝ := !![0, 4; 4, 4]

theorem cell_sizes : cellSize cells = ![1, 4] := by
  funext c
  fin_cases c <;> decide +kernel

theorem cell_metric_eq :
    Matrix.diagonal (fun c ↦ (cellSize cells c : ℝ)) = sizeMetric := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sizeMetric, cell_sizes]

private theorem centre_outer_neighbor_filter :
    Finset.univ.filter (fun w : Fin 5 ↦ friendship.Adj 0 w ∧ cells w = 1) =
      {1, 2, 3, 4} := by
  ext w
  fin_cases w <;>
    norm_num [friendship, cells, graphOfPackedRows_adj_iff,
      packedUndirectedAdjacencyBit, packedAdjacencyBit, packedAdjacencyRow] <;>
    decide +kernel

theorem friendship_equitable : IsEquitable friendship cells quotient := by
  intro v c
  fin_cases v
  · fin_cases c
    · norm_num [IsEquitable, friendship, cells, quotient]
    · change ((Finset.univ.filter
        (fun w : Fin 5 ↦ friendship.Adj 0 w ∧ cells w = 1)).card : ℝ) =
        quotient (cells 0) 1
      rw [centre_outer_neighbor_filter]
      have hcard : ({1, 2, 3, 4} : Finset (Fin 5)).card = 4 := by decide
      rw [hcard]
      norm_num [quotient, cells]
  all_goals fin_cases c <;>
    norm_num [IsEquitable, friendship, cells, quotient,
      graphOfPackedRows_adj_iff, packedUndirectedAdjacencyBit,
      packedAdjacencyBit, packedAdjacencyRow] <;>
    (decide +kernel)

theorem cell_compression_eq :
    cellCompression friendship cells = compressionLiteral := by
  rw [cellCompression, Matrix.mul_assoc,
    friendship_equitable.adjMatrix_mul_cellIndicator friendship cells quotient,
    ← Matrix.mul_assoc, cellIndicator_gram, cell_metric_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sizeMetric, quotient, compressionLiteral, Matrix.mul_apply]

noncomputable def lambdaPlus : ℝ := (1 + Real.sqrt 17) / 2
noncomputable def lambdaMinus : ℝ := (1 - Real.sqrt 17) / 2

theorem lambdaPlus_quadratic : lambdaPlus ^ 2 - lambdaPlus - 4 = 0 := by
  have hs : (Real.sqrt 17) ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  unfold lambdaPlus
  nlinarith

theorem lambdaMinus_quadratic : lambdaMinus ^ 2 - lambdaMinus - 4 = 0 := by
  have hs : (Real.sqrt 17) ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  unfold lambdaMinus
  nlinarith

def rootVector (t : ℝ) : Fin 2 → ℝ := ![t - 1, 1]

theorem rootVector_ne_zero (t : ℝ) : rootVector t ≠ 0 := by
  intro h
  have h1 := congrFun h (1 : Fin 2)
  norm_num [rootVector] at h1

theorem quotient_mul_rootVector (t : ℝ)
    (ht : t ^ 2 - t - 4 = 0) :
    quotient *ᵥ rootVector t = t • rootVector t := by
  funext i
  fin_cases i
  · norm_num [quotient, rootVector, Matrix.mulVec, dotProduct]
    nlinarith
  · norm_num [quotient, rootVector, Matrix.mulVec, dotProduct]

/-- The positive quadratic root occurs in the actual five-by-five adjacency
spectrum, via the equitable graph API. -/
theorem lambdaPlus_occurs :
    ∃ k : Fin 5, (adjMatrix_isHermitian friendship).eigenvalues₀ k = lambdaPlus := by
  exact eigenvalues₀_eq_of_equitable_eigenpair friendship cells cells_surjective
    quotient friendship_equitable lambdaPlus (rootVector lambdaPlus)
    (rootVector_ne_zero lambdaPlus)
    (quotient_mul_rootVector lambdaPlus lambdaPlus_quadratic)

/-- The negative quadratic root also occurs in the actual adjacency spectrum. -/
theorem lambdaMinus_occurs :
    ∃ k : Fin 5, (adjMatrix_isHermitian friendship).eigenvalues₀ k = lambdaMinus := by
  exact eigenvalues₀_eq_of_equitable_eigenpair friendship cells cells_surjective
    quotient friendship_equitable lambdaMinus (rootVector lambdaMinus)
    (rootVector_ne_zero lambdaMinus)
    (quotient_mul_rootVector lambdaMinus lambdaMinus_quadratic)

def rationalPencil : Matrix (Fin 2) (Fin 2) ℚ :=
  !![-5/2, 4; 4, -6]

def rationalPencilCertificate : ProductInertiaCertificate (Fin 2) where
  change := !![1, 8/5; 0, 1]
  inverse := !![1, -8/5; 0, 1]
  image := !![-5/2, 0; 4, 2/5]
  diagonal := ![-5/2, 2/5]
  target := ⟨1, 0, 1⟩

theorem rationalPencil_certificate_check :
    rationalPencilCertificate.check rationalPencil = true := by
  decide +kernel

theorem rationalPencil_inertia :
    matrixInertia (ratCastMatrix rationalPencil) = ⟨1, 0, 1⟩ :=
  rationalPencilCertificate.sound rationalPencil rationalPencil_certificate_check

theorem rationalPencil_eq_cellPencil :
    ratCastMatrix rationalPencil = cellPencil friendship cells (5 / 2) := by
  rw [cellPencil, cell_compression_eq, cell_metric_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rationalPencil, ratCastMatrix, compressionLiteral, sizeMetric]

/-- Independent strict ambient bound from the checked two-by-two cell pencil,
not from the already lifted positive root. -/
theorem five_halves_lt_top_eigenvalue :
    (5 / 2 : ℝ) <
      (adjMatrix_isHermitian friendship).eigenvalues₀ ⟨0, by decide⟩ := by
  apply lt_adjacency_eigenvalue_of_lt_cellPencil_pos
    friendship cells cells_surjective (5 / 2) ⟨0, by decide⟩
  rw [← rationalPencil_eq_cellPencil, rationalPencil_inertia]
  norm_num

#print axioms lambdaPlus_occurs
#print axioms lambdaMinus_occurs
#print axioms five_halves_lt_top_eigenvalue

end SpectralGraphTests.Applications.FriendshipPartition
