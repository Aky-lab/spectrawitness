import SpectralGraph.Graph.PartitionSpectrum
import SpectralGraph.Graph.Encoding
import SpectralGraph.Certificate.ProductInertia

namespace SpectralGraphTests.PartitionSpectrum

open Matrix SpectralGraph SpectralGraph.Graph SpectralGraph.Inertia
open SpectralGraph.Certificate

/-- The public count theorem has no nonempty or equitability hypotheses. -/
example {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → C) (hp : Function.Surjective p) (t : ℝ) :=
  partition_pos_bounds G p hp t

def K2 : SimpleGraph (Fin 2) := SimpleGraph.completeGraph (Fin 2)
instance : DecidableRel K2.Adj := by
  dsimp only [K2]
  infer_instance

def singletonCells : Fin 2 → Fin 2 := id

theorem singletonCells_surjective : Function.Surjective singletonCells :=
  Function.surjective_id

def K2PencilZero : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 1, 0]

def K2PencilZeroCertificate : ProductInertiaCertificate (Fin 2) where
  change := !![1, 1; 1, -1]
  inverse := !![1/2, 1/2; 1/2, -1/2]
  image := !![1, -1; 1, 1]
  diagonal := ![2, -2]
  target := ⟨1, 0, 1⟩

theorem K2_cellPencil_zero_eq_cast :
    cellPencil K2 singletonCells 0 = ratCastMatrix K2PencilZero := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cellPencil, cellCompression, cellIndicator, cellSize,
      K2, singletonCells, ratCastMatrix, SimpleGraph.adjMatrix_apply,
      Matrix.mul_apply, K2PencilZero]

theorem K2_cellPencil_zero_inertia :
    matrixInertia (cellPencil K2 singletonCells 0) = ⟨1, 0, 1⟩ := by
  rw [K2_cellPencil_zero_eq_cast]
  exact K2PencilZeroCertificate.sound K2PencilZero (by decide +kernel)

/-- A first end-to-end graph consequence through the cell-compression API. -/
theorem K2_top_eigenvalue_pos :
    0 < (adjMatrix_isHermitian K2).eigenvalues₀ ⟨0, by decide⟩ := by
  apply lt_adjacency_eigenvalue_of_lt_cellPencil_pos
    K2 singletonCells singletonCells_surjective 0 ⟨0, by decide⟩
  rw [K2_cellPencil_zero_inertia]
  norm_num

/-- The empty graph/cell instance has exactly zero positive counts on both
sides; no `Fin 0` value is manufactured. -/
theorem empty_partition_positive_counts (t : ℝ) :
    (matrixInertia
      (cellPencil (⊥ : SimpleGraph (Fin 0))
        (fun v : Fin 0 ↦ (Fin.elim0 v : Fin 0)) t)).pos = 0 ∧
    (matrixInertia
      ((⊥ : SimpleGraph (Fin 0)).adjMatrix ℝ - t • 1)).pos = 0 := by
  have hcell := matrixInertia_order
    (cellPencil (⊥ : SimpleGraph (Fin 0))
      (fun v : Fin 0 ↦ (Fin.elim0 v : Fin 0)) t)
  have hamb := matrixInertia_order
    ((⊥ : SimpleGraph (Fin 0)).adjMatrix ℝ - t • 1)
  simp only [Inertia.order, Fintype.card_fin] at hcell hamb
  omega

def unequalCells (v : Fin 3) : Fin 2 := if v = 0 then 0 else 1

theorem unequalCells_surjective : Function.Surjective unequalCells := by
  intro c
  fin_cases c
  · exact ⟨0, by simp [unequalCells]⟩
  · exact ⟨1, by simp [unequalCells]⟩

def nonEquitableGraph : SimpleGraph (Fin 3) :=
  graphOfPackedRows 3 #[2, 0, 0]

instance : DecidableRel nonEquitableGraph.Adj := by
  dsimp only [nonEquitableGraph]
  infer_instance

/-- Vertices `1` and `2` lie in the same cell but have different neighbour
 counts into cell `0`; no equitable hypothesis is required. -/
theorem nonEquitableGraph_cell_counts_differ :
    (Finset.univ.filter fun w : Fin 3 ↦
      nonEquitableGraph.Adj 1 w ∧ unequalCells w = 0).card ≠
    (Finset.univ.filter fun w : Fin 3 ↦
      nonEquitableGraph.Adj 2 w ∧ unequalCells w = 0).card := by
  decide

example (t : ℝ) :=
  partition_pos_bounds nonEquitableGraph unequalCells unequalCells_surjective t

/-- Unequal cells force the shift metric `D = diag(1,2)`; replacing it by
the identity changes the pencil. -/
theorem unequal_cell_shift_is_not_identity :
    cellPencil nonEquitableGraph unequalCells 1 ≠
      cellCompression nonEquitableGraph unequalCells -
        (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro h
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ ↦ M 1 1) h
  norm_num [cellPencil, cellSize, unequalCells] at h11
  have hcard : (Finset.univ.filter fun x : Fin 3 ↦ x ≠ 0).card = 2 := by decide
  rw [hcard] at h11
  norm_num at h11

#print axioms K2_top_eigenvalue_pos
#print axioms empty_partition_positive_counts
#print axioms unequal_cell_shift_is_not_identity

end SpectralGraphTests.PartitionSpectrum
