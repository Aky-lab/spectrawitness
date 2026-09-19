import SpectralGraph.Graph.InducedSpectrum
import SpectralGraph.Inertia.Compression
import SpectralGraph.Inertia.OrderedSpectrum

/-!
# Graph spectra from vertex cells

This module compresses the adjacency matrix along indicator columns for a
surjective map from vertices to cells.  Cells may contain edges: this is not a
proper-colouring partition.  For unequal cells the shifted compressed pencil
is `B - tD`, where `D` is the diagonal matrix of cell sizes.
-/

namespace SpectralGraph.Graph

open Matrix SpectralGraph.Inertia

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

/-- The vertex-by-cell indicator matrix of a cell map. -/
def cellIndicator (p : V → C) : Matrix V C ℝ :=
  fun v c ↦ if p v = c then 1 else 0

/-- Cardinality of one fibre of a cell map. -/
def cellSize (p : V → C) (c : C) : Nat :=
  (Finset.univ.filter fun v ↦ p v = c).card

omit [Fintype V] [DecidableEq V] in
@[simp] theorem cellIndicator_mulVec
    (p : V → C) (x : C → ℝ) (v : V) :
    (cellIndicator p *ᵥ x) v = x (p v) := by
  simp [cellIndicator, Matrix.mulVec, dotProduct]

omit [Fintype V] [DecidableEq V] in
/-- Surjectivity of the cell map makes indicator lifting injective. -/
theorem cellIndicator_mulVecLin_injective
    (p : V → C) (hp : Function.Surjective p) :
    Function.Injective (cellIndicator p).mulVecLin := by
  intro x y h
  funext c
  obtain ⟨v, rfl⟩ := hp c
  have hv := congrFun h v
  simpa only [Matrix.mulVecLin_apply, cellIndicator_mulVec] using hv

omit [DecidableEq V] [Fintype C] in
/-- The indicator Gram matrix is the diagonal matrix of cell sizes. -/
theorem cellIndicator_gram (p : V → C) :
    (cellIndicator p).transpose * cellIndicator p =
      Matrix.diagonal (fun c ↦ (cellSize p c : ℝ)) := by
  ext c d
  by_cases h : c = d
  · subst d
    simp [Matrix.mul_apply, Matrix.transpose_apply, cellIndicator, cellSize, ← ite_and]
  · simp [Matrix.mul_apply, Matrix.transpose_apply, cellIndicator,
      Matrix.diagonal_apply_ne _ h]
    apply Finset.sum_eq_zero
    intro v hv
    split_ifs with hvc hvd
    · exact (h (hvd.symm.trans hvc)).elim
    all_goals rfl

/-- Adjacency matrix compressed to cell-indicator columns. -/
def cellCompression (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → C) : Matrix C C ℝ :=
  (cellIndicator p).transpose * G.adjMatrix ℝ * cellIndicator p

/-- Shifted cell compression.  The shift metric is the cell-size diagonal. -/
def cellPencil (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → C) (t : ℝ) : Matrix C C ℝ :=
  cellCompression G p - t • Matrix.diagonal (fun c ↦ (cellSize p c : ℝ))

omit [Fintype C] in
/-- The graph cell pencil is literally the compression of the shifted
adjacency matrix. -/
theorem cellPencil_eq_shifted_compression
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → C) (t : ℝ) :
    cellPencil G p t =
      (cellIndicator p).transpose * (G.adjMatrix ℝ - t • 1) * cellIndicator p := by
  rw [SpectralGraph.Inertia.shifted_compression, cellIndicator_gram]
  rfl

/-- Exact positive-index bounds obtained from a surjective graph cell map. -/
theorem partition_pos_bounds
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → C)
    (hp : Function.Surjective p) (t : ℝ) :
    (matrixInertia (cellPencil G p t)).pos ≤
        (matrixInertia (G.adjMatrix ℝ - t • 1)).pos ∧
      (matrixInertia (G.adjMatrix ℝ - t • 1)).pos ≤
        (matrixInertia (cellPencil G p t)).pos +
          (Fintype.card V - Fintype.card C) := by
  simpa [cellPencil, cellCompression, cellIndicator_gram] using
    SpectralGraph.Inertia.compression_pos_bounds
      (G.adjMatrix ℝ) (cellIndicator p)
      (cellIndicator_mulVecLin_injective p hp) t

/-- A compressed positive count places the selected ambient adjacency
eigenvalue strictly above the threshold. -/
theorem lt_adjacency_eigenvalue_of_lt_cellPencil_pos
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → C)
    (hp : Function.Surjective p) (t : ℝ)
    (k : Fin (Fintype.card V))
    (hk : k.val < (matrixInertia (cellPencil G p t)).pos) :
    t < (adjMatrix_isHermitian G).eigenvalues₀ k := by
  rw [lt_eigenvalues₀_iff]
  exact lt_of_lt_of_le hk (partition_pos_bounds G p hp t).1

/-- If the compressed count plus codimension is at most the selected index,
the ambient adjacency eigenvalue is at most the threshold. -/
theorem adjacency_eigenvalue_le_of_cellPencil_pos_add_le
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → C)
    (hp : Function.Surjective p) (t : ℝ)
    (k : Fin (Fintype.card V))
    (hk : (matrixInertia (cellPencil G p t)).pos +
      (Fintype.card V - Fintype.card C) ≤ k.val) :
    (adjMatrix_isHermitian G).eigenvalues₀ k ≤ t := by
  rw [eigenvalues₀_le_iff]
  exact le_trans (partition_pos_bounds G p hp t).2 hk

end SpectralGraph.Graph
