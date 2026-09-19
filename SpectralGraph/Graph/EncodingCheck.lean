import SpectralGraph.Graph.Encoding
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

/-!
# Strict contracts for packed adjacency data

The total decoder deliberately accepts every array. At an external certificate
boundary, use `packedRowsValid` to reject wrong dimensions, out-of-range bits,
and loops. Edges may be stored in either or both orientations. Applications
requiring a full symmetric adjacency table use `symmetricPackedRowsValid`.
These are separate contracts: upper-triangular storage is a valid edge encoding.
-/

namespace SpectralGraph.Graph

/-- Exact dimensions, no out-of-range bits, and no stored loops. -/
def PackedRowsValid (n : Nat) (rows : PackedAdjacencyRows) : Prop :=
  rows.size = n ∧ ∀ i : Fin n,
    packedAdjacencyRow rows i.val < 2 ^ n ∧
      packedAdjacencyBit rows i.val i.val = false

instance (n : Nat) (rows : PackedAdjacencyRows) : Decidable (PackedRowsValid n rows) :=
  inferInstanceAs (Decidable (rows.size = n ∧ ∀ i : Fin n,
    packedAdjacencyRow rows i.val < 2 ^ n ∧
      packedAdjacencyBit rows i.val i.val = false))

/-- Strict executable validation of an oriented edge encoding. -/
def packedRowsValid (n : Nat) (rows : PackedAdjacencyRows) : Bool :=
  decide (PackedRowsValid n rows)

@[simp] theorem packedRowsValid_eq_true_iff (n : Nat) (rows : PackedAdjacencyRows) :
    packedRowsValid n rows = true ↔ PackedRowsValid n rows := by
  simp [packedRowsValid]

/-- A full adjacency table stores both orientations of each edge. -/
def SymmetricPackedRowsValid (n : Nat) (rows : PackedAdjacencyRows) : Prop :=
  PackedRowsValid n rows ∧ ∀ i j : Fin n,
    packedAdjacencyBit rows i.val j.val = packedAdjacencyBit rows j.val i.val

instance (n : Nat) (rows : PackedAdjacencyRows) :
    Decidable (SymmetricPackedRowsValid n rows) :=
  inferInstanceAs (Decidable (PackedRowsValid n rows ∧ ∀ i j : Fin n,
    packedAdjacencyBit rows i.val j.val = packedAdjacencyBit rows j.val i.val))

def symmetricPackedRowsValid (n : Nat) (rows : PackedAdjacencyRows) : Bool :=
  decide (SymmetricPackedRowsValid n rows)

@[simp] theorem symmetricPackedRowsValid_eq_true_iff (n : Nat)
    (rows : PackedAdjacencyRows) :
    symmetricPackedRowsValid n rows = true ↔ SymmetricPackedRowsValid n rows := by
  simp [symmetricPackedRowsValid]

/-- For a checked full table the stored bits are exactly semantic adjacency;
the total decoder cannot silently repair any accepted row. -/
theorem graphOfPackedRows_adj_iff_of_symmetric {n : Nat} {rows : PackedAdjacencyRows}
    (h : SymmetricPackedRowsValid n rows) (i j : Fin n) :
    (graphOfPackedRows n rows).Adj i j ↔ packedAdjacencyBit rows i.val j.val = true := by
  rw [graphOfPackedRows_adj_iff]
  by_cases hij : i = j
  · subst j
    simp [packedUndirectedAdjacencyBit, (h.1.2 i).2]
  · simp [packedUndirectedAdjacencyBit, ← h.2 i j, hij]

/-- The executable matrix uses the same forgiving semantics as the graph
decoder, so this bridge needs no well-formedness assumption. -/
def packedAdjacencyMatrix (R : Type*) [Zero R] [One R]
    (n : Nat) (rows : PackedAdjacencyRows) : Matrix (Fin n) (Fin n) R :=
  fun i j ↦ if i ≠ j ∧ packedUndirectedAdjacencyBit rows i.val j.val = true then 1 else 0

theorem packedAdjacencyMatrix_eq_adjMatrix (R : Type*) [Zero R] [One R]
    (n : Nat) (rows : PackedAdjacencyRows) :
    packedAdjacencyMatrix R n rows = (graphOfPackedRows n rows).adjMatrix R := by
  ext i j
  simp only [packedAdjacencyMatrix, SimpleGraph.adjMatrix, Matrix.of_apply, graphOfPackedRows_adj_iff]

/-- A checked symmetric file may be fed directly to a matrix certificate
without symmetrising its raw bit entries. -/
theorem rawPackedMatrix_eq_adjMatrix (R : Type*) [Zero R] [One R]
    {n : Nat} {rows : PackedAdjacencyRows} (h : SymmetricPackedRowsValid n rows) :
    (fun i j : Fin n ↦ if packedAdjacencyBit rows i.val j.val then (1 : R) else 0) =
      (graphOfPackedRows n rows).adjMatrix R := by
  ext i j
  simp only [SimpleGraph.adjMatrix, Matrix.of_apply, graphOfPackedRows_adj_iff_of_symmetric h]

/-- Semantic equality ignores the choice of orientation for each stored edge. -/
theorem graphOfPackedRows_eq_iff (n : Nat) (a b : PackedAdjacencyRows) :
    graphOfPackedRows n a = graphOfPackedRows n b ↔
      ∀ i j : Fin n, i ≠ j →
        packedUndirectedAdjacencyBit a i.val j.val =
          packedUndirectedAdjacencyBit b i.val j.val := by
  constructor
  · intro h i j hij
    have he : (graphOfPackedRows n a).Adj i j ↔ (graphOfPackedRows n b).Adj i j := by
      rw [h]
    simpa [graphOfPackedRows_adj_iff, hij] using he
  · intro h
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · simp [graphOfPackedRows_adj_iff, hij, h i j hij]

end SpectralGraph.Graph

