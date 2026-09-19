import SpectralGraph.Graph.Extension
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Nat.Bitwise

/-!
# Executable row-bit encodings for finite simple graphs

The representation here is deliberately generic: an array entry is the
bitset of neighbours of one labelled vertex.  Decoding symmetrises the stored
relation and removes loops, so every array denotes a genuine simple graph.
The executable one-vertex extension is proved equal to the mathematical
operation in `GraphExtension`.
-/

namespace SpectralGraph
namespace Graph

open SimpleGraph

/-- Compact executable adjacency rows.  The order is supplied separately,
allowing the same representation to be used throughout an extension chain. -/
abbrev PackedAdjacencyRows := Array Nat

def packedAdjacencyRow (rows : PackedAdjacencyRows) (i : Nat) : Nat :=
  rows[i]?.getD 0

def packedAdjacencyBit (rows : PackedAdjacencyRows) (i j : Nat) : Bool :=
  (packedAdjacencyRow rows i).testBit j

/-- Undirected adjacency represented by either orientation of a stored bit.
This is the executable counterpart of the symmetrisation performed by
`graphOfPackedRows` (apart from the loop test, which callers on distinct
vertices do not need). -/
def packedUndirectedAdjacencyBit (rows : PackedAdjacencyRows) (i j : Nat) : Bool :=
  packedAdjacencyBit rows i j || packedAdjacencyBit rows j i

def packedDegreeAt (n : Nat) (rows : PackedAdjacencyRows) (v : Nat) : Nat :=
  if h : v < n then
    (Finset.univ.filter fun w : Fin n ↦
      w != (⟨v, h⟩ : Fin n) &&
        packedUndirectedAdjacencyBit rows v w.val).card
  else 0

/-- Mathematical graph denoted by row bitsets.  Either orientation of a
stored edge is accepted; loops are discarded by `SimpleGraph.fromRel`. -/
def graphOfPackedRows (n : Nat) (rows : PackedAdjacencyRows) :
    SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j ↦ packedAdjacencyBit rows i.val j.val

instance (n : Nat) (rows : PackedAdjacencyRows) :
    DecidableRel (graphOfPackedRows n rows).Adj := by
  intro i j
  simp only [graphOfPackedRows, SimpleGraph.fromRel_adj]
  infer_instance

@[simp] theorem graphOfPackedRows_adj_iff (n : Nat)
    (rows : PackedAdjacencyRows) (i j : Fin n) :
    (graphOfPackedRows n rows).Adj i j ↔
      i ≠ j ∧
        packedUndirectedAdjacencyBit rows i.val j.val = true := by
  simp [graphOfPackedRows, packedUndirectedAdjacencyBit, Bool.or_eq_true]

/-- Executable packed degree agrees with the semantic degree of the decoded
simple graph, even when malformed input rows contain self-bits. -/
theorem packedDegreeAt_eq_degree (n : Nat) (rows : PackedAdjacencyRows)
    (v : Fin n) :
    packedDegreeAt n rows v.val = (graphOfPackedRows n rows).degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  simp [packedDegreeAt, SimpleGraph.neighborFinset,
    graphOfPackedRows_adj_iff, v.isLt, ne_comm]

/-- Executably adjoin a final vertex with neighbour set `S`.  Old rows are
masked to the old order and acquire the new-vertex bit precisely for members
of `S`; the new row can be zero because decoding symmetrises adjacency. -/
def extendPackedRows {n : Nat} (rows : PackedAdjacencyRows)
    (S : Finset (Fin n)) : PackedAdjacencyRows :=
  Array.ofFn <| Fin.lastCases 0 fun u ↦
    (packedAdjacencyRow rows u.val % 2 ^ n) |||
      if u ∈ S then 2 ^ n else 0

@[simp] theorem packedAdjacencyRow_extend_old {n : Nat}
    (rows : PackedAdjacencyRows) (S : Finset (Fin n)) (u : Fin n) :
    packedAdjacencyRow (extendPackedRows rows S) u.val =
      (packedAdjacencyRow rows u.val % 2 ^ n) |||
        if u ∈ S then 2 ^ n else 0 := by
  simp only [packedAdjacencyRow, extendPackedRows, Array.getElem?_ofFn]
  rw [dif_pos (u.isLt.trans (Nat.lt_succ_self n))]
  simp only [Option.getD_some]
  have heq : (⟨u.val, u.isLt.trans (Nat.lt_succ_self n)⟩ : Fin (n + 1)) =
      u.castSucc := by rfl
  rw [heq]
  simp

@[simp] theorem packedAdjacencyRow_extend_last {n : Nat}
    (rows : PackedAdjacencyRows) (S : Finset (Fin n)) :
    packedAdjacencyRow (extendPackedRows rows S) n = 0 := by
  simp only [packedAdjacencyRow, extendPackedRows, Array.getElem?_ofFn]
  rw [dif_pos (Nat.lt_succ_self n)]
  simp only [Option.getD_some]
  have heq : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n := by rfl
  rw [heq]
  simp

@[simp] theorem packedAdjacencyBit_extend_old_old {n : Nat}
    (rows : PackedAdjacencyRows) (S : Finset (Fin n)) (u v : Fin n) :
    packedAdjacencyBit (extendPackedRows rows S) u.val v.val =
      packedAdjacencyBit rows u.val v.val := by
  by_cases hu : u ∈ S <;>
    simp [packedAdjacencyBit, hu, Nat.testBit_mod_two_pow, v.isLt,
      Nat.testBit_two_pow_of_ne (Nat.ne_of_gt v.isLt)]

@[simp] theorem packedAdjacencyBit_extend_old_last {n : Nat}
    (rows : PackedAdjacencyRows) (S : Finset (Fin n)) (u : Fin n) :
    packedAdjacencyBit (extendPackedRows rows S) u.val n = decide (u ∈ S) := by
  by_cases hu : u ∈ S <;>
    simp [packedAdjacencyBit, hu, Nat.testBit_mod_two_pow]

@[simp] theorem packedAdjacencyBit_extend_last_old {n : Nat}
    (rows : PackedAdjacencyRows) (S : Finset (Fin n)) (v : Fin n) :
    packedAdjacencyBit (extendPackedRows rows S) n v.val = false := by
  simp [packedAdjacencyBit]

/-- The optimized row-bit extension implements exactly the specification-level
one-vertex extension. -/
theorem graphOfPackedRows_extend {n : Nat} (rows : PackedAdjacencyRows)
    (S : Finset (Fin n)) :
    graphOfPackedRows (n + 1) (extendPackedRows rows S) =
      oneVertexExtension (graphOfPackedRows n rows) S := by
  ext i j
  refine Fin.lastCases ?_ (fun u ↦ ?_) i <;>
    refine Fin.lastCases ?_ (fun v ↦ ?_) j
  · simp
  · have hne : Fin.last n ≠ v.castSucc := (Fin.castSucc_ne_last v).symm
    simp [graphOfPackedRows_adj_iff, packedUndirectedAdjacencyBit, hne]
  · simp [graphOfPackedRows_adj_iff, packedUndirectedAdjacencyBit]
  · simp [graphOfPackedRows_adj_iff, packedUndirectedAdjacencyBit]

end Graph
end SpectralGraph

