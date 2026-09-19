import SpectralGraph.Graph.EncodingCheck
import SpectralGraph.Certificate.IntegerCheck

/-! # Strict packed graph inertia certificates at integer thresholds -/

namespace SpectralGraph.Graph
open SpectralGraph.Certificate Matrix

/-- Dense integer shifted adjacency constructed directly from packed edges. -/
def packedShiftedAdjacency (n : Nat) (rows : PackedAdjacencyRows) (t : Int) :
    DenseIntMatrix :=
  DenseIntMatrix.ofFn n fun i j ↦
    if i = j then -t else if packedUndirectedAdjacencyBit rows i j then 1 else 0

/-- Exact matrix construction agrees with mathlib's shifted adjacency. -/
theorem packedShiftedAdjacency_toRatMatrix (n : Nat) (rows : PackedAdjacencyRows) (t : Int) :
    (packedShiftedAdjacency n rows t).toRatMatrix =
      (graphOfPackedRows n rows).adjMatrix ℚ - (t : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) := by
  change (fun i j : Fin n ↦ ((DenseIntMatrix.ofFn n (fun i j ↦
    if i = j then -t else if packedUndirectedAdjacencyBit rows i j then 1 else 0)).entry i j : ℚ)) = _
  ext i j
  change ((DenseIntMatrix.ofFn n _).entry i j : ℚ) = _
  rw [DenseIntMatrix.entry_ofFn n _ i j i.isLt j.isLt]
  by_cases hij : i = j
  · subst j
    simp [SimpleGraph.adjMatrix]
  · have hv : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
    by_cases hbit : packedUndirectedAdjacencyBit rows i.val j.val = true <;>
      simp [SimpleGraph.adjMatrix, graphOfPackedRows_adj_iff, hij, hv, hbit]

/-- Validate the edge encoding, then check the claimed inertia using the
proved integer algorithm. Neither malformed rows nor malformed matrices are
silently accepted by this public certificate boundary. -/
def checkPackedInertia (n : Nat) (rows : PackedAdjacencyRows) (t : Int) (target : Inertia) : Bool :=
  packedRowsValid n rows && (packedShiftedAdjacency n rows t).checkInertia target

/-- A successful packed certificate proves the real shifted adjacency inertia. -/
theorem checkPackedInertia_sound (n : Nat) (rows : PackedAdjacencyRows)
    (t : Int) (target : Inertia) (h : checkPackedInertia n rows t target = true) :
    matrixInertia ((graphOfPackedRows n rows).adjMatrix ℝ -
      (t : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) = target := by
  have hc := Bool.and_eq_true_iff.mp h
  have hi := DenseIntMatrix.checkInertia_sound _ target hc.2
  have hm : ratCastMatrix (packedShiftedAdjacency n rows t).toRatMatrix =
      (graphOfPackedRows n rows).adjMatrix ℝ -
        (t : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [packedShiftedAdjacency_toRatMatrix]
    change ((graphOfPackedRows n rows).adjMatrix ℚ - (t : ℚ) •
      (1 : Matrix (Fin n) (Fin n) ℚ)).map (Rat.castHom ℝ) = _
    ext i j
    by_cases hij : i = j
    · subst j
      simp [SimpleGraph.adjMatrix]
    · by_cases hbit : packedUndirectedAdjacencyBit rows i.val j.val = true <;>
        simp [SimpleGraph.adjMatrix, graphOfPackedRows_adj_iff, hij, hbit]
  rwa [hm] at hi

/-- Successful spectral checks also certify the external edge representation. -/
theorem checkPackedInertia_valid (n : Nat) (rows : PackedAdjacencyRows)
    (t : Int) (target : Inertia) (h : checkPackedInertia n rows t target = true) :
    PackedRowsValid n rows :=
  (packedRowsValid_eq_true_iff n rows).mp (Bool.and_eq_true_iff.mp h).1

/-- Apply a Boolean predicate to computed inertia, retaining the strict
representation and symmetry checks of `checkPackedInertia`. -/
def checkPackedInertiaProperty (n : Nat) (rows : PackedAdjacencyRows)
    (t : Int) (test : Inertia → Bool) : Bool :=
  let I := discoverIntegerInertiaV2 (packedShiftedAdjacency n rows t)
  checkPackedInertia n rows t I && test I

/-- The executable predicate holds of semantic real inertia on acceptance. -/
theorem checkPackedInertiaProperty_sound (n : Nat) (rows : PackedAdjacencyRows)
    (t : Int) (test : Inertia → Bool)
    (h : checkPackedInertiaProperty n rows t test = true) :
    test (matrixInertia ((graphOfPackedRows n rows).adjMatrix ℝ -
      (t : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))) = true := by
  have hc := Bool.and_eq_true_iff.mp h
  rw [checkPackedInertia_sound n rows t _ hc.1]
  exact hc.2

end SpectralGraph.Graph
