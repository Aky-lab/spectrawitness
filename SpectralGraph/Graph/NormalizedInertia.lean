import SpectralGraph.Graph.PackedInertia
import SpectralGraph.Graph.Threshold
import SpectralGraph.Certificate.NormalizedInteger

/-!
# Packed graph certificates using normalized integer elimination

This boundary reuses the established packed representation and shifted matrix
construction. Exact row count, in-range bits, and absence of loops are required.
Oriented storage is allowed: either or both orientations encode an undirected
edge. Its constructed matrix is symmetric even for one-sided edge storage.

The algorithm removes checked positive common factors from Schur remainders.
No floating-point approximation or external producer is required.
-/

namespace SpectralGraph.Graph
open SpectralGraph.Certificate Matrix

private theorem packedShiftedAdjacency_isSymm (n : Nat) (rows : PackedAdjacencyRows) (t : Int) :
    (packedShiftedAdjacency n rows t).toRatMatrix.IsSymm := by
  rw [packedShiftedAdjacency_toRatMatrix]
  exact (graphOfPackedRows n rows).isSymm_adjMatrix.sub (Matrix.isSymm_one.smul _)

private theorem packedShiftedAdjacency_cast (n : Nat) (rows : PackedAdjacencyRows) (t : Int) :
    ratCastMatrix (packedShiftedAdjacency n rows t).toRatMatrix =
      (graphOfPackedRows n rows).adjMatrix ℝ -
        (t : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  rw [packedShiftedAdjacency_toRatMatrix]
  simpa [adjacencyShift] using adjacencyShift_cast (graphOfPackedRows n rows) (t : ℚ)

/-- Strict packed graph check with normalized integer elimination, at any
integral threshold. It has exactly the same acceptance semantics as the
established `checkPackedInertia` checker. -/
def checkPackedNormalizedInertia (n : Nat) (rows : PackedAdjacencyRows)
    (t : Int) (target : Inertia) : Bool :=
  packedRowsValid n rows && (packedShiftedAdjacency n rows t).checkNormalizedInertia target

theorem checkPackedNormalizedInertia_sound (n : Nat) (rows : PackedAdjacencyRows)
    (t : Int) (target : Inertia) (h : checkPackedNormalizedInertia n rows t target = true) :
    matrixInertia ((graphOfPackedRows n rows).adjMatrix ℝ -
      (t : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) = target := by
  have hi := DenseIntMatrix.checkNormalizedInertia_sound _ target (Bool.and_eq_true_iff.mp h).2
  rwa [packedShiftedAdjacency_cast] at hi

theorem checkPackedNormalizedInertia_valid (n : Nat) (rows : PackedAdjacencyRows)
    (t : Int) (target : Inertia) (h : checkPackedNormalizedInertia n rows t target = true) :
    PackedRowsValid n rows :=
  (packedRowsValid_eq_true_iff n rows).mp (Bool.and_eq_true_iff.mp h).1

/-- Drop-in equivalence includes malformed input and every claimed target. -/
theorem checkPackedNormalizedInertia_eq_checkPackedInertia (n : Nat)
    (rows : PackedAdjacencyRows) (t : Int) (target : Inertia) :
    checkPackedNormalizedInertia n rows t target = checkPackedInertia n rows t target := by
  simp only [checkPackedNormalizedInertia, checkPackedInertia,
    DenseIntMatrix.checkNormalizedInertia, DenseIntMatrix.checkInertia,
    discoverNormalizedIntegerInertia_eq_v2 _ (packedShiftedAdjacency_isSymm n rows t)]

/-- Apply an inertia predicate during exhaustive graph verification. The
normalized algorithm runs once; symmetry and dimensions follow from the shared
matrix constructor, while packed-row validity is checked explicitly. -/
def checkPackedNormalizedInertiaProperty (n : Nat) (rows : PackedAdjacencyRows)
    (t : Int) (test : Inertia → Bool) : Bool :=
  packedRowsValid n rows && test (discoverNormalizedIntegerInertia (packedShiftedAdjacency n rows t))

theorem checkPackedNormalizedInertiaProperty_sound (n : Nat) (rows : PackedAdjacencyRows)
    (t : Int) (test : Inertia → Bool)
    (h : checkPackedNormalizedInertiaProperty n rows t test = true) :
    test (matrixInertia ((graphOfPackedRows n rows).adjMatrix ℝ -
      (t : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))) = true := by
  have hi := matrixInertia_eq_discoverNormalizedIntegerInertia
    (packedShiftedAdjacency n rows t) (packedShiftedAdjacency_isSymm n rows t)
  rw [packedShiftedAdjacency_cast] at hi
  exact (congrArg test hi).trans (Bool.and_eq_true_iff.mp h).2

theorem checkPackedNormalizedInertiaProperty_valid (n : Nat) (rows : PackedAdjacencyRows)
    (t : Int) (test : Inertia → Bool)
    (h : checkPackedNormalizedInertiaProperty n rows t test = true) :
    PackedRowsValid n rows :=
  (packedRowsValid_eq_true_iff n rows).mp (Bool.and_eq_true_iff.mp h).1

end SpectralGraph.Graph
