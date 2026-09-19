import SpectralGraph.Certificate.WitnessSubspaceInput

/-!
# Negative subspace certificates with a supplied product

The producer may supply the image of the witness columns under the ambient
matrix.  The checker verifies two separate product identities,
`A * U = W` and `U.transpose * W = Matrix.diagonal d`.  By associativity,
soundness reduces to the established Gram checker.
-/

namespace SpectralGraph.Certificate
open Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Check a negative subspace using a producer-supplied image `W = A * U`. -/
def checkNegativeSubspaceWithImage (A : Matrix ι ι ℚ) (U W : Matrix ι κ ℚ)
    (d : κ → ℚ) : Bool :=
  decide (A * U = W ∧ U.transpose * W = Matrix.diagonal d ∧ ∀ j, d j < 0)

omit [DecidableEq ι] in
/-- The checked product reduces the supplied-product path to the original
negative-subspace checker. -/
theorem checkNegativeSubspaceWithImage_implies_checkNegativeSubspace
    (A : Matrix ι ι ℚ) (U W : Matrix ι κ ℚ) (d : κ → ℚ)
    (h : checkNegativeSubspaceWithImage A U W d = true) :
    checkNegativeSubspace A U d = true := by
  have hc : A * U = W ∧ U.transpose * W = Matrix.diagonal d ∧ ∀ j, d j < 0 :=
    of_decide_eq_true h
  apply decide_eq_true
  refine ⟨?_, hc.2.2⟩
  simpa only [Matrix.mul_assoc, hc.1] using hc.2.1

/-- Acceptance of a supplied-product certificate has the usual negative-index
lower bound. -/
theorem checkNegativeSubspaceWithImage_sound (A : Matrix ι ι ℚ)
    (U W : Matrix ι κ ℚ) (d : κ → ℚ)
    (h : checkNegativeSubspaceWithImage A U W d = true) :
    Fintype.card κ ≤ (matrixInertia (ratCastMatrix A)).neg :=
  checkNegativeSubspace_sound A U d
    (checkNegativeSubspaceWithImage_implies_checkNegativeSubspace A U W d h)

/-- Raw supplied-product data.  Both families of columns and the diagonal are
untrusted; `Valid` below fixes their common witness dimension exactly. -/
structure ProductNegativeSubspaceData where
  columns : Array VectorData
  imageColumns : Array VectorData
  diagonal : Array ℚ
  deriving DecidableEq, Repr

namespace ProductNegativeSubspaceData

/-- Exact column counts and exact vector representations at ambient dimension
`n`.  In particular, image columns are independently range/support checked. -/
def Valid (n : Nat) (c : ProductNegativeSubspaceData) : Prop :=
  c.imageColumns.size = c.columns.size ∧ c.diagonal.size = c.columns.size ∧
    (∀ j : Fin c.columns.size, (c.columns[j]).Valid n) ∧
    ∀ j : Fin c.columns.size, (c.imageColumns[j.val]?.getD (.dense #[])).Valid n

instance (n : Nat) (c : ProductNegativeSubspaceData) : Decidable (c.Valid n) :=
  inferInstanceAs (Decidable (c.imageColumns.size = c.columns.size ∧
    c.diagonal.size = c.columns.size ∧
    (∀ j : Fin c.columns.size, (c.columns[j]).Valid n) ∧
    ∀ j : Fin c.columns.size, (c.imageColumns[j.val]?.getD (.dense #[])).Valid n))

def toMatrix (n : Nat) (c : ProductNegativeSubspaceData) :
    Matrix (Fin n) (Fin c.columns.size) ℚ :=
  fun i j ↦ (c.columns[j]).toVector n i

/-- Total interpretation of untrusted image data, guarded by `Valid` in every
public checker. -/
def toImage (n : Nat) (c : ProductNegativeSubspaceData) :
    Matrix (Fin n) (Fin c.columns.size) ℚ :=
  fun i j ↦ (c.imageColumns[j.val]?.getD (.dense #[])).toVector n i

/-- Total diagonal interpretation, also guarded by its exact-length check. -/
def toDiagonal (c : ProductNegativeSubspaceData) : Fin c.columns.size → ℚ :=
  fun j ↦ c.diagonal[j.val]?.getD 0

def check {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ)
    (c : ProductNegativeSubspaceData) : Bool :=
  decide (c.Valid n) &&
    checkNegativeSubspaceWithImage A (c.toMatrix n) (c.toImage n) c.toDiagonal

theorem check_valid {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ)
    (c : ProductNegativeSubspaceData) (h : c.check A = true) : c.Valid n :=
  of_decide_eq_true (Bool.and_eq_true_iff.mp h).1

theorem check_implies_checkNegativeSubspace {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ)
    (c : ProductNegativeSubspaceData) (h : c.check A = true) :
    checkNegativeSubspace A (c.toMatrix n) c.toDiagonal = true :=
  checkNegativeSubspaceWithImage_implies_checkNegativeSubspace A (c.toMatrix n)
    (c.toImage n) c.toDiagonal (Bool.and_eq_true_iff.mp h).2

theorem check_sound {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ)
    (c : ProductNegativeSubspaceData) (h : c.check A = true) :
    c.columns.size ≤ (matrixInertia (ratCastMatrix A)).neg := by
  simpa using checkNegativeSubspaceWithImage_sound A (c.toMatrix n) (c.toImage n)
    c.toDiagonal (Bool.and_eq_true_iff.mp h).2

end ProductNegativeSubspaceData

/-- Strict row-major integer-matrix boundary for supplied-product negative
subspace certificates. -/
def DenseIntMatrix.checkNegativeSubspaceWithImage (A : DenseIntMatrix)
    (c : ProductNegativeSubspaceData) : Bool :=
  decide (A.entries.size = A.order * A.order) && c.check A.toRatMatrix

theorem DenseIntMatrix.checkNegativeSubspaceWithImage_sound (A : DenseIntMatrix)
    (c : ProductNegativeSubspaceData) (h : A.checkNegativeSubspaceWithImage c = true) :
    c.columns.size ≤ (matrixInertia (ratCastMatrix A.toRatMatrix)).neg :=
  c.check_sound _ (Bool.and_eq_true_iff.mp h).2

theorem DenseIntMatrix.checkNegativeSubspaceWithImage_valid (A : DenseIntMatrix)
    (c : ProductNegativeSubspaceData) (h : A.checkNegativeSubspaceWithImage c = true) :
    A.entries.size = A.order * A.order ∧ c.Valid A.order :=
  ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp h).1,
    c.check_valid _ (Bool.and_eq_true_iff.mp h).2⟩

end SpectralGraph.Certificate
