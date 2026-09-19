import SpectralGraph.Certificate.WitnessSubspace
import SpectralGraph.Certificate.WitnessInput

/-! # Strict external negative-subspace witness data -/

namespace SpectralGraph.Certificate

/-- Untrusted external columns and their alleged negative Gram diagonal.
The number of columns is the claimed negative-index lower bound; acceptance
proves their independence. -/
structure NegativeSubspaceData where
  columns : Array VectorData
  diagonal : Array ℚ
  deriving DecidableEq, Repr

namespace NegativeSubspaceData

def Valid (n : Nat) (c : NegativeSubspaceData) : Prop :=
  c.diagonal.size = c.columns.size ∧ ∀ j : Fin c.columns.size, (c.columns[j]).Valid n

instance (n : Nat) (c : NegativeSubspaceData) : Decidable (c.Valid n) :=
  inferInstanceAs (Decidable (c.diagonal.size = c.columns.size ∧
    ∀ j : Fin c.columns.size, (c.columns[j]).Valid n))

/-- Interpret columns with the dimension fixed by the ambient matrix. -/
def toMatrix (n : Nat) (c : NegativeSubspaceData) : Matrix (Fin n) (Fin c.columns.size) ℚ :=
  fun i j ↦ (c.columns[j]).toVector n i

/-- Total diagonal interpretation, guarded by exact-length checking below. -/
def toDiagonal (c : NegativeSubspaceData) : Fin c.columns.size → ℚ :=
  fun j ↦ c.diagonal[j.val]?.getD 0

def check {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ) (c : NegativeSubspaceData) : Bool :=
  decide (c.Valid n) && checkNegativeSubspace A (c.toMatrix n) c.toDiagonal

theorem check_valid {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ) (c : NegativeSubspaceData)
    (h : c.check A = true) : c.Valid n :=
  of_decide_eq_true (Bool.and_eq_true_iff.mp h).1

theorem check_sound {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ) (c : NegativeSubspaceData)
    (h : c.check A = true) : c.columns.size ≤ (matrixInertia (ratCastMatrix A)).neg := by
  simpa using checkNegativeSubspace_sound A (c.toMatrix n) c.toDiagonal
    (Bool.and_eq_true_iff.mp h).2

end NegativeSubspaceData

/-- Strict raw integer-matrix boundary for a negative-subspace certificate. -/
def DenseIntMatrix.checkNegativeSubspace (A : DenseIntMatrix) (c : NegativeSubspaceData) : Bool :=
  decide (A.entries.size = A.order * A.order) && c.check A.toRatMatrix

theorem DenseIntMatrix.checkNegativeSubspace_sound (A : DenseIntMatrix)
    (c : NegativeSubspaceData) (h : A.checkNegativeSubspace c = true) :
    c.columns.size ≤ (matrixInertia (ratCastMatrix A.toRatMatrix)).neg :=
  c.check_sound _ (Bool.and_eq_true_iff.mp h).2

theorem DenseIntMatrix.checkNegativeSubspace_valid (A : DenseIntMatrix)
    (c : NegativeSubspaceData) (h : A.checkNegativeSubspace c = true) :
    A.entries.size = A.order * A.order ∧ c.Valid A.order :=
  ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp h).1,
    c.check_valid _ (Bool.and_eq_true_iff.mp h).2⟩

end SpectralGraph.Certificate
