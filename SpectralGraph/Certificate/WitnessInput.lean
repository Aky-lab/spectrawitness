import SpectralGraph.Certificate.Witness
import SpectralGraph.Certificate.Integer

/-!
# Strict dense and sparse vector witness input

Raw files can use dense rational coordinates or sparse `(index, coefficient)`
lists. A checked dense vector has exactly the ambient dimension. A checked
sparse vector has in-range, distinct indices and nonzero coefficients. Sparse
order is immaterial. No fixed ambient dimension or support bound is imposed.

The total interpretation is useful for stating semantics but does not validate
input: public witness checkers always check the representation first. A separate
integer-matrix boundary checks the complete row-major storage length too.
-/

namespace SpectralGraph.Certificate

/-- External vector data, before dimension/support validation. -/
inductive VectorData where
  | dense (entries : Array ℚ)
  | sparse (entries : List (Nat × ℚ))
  deriving DecidableEq, Repr

namespace VectorData

/-- Integer vectors embed exactly in the rational witness format. -/
def ofIntDense (entries : Array Int) : VectorData := .dense (entries.map fun x : Int ↦ (x : ℚ))

def ofIntSparse (entries : List (Nat × Int)) : VectorData :=
  .sparse (entries.map fun p ↦ (p.1, (p.2 : ℚ)))

/-- Dense input is exact-length; sparse input has explicit, nonzero,
nonrepeated coefficients on in-range coordinates. -/
def Valid (n : Nat) : VectorData → Prop
  | .dense entries => entries.size = n
  | .sparse entries => (entries.map Prod.fst).Nodup ∧
      ∀ p ∈ entries, p.1 < n ∧ p.2 ≠ 0

instance (n : Nat) (v : VectorData) : Decidable (v.Valid n) := by
  cases v <;> unfold Valid <;> infer_instance

def valid (n : Nat) (v : VectorData) : Bool := decide (v.Valid n)

@[simp] theorem valid_eq_true_iff (n : Nat) (v : VectorData) :
    v.valid n = true ↔ v.Valid n := by simp [valid]

/-- Total interpretation; only use raw input as a certificate through a
checker that also establishes `Valid`. Duplicate sparse entries sum, but are
rejected by validation. -/
def toVector (n : Nat) : VectorData → Fin n → ℚ
  | .dense entries => fun i ↦ entries[i.val]?.getD 0
  | .sparse entries => fun i ↦
      ((entries.filter fun p ↦ p.1 == i.val).map Prod.snd).sum

end VectorData

/-- Small exact witnesses for common spectral exclusions. -/
inductive VectorWitness where
  | negative (u : VectorData)
  | negativePair (u v : VectorData)
  | kernel (u : VectorData)
  | negativeKernel (negative kernel : VectorData)
  deriving DecidableEq, Repr

namespace VectorWitness

/-- Every supplied vector has a valid external representation. -/
def Valid (n : Nat) : VectorWitness → Prop
  | .negative u | .kernel u => u.Valid n
  | .negativePair u v | .negativeKernel u v => u.Valid n ∧ v.Valid n

instance (n : Nat) (w : VectorWitness) : Decidable (w.Valid n) := by
  cases w <;> unfold Valid <;> infer_instance

def check {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ) (w : VectorWitness) : Bool :=
  decide (w.Valid n) && match w with
    | .negative u => checkNegativeVector A (u.toVector n)
    | .negativePair u v => checkNegativePair A (u.toVector n) (v.toVector n)
    | .kernel u => checkKernelVector A (u.toVector n)
    | .negativeKernel u v =>
        checkNegativeVector A (u.toVector n) && checkKernelVector A (v.toVector n)

/-- Semantic lower bounds carried by each witness kind. -/
def Conclusion {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) : VectorWitness → Prop
  | .negative _ => 1 ≤ (matrixInertia A).neg
  | .negativePair _ _ => 2 ≤ (matrixInertia A).neg
  | .kernel _ => 1 ≤ (matrixInertia A).zero
  | .negativeKernel _ _ => 1 ≤ (matrixInertia A).neg ∧ 1 ≤ (matrixInertia A).zero

theorem check_valid {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ) (w : VectorWitness)
    (h : w.check A = true) : w.Valid n :=
  of_decide_eq_true (Bool.and_eq_true_iff.mp h).1

theorem check_sound {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ) (w : VectorWitness)
    (h : w.check A = true) : w.Conclusion (ratCastMatrix A) := by
  have hc := (Bool.and_eq_true_iff.mp h).2
  cases w with
  | negative u => exact checkNegativeVector_sound _ _ hc
  | negativePair u v => exact checkNegativePair_sound _ _ _ hc
  | kernel u => exact checkKernelVector_sound _ _ hc
  | negativeKernel u v =>
      exact ⟨checkNegativeVector_sound _ _ (Bool.and_eq_true_iff.mp hc).1,
        checkKernelVector_sound _ _ (Bool.and_eq_true_iff.mp hc).2⟩

end VectorWitness

/-- A raw row-major integer matrix is accepted only with exact storage length
and valid witness data. The per-kind checker checks symmetry whenever needed. -/
def DenseIntMatrix.checkWitness (A : DenseIntMatrix) (w : VectorWitness) : Bool :=
  decide (A.entries.size = A.order * A.order) && w.check A.toRatMatrix

theorem DenseIntMatrix.checkWitness_sound (A : DenseIntMatrix) (w : VectorWitness)
    (h : A.checkWitness w = true) : w.Conclusion (ratCastMatrix A.toRatMatrix) :=
  w.check_sound _ (Bool.and_eq_true_iff.mp h).2

/-- Acceptance explicitly excludes missing entries, ignored tails and invalid
vector supports, independently of the semantic lower bound. -/
theorem DenseIntMatrix.checkWitness_valid (A : DenseIntMatrix) (w : VectorWitness)
    (h : A.checkWitness w = true) :
    A.entries.size = A.order * A.order ∧ w.Valid A.order :=
  ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp h).1,
    w.check_valid _ (Bool.and_eq_true_iff.mp h).2⟩

end SpectralGraph.Certificate


