import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.Dimension.Constructions
import SpectralGraph.Inertia.Basic

/-!
# Semantic matrix inertia

Inertia of the real quadratic form represented by a matrix. For a symmetric
matrix this is spectral inertia; for a nonsymmetric matrix it describes its
symmetric part. Nullity here is the radical dimension of the quadratic form.
-/

namespace SpectralGraph

open QuadraticForm

/-- Semantic inertia of the quadratic form represented by a real matrix. -/
noncomputable def matrixInertia {ι : Type _} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : Inertia :=
  let Q : QuadraticForm ℝ (ι → ℝ) := A.toQuadraticForm'
  { pos := sigPos Q
    zero := Module.finrank ℝ ↥(QuadraticMap.radical Q)
    neg := sigNeg Q }

/-- A positive-definite real matrix has zero nullity in semantic inertia. -/
theorem matrixInertia_zero_eq_zero_of_posDef
    {ι : Type _} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.toQuadraticForm'.PosDef) :
    (matrixInertia A).zero = 0 := by
  change Module.finrank ℝ ↥(QuadraticMap.radical A.toQuadraticForm') = 0
  have hradical : QuadraticMap.radical A.toQuadraticForm' = ⊥ := by
    ext x
    constructor
    · intro hx
      rw [Submodule.mem_bot]
      exact hA.anisotropic x hx.1
    · intro hx
      rw [Submodule.mem_bot] at hx
      subst x
      exact Submodule.zero_mem _
  rw [hradical]
  simp

/-- The three semantic inertia indices account for the whole ambient space. -/
theorem matrixInertia_order {ι : Type _} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) :
    (matrixInertia A).order = Fintype.card ι := by
  let Q : QuadraticForm ℝ (ι → ℝ) := A.toQuadraticForm'
  have hsig := sigPos_add_sigNeg_add_radical (Q := Q)
  have hdim : Module.finrank ℝ (ι → ℝ) = Fintype.card ι :=
    Module.finrank_fintype_fun_eq_card ℝ
  change sigPos Q + Module.finrank ℝ ↥(QuadraticMap.radical Q) +
      sigNeg Q = Fintype.card ι
  rw [← hdim]
  simpa [add_assoc, add_left_comm, add_comm] using hsig

/-- Matrix signature, defined as `n₊ - n₋`. -/
noncomputable def matrixSignature {ι : Type _} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : Int :=
  (matrixInertia A).signature

@[simp] theorem matrixSignature_eq {ι : Type _} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) :
    matrixSignature A =
      ((sigPos A.toQuadraticForm' : Nat) : Int) -
        ((sigNeg A.toQuadraticForm' : Nat) : Int) := rfl

end SpectralGraph
