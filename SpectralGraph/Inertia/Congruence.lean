import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import SpectralGraph.Inertia.Matrix

/-!
# Inertia invariance under quadratic-form equivalence

This is the reusable Sylvester-law interface used by the later exact
congruence and Schur-complement layers.

Rather than tie the semantic inertia API to a particular matrix elimination
algorithm, we first prove the strongest basis-free statement: equivalent real
quadratic forms have the same `(positive, zero, negative)` inertia triple.
-/

namespace SpectralGraph

/-- Equivalent real quadratic forms represented by finite matrices have the
same semantic inertia.  This packages mathlib's invariance of positive
signature, negative signature, and radical rank into the
`Inertia` structure. -/
theorem matrixInertia_eq_of_equivalent
    {ι κ : Type _}
    [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (h : QuadraticMap.Equivalent A.toQuadraticForm' B.toQuadraticForm') :
    matrixInertia A = matrixInertia B := by
  change Inertia.mk
      (sigPos A.toQuadraticForm')
      (Module.finrank ℝ ↥(QuadraticMap.radical A.toQuadraticForm'))
      (sigNeg A.toQuadraticForm') =
    Inertia.mk
      (sigPos B.toQuadraticForm')
      (Module.finrank ℝ ↥(QuadraticMap.radical B.toQuadraticForm'))
      (sigNeg B.toQuadraticForm')
  rw [h.sigPos_eq, h.rank_radical_eq, h.sigNeg_eq]

/-- Equivalent quadratic forms also have equal matrix signature. -/
theorem matrixSignature_eq_of_equivalent
    {ι κ : Type _}
    [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (h : QuadraticMap.Equivalent A.toQuadraticForm' B.toQuadraticForm') :
    matrixSignature A = matrixSignature B := by
  rw [matrixSignature, matrixSignature]
  rw [matrixInertia_eq_of_equivalent A B h]


/-- Invertible matrix congruence preserves semantic inertia.

If `B = Pᵀ A P` and `P` is invertible, then the quadratic forms represented by
`A` and `B` are equivalent, hence have the same `(n₊,n₀,n₋)` triple. -/
theorem matrixInertia_eq_of_congr
    {ι : Type _} [Fintype ι] [DecidableEq ι]
    (A B P : Matrix ι ι ℝ) [Invertible P]
    (hB : B = P.transpose * A * P) :
    matrixInertia A = matrixInertia B := by
  let e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) :=
    Matrix.toLinearEquiv' P (inferInstance : Invertible P)
  have hbilin :
      (Matrix.toLinearMap₂' ℝ) B =
        ((Matrix.toLinearMap₂' ℝ) A).compl₁₂ (Matrix.toLin' P) (Matrix.toLin' P) := by
    apply (LinearMap.toMatrix₂' ℝ).injective
    simp [hB]
  have hquad :
      B.toQuadraticForm' =
        A.toQuadraticForm'.comp (Matrix.toLin' P) := by
    unfold Matrix.toQuadraticForm'
    rw [hbilin, LinearMap.BilinMap.toQuadraticMap_comp_same]
  have hquad_e :
      B.toQuadraticForm' =
        A.toQuadraticForm'.comp (e : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) := by
    simpa [e] using hquad
  have hiso := QuadraticMap.isometryEquivOfCompLinearEquiv A.toQuadraticForm' e
  have hequiv : QuadraticMap.Equivalent A.toQuadraticForm' B.toQuadraticForm' := by
    rw [hquad_e]
    exact ⟨hiso⟩
  exact matrixInertia_eq_of_equivalent A B hequiv

/-- Invertible matrix congruence also preserves matrix signature. -/
theorem matrixSignature_eq_of_congr
    {ι : Type _} [Fintype ι] [DecidableEq ι]
    (A B P : Matrix ι ι ℝ) [Invertible P]
    (hB : B = P.transpose * A * P) :
    matrixSignature A = matrixSignature B := by
  rw [matrixSignature, matrixSignature, matrixInertia_eq_of_congr A B P hB]

end SpectralGraph
