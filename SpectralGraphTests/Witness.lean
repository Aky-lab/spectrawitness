import SpectralGraph.Certificate.WitnessSubspaceInput

namespace SpectralGraphTests.Witness
open SpectralGraph SpectralGraph.Certificate Matrix

def residual : Matrix (Fin 3) (Fin 3) ℚ := !![-2, 1, 0; 1, -2, 0; 0, 0, 0]

-- Rational coefficients, a nonorthogonal negative pair, and an exact kernel.
example : checkNegativeVector residual ![1/2, 0, 0] = true := by decide +kernel
example : checkNegativePair residual ![1, 0, 0] ![0, 1, 0] = true := by decide +kernel
example : checkKernelVector residual ![0, 0, 1] = true := by decide +kernel
example : 2 ≤ (matrixInertia (ratCastMatrix residual)).neg :=
  checkNegativePair_sound _ ![1, 0, 0] ![0, 1, 0] (by decide +kernel)
example : 1 ≤ (matrixInertia (ratCastMatrix residual)).zero :=
  checkKernelVector_sound _ ![0, 0, 1] (by decide +kernel)
example : ¬ IsUnit (ratCastMatrix residual) :=
  checkKernelVector_not_isUnit _ ![0, 0, 1] (by decide +kernel)

-- Zero/dependent vectors and an isotropic nonkernel vector cannot overclaim.
example : checkNegativeVector residual 0 = false := by decide +kernel
example : checkNegativePair residual ![1, 0, 0] ![2, 0, 0] = false := by decide +kernel
example : checkKernelVector residual 0 = false := by decide +kernel
example : checkKernelVector residual ![0, 1, 0] = false := by decide +kernel
example : checkKernelVector (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ)
    ![1, 0] = false := by decide +kernel
-- With only one cross term, omitting symmetry here would be unsound.
example : checkNegativePair (!![-1, 0; 100, -1] : Matrix (Fin 2) (Fin 2) ℚ)
    ![1, 0] ![0, 1] = false := by decide +kernel
example : checkKernelVector (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ)
    ![1, 0] = false := by decide +kernel

def intResidual : DenseIntMatrix := ⟨3, #[-2, 1, 0, 1, -2, 0, 0, 0, 0]⟩
def combined : VectorWitness := .negativeKernel
  (.ofIntSparse [(0, 1), (1, 1)]) (.dense #[0, 0, 1/3])

example : intResidual.checkWitness combined = true := by decide +kernel
example : 1 ≤ (matrixInertia (ratCastMatrix intResidual.toRatMatrix)).neg ∧
    1 ≤ (matrixInertia (ratCastMatrix intResidual.toRatMatrix)).zero :=
  intResidual.checkWitness_sound combined (by decide +kernel)
example : intResidual.checkWitness (.negativePair
    (.ofIntDense #[1, 0, 0]) (.sparse [(1, 1)])) = true := by decide +kernel

-- A sparse entry order is not a hidden normalization requirement.
example : intResidual.checkWitness (.negative (.sparse [(1, 1), (0, 1)])) = true := by
  decide +kernel
-- All these malformed inputs would still denote negative vectors under a
-- padding/truncation/summing interpretation. The strict boundary rejects them.
example : intResidual.checkWitness (.negative (.dense #[1])) = false := by decide +kernel
example : intResidual.checkWitness (.negative (.dense #[1, 0, 0, 0])) = false := by decide +kernel
example : intResidual.checkWitness (.negative (.sparse [(0, 1), (3, 1)])) = false := by
  decide +kernel
example : intResidual.checkWitness (.negative (.sparse [(0, -1), (0, 2)])) = false := by
  decide +kernel
example : intResidual.checkWitness (.negative (.sparse [(0, 1), (1, 0)])) = false := by
  decide +kernel
example : (⟨3, #[-2]⟩ : DenseIntMatrix).checkWitness
    (.negative (.sparse [(0, 1)])) = false := by decide +kernel
example : (⟨1, #[-2, 99]⟩ : DenseIntMatrix).checkWitness
    (.negative (.sparse [(0, 1)])) = false := by decide +kernel
example : (⟨0, #[]⟩ : DenseIntMatrix).checkWitness
    (.kernel (.dense #[])) = false := by decide +kernel

-- A three-dimensional witness in a four-dimensional indefinite matrix;
-- two columns are noncoordinate linear combinations.
def ambient : DenseIntMatrix :=
  ⟨4, #[-2, 0, 0, 0, 0, -3, 0, 0, 0, 0, -5, 0, 0, 0, 0, 7]⟩
def negativeThree : NegativeSubspaceData :=
  ⟨#[.sparse [(0, 1), (1, 1)], .sparse [(0, 3), (1, -2)], .sparse [(2, 1)]],
    #[-5, -30, -5]⟩
example : ambient.checkNegativeSubspace negativeThree = true := by decide +kernel
example : 3 ≤ (matrixInertia (ratCastMatrix ambient.toRatMatrix)).neg :=
  ambient.checkNegativeSubspace_sound negativeThree (by decide +kernel)

-- False Gram data, dependent columns, a positive column, and diagonal shape.
example : ambient.checkNegativeSubspace { negativeThree with diagonal := #[-5, -29, -5] }
    = false := by decide +kernel
example : ambient.checkNegativeSubspace
    ⟨#[.sparse [(0, 1)], .sparse [(0, 2)]], #[-2, -8]⟩ = false := by decide +kernel
example : ambient.checkNegativeSubspace ⟨#[.sparse [(3, 1)]], #[7]⟩ = false := by
  decide +kernel
example : ambient.checkNegativeSubspace { negativeThree with diagonal := #[-5, -30] }
    = false := by decide +kernel
example : ambient.checkNegativeSubspace { negativeThree with diagonal := #[-5, -30, -5, 0] }
    = false := by decide +kernel
example : ambient.checkNegativeSubspace
    ⟨#[.sparse [(0, 1), (4, 1)]], #[-2]⟩ = false := by decide +kernel
-- The zero-dimensional lower bound is meaningful and works at order zero.
example : (⟨0, #[]⟩ : DenseIntMatrix).checkNegativeSubspace ⟨#[], #[]⟩ = true := by
  decide +kernel

#print axioms checkNegativePair_sound
#print axioms checkKernelVector_sound
#print axioms checkNegativeSubspace_sound
#print axioms DenseIntMatrix.checkWitness_sound
#print axioms DenseIntMatrix.checkNegativeSubspace_valid

end SpectralGraphTests.Witness
