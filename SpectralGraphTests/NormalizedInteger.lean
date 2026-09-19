import SpectralGraph.Certificate.NormalizedInteger

/-! Kernel evaluation of exact normalization, pivots, nullity, and rejected input. -/
namespace SpectralGraphTests.NormalizedInteger
open SpectralGraph SpectralGraph.Certificate

def scaled : DenseIntMatrix := ⟨2, #[120, -60, -60, 180]⟩

example : scaled.contentCandidate = 60 := by decide
example : scaled.normalizeContent.entries = #[2, -1, -1, 3] := by decide
example : scaled.checkedDivisor 0 = 1 := by decide
example : scaled.checkedDivisor (-60) = 1 := by decide
example : scaled.checkedDivisor 7 = 1 := by decide
example : scaled.checkedDivisor 30 = 30 := by decide
example : scaled.checkNormalizedInertia ⟨2, 0, 0⟩ = true := by decide
example : matrixInertia (ratCastMatrix scaled.toRatMatrix) = ⟨2, 0, 0⟩ :=
  scaled.checkNormalizedInertia_sound _ (by decide)

-- Off-diagonal pivot requires a basis addition before Schur elimination.
def hyperbolic : DenseIntMatrix := ⟨2, #[0, 60, 60, 0]⟩
example : hyperbolic.checkNormalizedInertia ⟨1, 0, 1⟩ = true := by decide

-- Negative pivots and a singular Schur remainder are both represented.
def singular : DenseIntMatrix := ⟨3, #[12, 6, 0, 6, 0, 6, 0, 6, -12]⟩
example : singular.checkNormalizedInertia ⟨1, 1, 1⟩ = true := by decide
example : singular.checkNormalizedInertia ⟨2, 0, 1⟩ = false := by decide
example : (DenseIntMatrix.ofFn 3 (fun i j ↦ -(singular.entry i j))).checkNormalizedInertia
    ⟨1, 1, 1⟩ = true := by decide

-- A first remainder that would have content 144 is reduced to the identity.
def diagonalScale : DenseIntMatrix := DenseIntMatrix.ofFn 4 fun i j ↦ if i = j then 12 else 0
example : (diagonalScale.signedDiagonalRemainder 0).contentCandidate = 144 := by decide
example : (diagonalScale.signedDiagonalRemainder 0).normalizeContent.entries =
    #[1, 0, 0, 0, 1, 0, 0, 0, 1] := by decide
example : diagonalScale.checkNormalizedInertia ⟨4, 0, 0⟩ = true := by decide

example : (⟨0, #[]⟩ : DenseIntMatrix).checkNormalizedInertia ⟨0, 0, 0⟩ = true := by decide
example : (⟨2, #[0, 0, 0, 0]⟩ : DenseIntMatrix).normalizeContent.entries = #[0, 0, 0, 0] := by decide
example : (⟨2, #[1]⟩ : DenseIntMatrix).checkNormalizedInertia ⟨1, 1, 0⟩ = false := by decide
example : (⟨1, #[1, 2]⟩ : DenseIntMatrix).checkNormalizedInertia ⟨1, 0, 0⟩ = false := by decide
example : (⟨2, #[1, 2, 3, 4]⟩ : DenseIntMatrix).checkNormalizedInertia ⟨1, 0, 1⟩ = false := by decide

#print axioms SpectralGraph.Certificate.matrixInertia_eq_discoverNormalizedIntegerInertia
#print axioms SpectralGraph.Certificate.DenseIntMatrix.checkNormalizedInertia_sound

end SpectralGraphTests.NormalizedInteger
