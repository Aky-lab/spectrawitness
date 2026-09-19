import SpectralGraph.Certificate.ProductWitnessSubspace
import SpectralGraph.Certificate.SpectralInterval
import SpectralGraph.Inertia.NegativeSpectrum

namespace SpectralGraphTests.ProductWitnessSubspace
open SpectralGraph SpectralGraph.Certificate SpectralGraph.Inertia Matrix

/-- A nontrivial three-column witness: two columns mix the first two ambient
coordinates, while the supplied image is checked independently. -/
def ambient : DenseIntMatrix :=
  ⟨4, #[-2, 0, 0, 0, 0, -3, 0, 0, 0, 0, -5, 0, 0, 0, 0, 7]⟩

def oldWitness : NegativeSubspaceData :=
  ⟨#[.sparse [(0, 1), (1, 1)], .sparse [(0, 3), (1, -2)], .sparse [(2, 1)]],
    #[-5, -30, -5]⟩

def suppliedWitness : ProductNegativeSubspaceData :=
  ⟨oldWitness.columns,
    #[.sparse [(0, -2), (1, -3)], .sparse [(0, -6), (1, 6)], .sparse [(2, -5)]],
    oldWitness.diagonal⟩

example : ambient.checkNegativeSubspace oldWitness = true := by decide +kernel
example : ambient.checkNegativeSubspaceWithImage suppliedWitness = true := by decide +kernel
example : suppliedWitness.check ambient.toRatMatrix = true := by decide +kernel
example : 3 ≤ (matrixInertia (ratCastMatrix ambient.toRatMatrix)).neg :=
  ambient.checkNegativeSubspaceWithImage_sound suppliedWitness (by decide +kernel)

-- The supplied-product route reduces to precisely the established checker.
example : checkNegativeSubspace ambient.toRatMatrix
    (suppliedWitness.toMatrix ambient.order) suppliedWitness.toDiagonal = true :=
  suppliedWitness.check_implies_checkNegativeSubspace ambient.toRatMatrix (by decide +kernel)

-- A false image or a false Gram diagonal is rejected before any conclusion.
example : ambient.checkNegativeSubspaceWithImage
    { suppliedWitness with imageColumns := #[(.sparse [(0, -2), (1, -2)]),
      .sparse [(0, -6), (1, 6)], .sparse [(2, -5)]] } = false := by decide +kernel
example : ambient.checkNegativeSubspaceWithImage
    { suppliedWitness with diagonal := #[-5, -29, -5] } = false := by decide +kernel

/- The semantic part of the public checker, deliberately without the raw-storage
guards.  The fixtures below use it to distinguish a malformed representation
from a different interpreted certificate. -/
private def unguarded (A : DenseIntMatrix) (c : ProductNegativeSubspaceData) : Bool :=
  checkNegativeSubspaceWithImage A.toRatMatrix (c.toMatrix A.order)
    (c.toImage A.order) c.toDiagonal

-- Surplus outer storage is ignored by total interpretation, but rejected at
-- the raw boundary.
private def surplusImage : ProductNegativeSubspaceData :=
  { suppliedWitness with imageColumns := suppliedWitness.imageColumns.push (.dense #[]) }
private def surplusDiagonal : ProductNegativeSubspaceData :=
  { suppliedWitness with diagonal := suppliedWitness.diagonal.push (-1) }
private def surplusMatrix : DenseIntMatrix := { ambient with entries := ambient.entries.push 999 }

example : unguarded ambient surplusImage = true := by decide +kernel
example : ambient.checkNegativeSubspaceWithImage surplusImage = false := by decide +kernel
example : unguarded ambient surplusDiagonal = true := by decide +kernel
example : ambient.checkNegativeSubspaceWithImage surplusDiagonal = false := by decide +kernel
example : unguarded surplusMatrix suppliedWitness = true := by decide +kernel
example : surplusMatrix.checkNegativeSubspaceWithImage suppliedWitness = false := by decide +kernel

-- Missing dense entries read as zero, and ignored dense tails do not change
-- the interpreted witness.
private def shortDense : ProductNegativeSubspaceData :=
  { suppliedWitness with columns := #[.dense #[1, 1], .dense #[3, -2], .dense #[0, 0, 1]] }
private def longDense : ProductNegativeSubspaceData :=
  { suppliedWitness with columns := #[.dense #[1, 1, 0, 0, 0],
      .dense #[3, -2, 0, 0, 0], .dense #[0, 0, 1, 0, 0]] }

example : unguarded ambient shortDense = true := by decide +kernel
example : ambient.checkNegativeSubspaceWithImage shortDense = false := by decide +kernel
example : unguarded ambient longDense = true := by decide +kernel
example : ambient.checkNegativeSubspaceWithImage longDense = false := by decide +kernel

-- Sparse interpretation sums duplicates and ignores out-of-range or zero
-- coordinates; each representation is nevertheless rejected.
private def duplicateSparse : ProductNegativeSubspaceData :=
  { suppliedWitness with columns := #[.sparse [(0, 2), (0, -1), (1, 1)],
      .sparse [(0, 3), (1, -2)], .sparse [(2, 1)]] }
private def outOfRangeSparse : ProductNegativeSubspaceData :=
  { suppliedWitness with columns := #[.sparse [(0, 1), (1, 1), (4, 9)],
      .sparse [(0, 3), (1, -2)], .sparse [(2, 1)]] }
private def explicitZeroSparse : ProductNegativeSubspaceData :=
  { suppliedWitness with columns := #[.sparse [(0, 1), (1, 1), (3, 0)],
      .sparse [(0, 3), (1, -2)], .sparse [(2, 1)]] }

example : unguarded ambient duplicateSparse = true := by decide +kernel
example : ambient.checkNegativeSubspaceWithImage duplicateSparse = false := by decide +kernel
example : unguarded ambient outOfRangeSparse = true := by decide +kernel
example : ambient.checkNegativeSubspaceWithImage outOfRangeSparse = false := by decide +kernel
example : unguarded ambient explicitZeroSparse = true := by decide +kernel
example : ambient.checkNegativeSubspaceWithImage explicitZeroSparse = false := by decide +kernel

-- The same representation guards apply independently to supplied image
-- vectors.  Splitting one coefficient preserves the interpreted image, but
-- the duplicate sparse coordinate is rejected at the raw boundary.
private def duplicateSparseImage : ProductNegativeSubspaceData :=
  { suppliedWitness with imageColumns := #[.sparse [(0, -1), (0, -1), (1, -3)],
      .sparse [(0, -6), (1, 6)], .sparse [(2, -5)]] }

example : unguarded ambient duplicateSparseImage = true := by decide +kernel
example : ambient.checkNegativeSubspaceWithImage duplicateSparseImage = false := by decide +kernel

-- An image component orthogonal to all witness columns keeps the Gram
-- equation true, so the rejection specifically tests the supplied product.
private def invisibleImage : ProductNegativeSubspaceData :=
  { suppliedWitness with imageColumns := #[.sparse [(0, -2), (1, -3), (3, 1)],
      .sparse [(0, -6), (1, 6)], .sparse [(2, -5)]] }

example : decide (invisibleImage.Valid ambient.order) = true := by decide +kernel
example : ambient.toRatMatrix * suppliedWitness.toMatrix ambient.order ≠
    invisibleImage.toImage ambient.order := by decide +kernel
example : (suppliedWitness.toMatrix 4).transpose * invisibleImage.toImage 4 =
    Matrix.diagonal suppliedWitness.toDiagonal := by decide +kernel
example : ambient.checkNegativeSubspaceWithImage invisibleImage = false := by decide +kernel

-- The empty witness is valid in a nonempty ambient space, whereas a nonempty
-- witness cannot have a negative Gram diagonal in a zero-dimensional space.
example : ambient.checkNegativeSubspaceWithImage ⟨#[], #[], #[]⟩ = true := by decide +kernel
example : (⟨0, #[]⟩ : DenseIntMatrix).checkNegativeSubspaceWithImage
    ⟨#[], #[], #[]⟩ = true := by decide +kernel
example : (⟨0, #[]⟩ : DenseIntMatrix).checkNegativeSubspaceWithImage
    ⟨#[.dense #[]], #[.dense #[]], #[-1]⟩ = false := by decide +kernel

-- A zero diagonal can satisfy both matrix equations, but strict negativity
-- remains a required, independently checked condition.
private def zeroDiagonal : ProductNegativeSubspaceData :=
  ⟨#[.dense #[0, 0, 0, 0]], #[.dense #[0, 0, 0, 0]], #[0]⟩
private def equationsHold (A : DenseIntMatrix) (c : ProductNegativeSubspaceData) : Bool :=
  decide (A.toRatMatrix * c.toMatrix A.order = c.toImage A.order ∧
    (c.toMatrix A.order).transpose * c.toImage A.order = Matrix.diagonal c.toDiagonal)

example : decide (zeroDiagonal.Valid ambient.order) = true := by decide +kernel
example : equationsHold ambient zeroDiagonal = true := by decide +kernel
example : unguarded ambient zeroDiagonal = false := by decide +kernel
example : ambient.checkNegativeSubspaceWithImage zeroDiagonal = false := by decide +kernel

/-- The same partial three-column certificate on a six-dimensional form gives
a spectral conclusion without computing full ambient inertia. -/
def partialForm : Matrix (Fin 6) (Fin 6) ℚ := diagonal ![9, 5, 3, -2, -2, -2]
def partialColumns : Array VectorData :=
  #[.sparse [(3, 1)], .sparse [(4, 1)], .sparse [(5, 1)]]
def partialImageColumns : Array VectorData :=
  #[.sparse [(3, -1)], .sparse [(4, -1)], .sparse [(5, -1)]]
def partialSupplied : ProductNegativeSubspaceData :=
  ⟨partialColumns, partialImageColumns, #[-1, -1, -1]⟩

theorem partialForm_hermitian : (ratCastMatrix partialForm).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases hij : i = j <;> simp [ratCastMatrix, partialForm, hij, eq_comm]

theorem fourth_eigenvalue_below_minus_one :
    partialForm_hermitian.eigenvalues₀ ⟨3, by decide⟩ < (-1 : ℝ) := by
  have hw := ProductNegativeSubspaceData.check_sound
    (partialForm - (-1 : ℚ) • 1) partialSupplied (by decide +kernel)
  rw [ratCast_shift] at hw
  apply eigenvalues₀_lt_of_negative_index (ratCastMatrix partialForm)
    partialForm_hermitian (-1) ⟨3, by decide⟩ 3 _ (by decide)
  simpa using hw

#print axioms checkNegativeSubspaceWithImage_sound
#print axioms DenseIntMatrix.checkNegativeSubspaceWithImage_valid
#print axioms fourth_eigenvalue_below_minus_one

end SpectralGraphTests.ProductWitnessSubspace
