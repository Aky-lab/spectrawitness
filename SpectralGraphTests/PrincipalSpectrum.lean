import SpectralGraph.Inertia.PrincipalSpectrum
import SpectralGraph.Inertia.NegativeSpectrum
import SpectralGraph.Certificate.SpectralInterval

namespace SpectralGraphTests.PrincipalSpectrum

open Matrix SpectralGraph SpectralGraph.Certificate SpectralGraph.Inertia

/-! A diagonal matrix with a repeated eigenvalue, indexed in an order that is
not the descending spectral order. -/
def repeated : Matrix (Fin 4) (Fin 4) ℚ := Matrix.diagonal ![0, 1, 1, 2]

def atOne : InertiaCertificate (Fin 4) := ⟨1, 1, ⟨1, 2, 1⟩⟩

theorem repeatedHermitian : (ratCastMatrix repeated).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases hij : i = j <;> simp [ratCastMatrix, repeated, hij, eq_comm]

theorem repeatedEigenvalueOne :
    repeatedHermitian.eigenvalues₀ ⟨1, by decide⟩ = 1 := by
  have hi := atOne.sound (repeated - (1 : ℚ) • 1) (by decide +kernel)
  rw [ratCast_shift] at hi
  norm_num at hi
  have hp : (matrixInertia (ratCastMatrix repeated - (1 : ℝ) • 1)).pos = 1 := by
    simpa [atOne] using congrArg Inertia.pos hi
  have hn : (matrixInertia (ratCastMatrix repeated - (1 : ℝ) • 1)).neg = 1 := by
    simpa [atOne] using congrArg Inertia.neg hi
  have hnOne : (matrixInertia (ratCastMatrix repeated - 1)).neg = 1 := by
    simpa only [one_smul] using hn
  apply le_antisymm
  · apply (eigenvalues₀_le_iff _ repeatedHermitian 1 ⟨1, by decide⟩).mpr
    simpa using hp.le
  · apply (le_eigenvalues₀_iff _ repeatedHermitian 1 ⟨1, by decide⟩).mpr
    calc
      (matrixInertia (ratCastMatrix repeated - (1 : ℝ) • 1)).neg = 1 := hn
      _ < Fintype.card (Fin 4) - (⟨1, by decide⟩ : Fin 4).val := by decide

inductive Kept where
  | repeated
  | largest
  deriving DecidableEq, Fintype

def keptEmbedding : Kept ↪ Fin 4 where
  toFun
    | .repeated => 1
    | .largest => 3
  inj' := by
    intro x y h
    cases x <;> cases y <;> simp_all

def keptMatrix : Matrix Kept Kept ℚ := repeated.submatrix keptEmbedding keptEmbedding
def keptAtOne : InertiaCertificate Kept := ⟨1, 1, ⟨1, 1, 0⟩⟩

theorem keptHermitian : (ratCastMatrix keptMatrix).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  cases i <;> cases j <;>
    simp [keptMatrix, keptEmbedding, repeated, ratCastMatrix, Matrix.diagonal_apply]

theorem submatrixSecondEigenvalueOne :
    (repeatedHermitian.submatrix keptEmbedding).eigenvalues₀ ⟨1, by decide⟩ = 1 := by
  have hi := keptAtOne.sound (keptMatrix - (1 : ℚ) • 1) (by decide +kernel)
  rw [ratCast_shift] at hi
  norm_num at hi
  have hm : (ratCastMatrix repeated).submatrix keptEmbedding keptEmbedding =
      ratCastMatrix keptMatrix := by
    ext i j
    simp [keptMatrix, ratCastMatrix, Matrix.submatrix_apply]
  have hi' : matrixInertia
      ((ratCastMatrix repeated).submatrix keptEmbedding keptEmbedding - 1 • 1) =
      keptAtOne.target := by
    rw [hm]
    simpa using hi
  have hp : (matrixInertia
      ((ratCastMatrix repeated).submatrix keptEmbedding keptEmbedding -
        (1 : ℝ) • 1)).pos = 1 := by
    simpa [keptAtOne] using congrArg Inertia.pos hi'
  have hn : (matrixInertia
      ((ratCastMatrix repeated).submatrix keptEmbedding keptEmbedding -
        (1 : ℝ) • 1)).neg = 0 := by
    simpa [keptAtOne] using congrArg Inertia.neg hi'
  have hnOne : (matrixInertia
      ((ratCastMatrix repeated).submatrix keptEmbedding keptEmbedding - 1)).neg = 0 := by
    simpa only [one_smul] using hn
  apply le_antisymm
  · apply (eigenvalues₀_le_iff _ (repeatedHermitian.submatrix keptEmbedding)
      1 ⟨1, by decide⟩).mpr
    simpa using hp.le
  · apply (le_eigenvalues₀_iff _ (repeatedHermitian.submatrix keptEmbedding)
      1 ⟨1, by decide⟩).mpr
    calc
      (matrixInertia ((ratCastMatrix repeated).submatrix keptEmbedding keptEmbedding -
        (1 : ℝ) • 1)).neg = 0 := hn
      _ < Fintype.card Kept - (⟨1, by decide⟩ : Fin (Fintype.card Kept)).val := by decide

/-- A noncontiguous named embedding exercises both codimension-two bounds;
the upper bound is equality at the repeated eigenvalue. -/
theorem noncontiguous_cauchy_and_repeated_equality :
    repeatedHermitian.eigenvalues₀ ⟨3, by decide⟩ ≤
        (repeatedHermitian.submatrix keptEmbedding).eigenvalues₀ ⟨1, by decide⟩ ∧
      (repeatedHermitian.submatrix keptEmbedding).eigenvalues₀ ⟨1, by decide⟩ ≤
        repeatedHermitian.eigenvalues₀ ⟨1, by decide⟩ ∧
      (repeatedHermitian.submatrix keptEmbedding).eigenvalues₀ ⟨1, by decide⟩ =
        repeatedHermitian.eigenvalues₀ ⟨1, by decide⟩ := by
  have h := principalSubmatrix_eigenvalues₀_interlace
    (ratCastMatrix repeated) repeatedHermitian keptEmbedding 2 (by decide)
    ⟨1, by decide⟩
  exact ⟨h.1, h.2, submatrixSecondEigenvalueOne.trans repeatedEigenvalueOne.symm⟩

-- Codimension zero uses the same public interface.
example (k : Fin 4) :
    repeatedHermitian.eigenvalues₀ k ≤
        (repeatedHermitian.submatrix (Function.Embedding.refl (Fin 4))).eigenvalues₀ k ∧
      (repeatedHermitian.submatrix (Function.Embedding.refl (Fin 4))).eigenvalues₀ k ≤
        repeatedHermitian.eigenvalues₀ k := by
  simpa using principalSubmatrix_eigenvalues₀_interlace
    (ratCastMatrix repeated) repeatedHermitian (Function.Embedding.refl (Fin 4)) 0 (by simp) k

-- A genuine subtype embedding exercises codimension one.
example (k : Fin (Fintype.card {i : Fin 4 // i ≠ 0})) :=
    principalSpectrumInterlaces (ratCastMatrix repeated) repeatedHermitian
      (Function.Embedding.subtype fun i : Fin 4 => i ≠ 0) k

-- Empty retained sets are handled by the count interface; the indexed theorem
-- is correctly vacuous because no `Fin 0` value can be supplied.
def emptyEmbedding : Empty ↪ Fin 4 where
  toFun := isEmptyElim
  inj' x := isEmptyElim x

example (t : ℝ) :
    (matrixInertia (((ratCastMatrix repeated) - t • 1).submatrix
      emptyEmbedding emptyEmbedding)).pos ≤
      (matrixInertia ((ratCastMatrix repeated) - t • 1)).pos :=
  matrixInertia_submatrix_pos_le _ _

example (A : Matrix Empty Empty ℝ) : (matrixInertia A).pos = 0 := by
  have h := matrixInertia_order A
  change (matrixInertia A).pos + (matrixInertia A).zero +
    (matrixInertia A).neg = 0 at h
  omega

-- At size one there is no adjacent eigenvalue pair to index.
example (k : Fin 1) : ¬ k.val + 1 < 1 := by omega

#print axioms SpectralGraph.Inertia.eigenvalues₀_le_of_pos_le_add
#print axioms SpectralGraph.Inertia.principalSubmatrix_eigenvalues₀_interlace
#print axioms noncontiguous_cauchy_and_repeated_equality

end SpectralGraphTests.PrincipalSpectrum
