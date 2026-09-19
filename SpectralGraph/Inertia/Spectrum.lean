import SpectralGraph.Inertia.Diagonal
import SpectralGraph.Inertia.Congruence
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Inertia counts real eigenvalues

This module identifies quadratic-form inertia with the signs of mathlib's
Hermitian eigenvalues, counted with multiplicity. At any real threshold,
shifted inertia counts eigenvalues above, at, and below that threshold.
-/

namespace SpectralGraph.Inertia
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The spectral basis gives a real congruence diagonalization. -/
theorem eigenvector_congruence (A : Matrix ι ι ℝ) (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix ι ι ℝ).transpose * A *
      (hA.eigenvectorUnitary : Matrix ι ι ℝ) = Matrix.diagonal hA.eigenvalues := by
  simpa [Unitary.conjStarAlgAut_star_apply] using hA.conjStarAlgAut_star_eigenvectorUnitary

/-- Semantic inertia is the eigenvalue sign count, including multiplicity. -/
theorem matrixInertia_eq_eigenvalue_counts (A : Matrix ι ι ℝ) (hA : A.IsHermitian) :
    matrixInertia A =
      { pos := (Finset.univ.filter fun i ↦ 0 < hA.eigenvalues i).card
        zero := (Finset.univ.filter fun i ↦ hA.eigenvalues i = 0).card
        neg := (Finset.univ.filter fun i ↦ hA.eigenvalues i < 0).card } := by
  let U : Matrix ι ι ℝ := hA.eigenvectorUnitary
  have hu : U.transpose * U = 1 := by
    simpa only [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using Unitary.coe_star_mul_self hA.eigenvectorUnitary
  letI : Invertible U := invertibleOfLeftInverse U U.transpose hu
  rw [matrixInertia_eq_of_congr A (Matrix.diagonal hA.eigenvalues) U
    (eigenvector_congruence A hA).symm]
  exact SpectralGraph.matrixInertia_diagonal _

/-- Congruence in the eigenbasis commutes with a scalar shift. -/
theorem eigenvector_congruence_shift (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (t : ℝ) :
    (hA.eigenvectorUnitary : Matrix ι ι ℝ).transpose * (A - t • 1) *
      (hA.eigenvectorUnitary : Matrix ι ι ℝ) =
        Matrix.diagonal (fun i ↦ hA.eigenvalues i - t) := by
  have hu : (hA.eigenvectorUnitary : Matrix ι ι ℝ).transpose *
      (hA.eigenvectorUnitary : Matrix ι ι ℝ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using Unitary.coe_star_mul_self hA.eigenvectorUnitary
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, hu, eigenvector_congruence A hA]
  ext i j
  by_cases hij : i = j <;> simp [hij]

/-- Shifted inertia counts eigenvalues relative to any real threshold.
No eigenvalue shift/reordering convention is needed: the counts refer to the
original matrix's eigenvalues, with their multiplicities. -/
theorem matrixInertia_shift_eq_eigenvalue_counts
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (t : ℝ) :
    matrixInertia (A - t • 1) =
      { pos := (Finset.univ.filter fun i ↦ t < hA.eigenvalues i).card
        zero := (Finset.univ.filter fun i ↦ hA.eigenvalues i = t).card
        neg := (Finset.univ.filter fun i ↦ hA.eigenvalues i < t).card } := by
  let U : Matrix ι ι ℝ := hA.eigenvectorUnitary
  have hu : U.transpose * U = 1 := by
    simpa only [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using Unitary.coe_star_mul_self hA.eigenvectorUnitary
  letI : Invertible U := invertibleOfLeftInverse U U.transpose hu
  rw [matrixInertia_eq_of_congr (A - t • 1)
    (Matrix.diagonal (fun i ↦ hA.eigenvalues i - t)) U
    (eigenvector_congruence_shift A hA t).symm, SpectralGraph.matrixInertia_diagonal]
  simp only [sub_pos, sub_eq_zero, sub_neg]

/-- Eigenvalues in `(a,b]` can be counted using two shifted inertia computations.
The additive form avoids truncated natural subtraction and makes endpoint
conventions explicit, even when eigenvalues equal either endpoint. -/
theorem eigenvalue_count_Ioc_add_pos_eq (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (a b : ℝ) (hab : a ≤ b) :
    (Finset.univ.filter fun i ↦ a < hA.eigenvalues i ∧ hA.eigenvalues i ≤ b).card +
      (matrixInertia (A - b • 1)).pos = (matrixInertia (A - a • 1)).pos := by
  classical
  rw [matrixInertia_shift_eq_eigenvalue_counts A hA b,
    matrixInertia_shift_eq_eigenvalue_counts A hA a]
  change _ + (Finset.univ.filter fun i ↦ b < hA.eigenvalues i).card = _
  have hs := (Finset.univ.filter fun i ↦ a < hA.eigenvalues i).card_filter_add_card_filter_not
    (fun i ↦ hA.eigenvalues i ≤ b)
  have he : ((Finset.univ.filter fun i ↦ a < hA.eigenvalues i).filter
      fun i ↦ ¬hA.eigenvalues i ≤ b) = Finset.univ.filter (fun i ↦ b < hA.eigenvalues i) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨lt_of_le_of_lt hab h, h⟩⟩
  rw [he] at hs
  simpa only [Finset.filter_filter] using hs

/-- Subtraction form of interval counting, useful for an executable target. -/
theorem eigenvalue_count_Ioc_eq (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (a b : ℝ) (hab : a ≤ b) :
    (Finset.univ.filter fun i ↦ a < hA.eigenvalues i ∧ hA.eigenvalues i ≤ b).card =
      (matrixInertia (A - a • 1)).pos - (matrixInertia (A - b • 1)).pos := by
  have h := eigenvalue_count_Ioc_add_pos_eq A hA a b hab
  omega

end SpectralGraph.Inertia
