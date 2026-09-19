import SpectralGraph.Inertia.OrderedSpectrum

/-!
# Comparing ordered spectra from shifted inertia

This module converts a uniform comparison of positive inertia counts into a
comparison of mathlib's descending, zero-based `eigenvalues₀` lists.
-/

namespace SpectralGraph.Inertia

variable {ι κ : Type*}
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- If every shifted positive count for `A` is bounded by the corresponding
count for `B`, up to `d` extra directions, then the appropriately offset
eigenvalue of `A` is at most the chosen eigenvalue of `B`.

The eigenvalue lists are descending and zero based.  No strictness or
simplicity hypothesis is needed, so repeated eigenvalues are preserved. -/
theorem eigenvalues₀_le_of_pos_le_add
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (B : Matrix κ κ ℝ) (hB : B.IsHermitian)
    (d : Nat) (i : Fin (Fintype.card ι)) (j : Fin (Fintype.card κ))
    (hij : j.val + d ≤ i.val)
    (hcount : ∀ t : ℝ, (matrixInertia (A - t • 1)).pos ≤
      (matrixInertia (B - t • 1)).pos + d) :
    hA.eigenvalues₀ i ≤ hB.eigenvalues₀ j := by
  by_contra hnot
  have hAi := (lt_eigenvalues₀_iff A hA (hB.eigenvalues₀ j) i).mp
    (lt_of_not_ge hnot)
  have hBj := (eigenvalues₀_le_iff B hB (hB.eigenvalues₀ j) j).mp le_rfl
  have h := hcount (hB.eigenvalues₀ j)
  omega

end SpectralGraph.Inertia
