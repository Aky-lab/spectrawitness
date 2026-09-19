import SpectralGraph.Inertia.OrderedSpectrum

/-!
# Eigenpairs from invariant matrix subspaces

An injective matrix map carries an eigenpair of a matrix describing an
invariant subspace to an eigenpair of the ambient matrix.  The smaller matrix
need not be symmetric.  Hermitian structure is needed only to identify the
lifted eigenvalue in the ambient ordered spectrum.
-/

namespace SpectralGraph.Inertia

open Matrix

variable {V C : Type*}
variable [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

omit [Fintype V] [DecidableEq V] [DecidableEq C] in
/-- A nonzero vector remains nonzero after multiplication by an injective
matrix map. -/
theorem mulVec_ne_zero_of_injective (U : Matrix V C ℝ)
    (hU : Function.Injective U.mulVecLin) (x : C → ℝ) (hx : x ≠ 0) :
    U *ᵥ x ≠ 0 := by
  intro hzero
  apply hx
  apply hU
  simpa only [Matrix.mulVecLin_apply, LinearMap.map_zero] using hzero

omit [DecidableEq V] [DecidableEq C] in
/-- An injective matrix map carries an eigenpair of a matrix describing an
invariant subspace to an eigenpair of the ambient matrix. -/
theorem lift_invariant_eigenpair (A : Matrix V V ℝ) (U : Matrix V C ℝ)
    (Q : Matrix C C ℝ) (hU : Function.Injective U.mulVecLin)
    (hAU : A * U = U * Q) (t : ℝ) (x : C → ℝ) (hx : x ≠ 0)
    (hQx : Q *ᵥ x = t • x) :
    U *ᵥ x ≠ 0 ∧ A *ᵥ (U *ᵥ x) = t • (U *ᵥ x) := by
  refine ⟨mulVec_ne_zero_of_injective U hU x hx, ?_⟩
  rw [Matrix.mulVec_mulVec, hAU, ← Matrix.mulVec_mulVec, hQx,
    Matrix.mulVec_smul]

/-- A real eigenpair of a Hermitian matrix occurs in its descending ordered
eigenvalue list. -/
theorem eigenvalues₀_eq_of_eigenpair (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (t : ℝ) (y : V → ℝ) (hy : y ≠ 0) (hAy : A *ᵥ y = t • y) :
    ∃ k : Fin (Fintype.card V), hA.eigenvalues₀ k = t := by
  have hv : Module.End.HasEigenvector A.toLin' t y :=
    ⟨Module.End.mem_eigenspace_iff.mpr hAy, hy⟩
  have hs := (Module.End.hasEigenvalue_of_hasEigenvector hv).mem_spectrum
  rw [Matrix.spectrum_toLin', hA.spectrum_real_eq_range_eigenvalues] at hs
  obtain ⟨v, hv⟩ := hs
  let e : Fin (Fintype.card V) ≃ V :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  refine ⟨e.symm v, ?_⟩
  simpa [Matrix.IsHermitian.eigenvalues, e] using hv

omit [DecidableEq C] in
/-- An eigenpair of a matrix describing an injectively represented invariant
subspace occurs in the ordered spectrum of a Hermitian ambient matrix. -/
theorem eigenvalues₀_eq_of_invariant_eigenpair
    (A : Matrix V V ℝ) (hA : A.IsHermitian) (U : Matrix V C ℝ)
    (Q : Matrix C C ℝ) (hU : Function.Injective U.mulVecLin)
    (hAU : A * U = U * Q) (t : ℝ) (x : C → ℝ) (hx : x ≠ 0)
    (hQx : Q *ᵥ x = t • x) :
    ∃ k : Fin (Fintype.card V), hA.eigenvalues₀ k = t := by
  obtain ⟨hUx, hAUx⟩ := lift_invariant_eigenpair A U Q hU hAU t x hx hQx
  exact eigenvalues₀_eq_of_eigenpair A hA t (U *ᵥ x) hUx hAUx

end SpectralGraph.Inertia
