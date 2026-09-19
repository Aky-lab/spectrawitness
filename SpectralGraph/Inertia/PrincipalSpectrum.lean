import SpectralGraph.Inertia.Restriction
import SpectralGraph.Inertia.SpectrumComparison

/-!
# Ordered Cauchy interlacing for principal submatrices

The public theorem carries the ambient `Fin` bounds and uses arbitrary finite
index types.  The codimension is explicit, while `principalSpectrumInterlaces`
computes it from the two cardinalities.
-/

namespace SpectralGraph.Inertia

variable {ι κ : Type*}
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [Fintype κ] in
/-- Restriction commutes with subtracting a scalar identity matrix. -/
theorem submatrix_sub_smul_one (A : Matrix ι ι ℝ) (e : κ ↪ ι) (t : ℝ) :
    (A - t • 1).submatrix e e = A.submatrix e e - t • 1 := by
  ext x y
  simp [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, e.injective.eq_iff]

/-- The ambient positive index is at most the restricted positive index plus
the codimension.  This is the second threshold-count inequality used by
Cauchy interlacing. -/
theorem matrixInertia_pos_le_submatrix_add_codim
    (A : Matrix ι ι ℝ) (e : κ ↪ ι) (d : Nat)
    (hcard : Fintype.card ι = Fintype.card κ + d) :
    (matrixInertia A).pos ≤ (matrixInertia (A.submatrix e e)).pos + d := by
  have hf : Function.Injective (coordinateEmbedding e) := by
    simpa [coordinateEmbedding, Function.ExtendByZero.linearMap] using
      Function.extend_injective e.injective (0 : ι → ℝ)
  have hcodim : Module.finrank ℝ (ι → ℝ) =
      Module.finrank ℝ (κ → ℝ) + d := by
    simpa [Module.finrank_fintype_fun_eq_card] using hcard
  have h := sigPos_le_comp_add_codim A.toQuadraticForm'
    (coordinateEmbedding e) hf d hcodim
  rw [← submatrix_toQuadraticForm'_eq_comp] at h
  exact h

/-- Ordered Cauchy interlacing for a principal submatrix of explicit
codimension `d`.  Both eigenvalue lists are descending and zero based. -/
theorem principalSubmatrix_eigenvalues₀_interlace
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (e : κ ↪ ι)
    (d : Nat) (hcard : Fintype.card ι = Fintype.card κ + d)
    (k : Fin (Fintype.card κ)) :
    hA.eigenvalues₀ ⟨k.val + d, by omega⟩ ≤
        (hA.submatrix e).eigenvalues₀ k ∧
      (hA.submatrix e).eigenvalues₀ k ≤
        hA.eigenvalues₀ ⟨k.val, by omega⟩ := by
  constructor
  · apply eigenvalues₀_le_of_pos_le_add A hA (A.submatrix e e)
      (hA.submatrix e) d ⟨k.val + d, by omega⟩ k (by rfl)
    intro t
    have h := matrixInertia_pos_le_submatrix_add_codim (A - t • 1) e d hcard
    rw [submatrix_sub_smul_one] at h
    exact h
  · apply eigenvalues₀_le_of_pos_le_add (A.submatrix e e) (hA.submatrix e)
      A hA 0 k ⟨k.val, by omega⟩ (by simp)
    intro t
    have h := matrixInertia_submatrix_pos_le (A - t • 1) e
    rw [submatrix_sub_smul_one] at h
    simpa using h

/-- Convenience form of Cauchy interlacing that computes the codimension from
the embedding. -/
theorem principalSpectrumInterlaces
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (e : κ ↪ ι)
    (k : Fin (Fintype.card κ)) :
    hA.eigenvalues₀
        ⟨k.val + (Fintype.card ι - Fintype.card κ), by
          have hle := Fintype.card_le_of_injective e e.injective
          omega⟩ ≤ (hA.submatrix e).eigenvalues₀ k ∧
      (hA.submatrix e).eigenvalues₀ k ≤
        hA.eigenvalues₀ ⟨k.val, by
          have hle := Fintype.card_le_of_injective e e.injective
          omega⟩ := by
  have hle := Fintype.card_le_of_injective e e.injective
  apply principalSubmatrix_eigenvalues₀_interlace A hA e
    (Fintype.card ι - Fintype.card κ) (by omega) k

/-- Codimension-one specialization; consumers only provide the retained
index. -/
theorem principalSubmatrix_eigenvalues₀_interlace_one
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (e : κ ↪ ι)
    (hcard : Fintype.card ι = Fintype.card κ + 1)
    (k : Fin (Fintype.card κ)) :
    hA.eigenvalues₀ ⟨k.val + 1, by omega⟩ ≤
        (hA.submatrix e).eigenvalues₀ k ∧
      (hA.submatrix e).eigenvalues₀ k ≤
        hA.eigenvalues₀ ⟨k.val, by omega⟩ :=
  principalSubmatrix_eigenvalues₀_interlace A hA e 1 hcard k

end SpectralGraph.Inertia
