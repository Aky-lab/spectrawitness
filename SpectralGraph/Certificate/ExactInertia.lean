import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import SpectralGraph.Inertia.Congruence
import SpectralGraph.Inertia.Diagonal

/-!
# Exact rational inertia certificates

An external producer supplies a rational congruence. Exact determinant or
left-inverse and diagonality checks certify semantic real inertia.
-/

namespace SpectralGraph
namespace Certificate

open QuadraticForm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The inertia obtained by counting the signs of rational diagonal entries. -/
def rationalDiagonalInertia (w : ι → ℚ) : Inertia where
  pos := (Finset.univ.filter fun i ↦ 0 < w i).card
  zero := (Finset.univ.filter fun i ↦ w i = 0).card
  neg := (Finset.univ.filter fun i ↦ w i < 0).card

/-- A rational matrix, interpreted exactly as a real matrix. -/
noncomputable def ratCastMatrix (A : Matrix ι ι ℚ) : Matrix ι ι ℝ :=
  A.map (Rat.castHom ℝ)

/-- Compatibility name for the diagonal theorem, now in the semantic layer. -/
alias matrixInertia_diagonal := SpectralGraph.matrixInertia_diagonal

/-- Casting a rational diagonal matrix to the reals preserves its exact
sign-counting inertia. -/
theorem matrixInertia_ratCast_diagonal (w : ι → ℚ) :
    matrixInertia (Matrix.diagonal fun i ↦ (w i : ℝ)) =
      rationalDiagonalInertia w := by
  rw [matrixInertia_diagonal]
  unfold rationalDiagonalInertia
  have hp : (Finset.univ.filter fun i ↦ 0 < ((w i : ℚ) : ℝ)) =
      Finset.univ.filter fun i ↦ 0 < w i := by
    ext i
    simp
  have hz : (Finset.univ.filter fun i ↦ ((w i : ℚ) : ℝ) = 0) =
      Finset.univ.filter fun i ↦ w i = 0 := by
    ext i
    simp
  have hn : (Finset.univ.filter fun i ↦ ((w i : ℚ) : ℝ) < 0) =
      Finset.univ.filter fun i ↦ w i < 0 := by
    ext i
    simp
  rw [hp, hz, hn]

/-- Exact, decidable conditions under which `P` certifies the inertia of `A`.

The checker does not assume that the external generator performed valid
elimination: every matrix multiplication and every rational equality below
is recomputed by Lean. -/
def CertifiesInertia (A P : Matrix ι ι ℚ) (target : Inertia) : Prop :=
  P.det ≠ 0 ∧
    let D := P.transpose * A * P
    (∀ i j, i ≠ j → D i j = 0) ∧
      rationalDiagonalInertia (fun i ↦ D i i) = target

/-- A faster certificate format for large searches.  Supplying an alleged
inverse avoids expanding a determinant for every candidate; Lean instead
checks the cubic-size identity `Pinv * P = 1`. -/
def CertifiesInertiaWithInverse
    (A P Pinv : Matrix ι ι ℚ) (target : Inertia) : Prop :=
  Pinv * P = 1 ∧
    let D := P.transpose * A * P
    (∀ i j, i ≠ j → D i j = 0) ∧
      rationalDiagonalInertia (fun i ↦ D i i) = target

/-- A successful exact rational diagonalization certificate proves the
semantic inertia of the corresponding real matrix. -/
theorem matrixInertia_eq_of_certifiesInertia
    (A P : Matrix ι ι ℚ) (target : Inertia)
    (hcert : CertifiesInertia A P target) :
    matrixInertia (ratCastMatrix A) = target := by
  rcases hcert with ⟨hdet, hdiag, htarget⟩
  let D : Matrix ι ι ℚ := P.transpose * A * P
  let AR : Matrix ι ι ℝ := ratCastMatrix A
  let PR : Matrix ι ι ℝ := ratCastMatrix P
  let DR : Matrix ι ι ℝ := ratCastMatrix D
  have hdetR : PR.det ≠ 0 := by
    dsimp [PR, ratCastMatrix]
    rw [← Rat.cast_det]
    exact_mod_cast hdet
  letI : Invertible PR :=
    Matrix.invertibleOfIsUnitDet PR (isUnit_iff_ne_zero.mpr hdetR)
  have hcongr : DR = PR.transpose * AR * PR := by
    dsimp [DR, PR, AR, D, ratCastMatrix]
    calc
      (P.transpose * A * P).map (Rat.castHom ℝ) =
          (P.transpose * A).map (Rat.castHom ℝ) *
            P.map (Rat.castHom ℝ) := Matrix.map_mul
      _ = (P.transpose.map (Rat.castHom ℝ) *
            A.map (Rat.castHom ℝ)) * P.map (Rat.castHom ℝ) := by
          rw [Matrix.map_mul]
      _ = (P.map (Rat.castHom ℝ)).transpose *
            A.map (Rat.castHom ℝ) * P.map (Rat.castHom ℝ) := by
          rw [Matrix.transpose_map]
  have hdiagD : ∀ i j, i ≠ j → D i j = 0 := by
    simpa [D] using hdiag
  have hDdiag : D = Matrix.diagonal (fun i ↦ D i i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · rw [hdiagD i j hij]
      simp [hij]
  have hDRdiag : DR = Matrix.diagonal (fun i ↦ ((D i i : ℚ) : ℝ)) := by
    calc
      DR = D.map (Rat.castHom ℝ) := rfl
      _ = (Matrix.diagonal fun i ↦ D i i).map (Rat.castHom ℝ) :=
        congrArg (fun M ↦ M.map (Rat.castHom ℝ)) hDdiag
      _ = Matrix.diagonal (fun i ↦ ((D i i : ℚ) : ℝ)) := by
        simp
  calc
    matrixInertia AR = matrixInertia DR :=
      matrixInertia_eq_of_congr AR DR PR hcongr
    _ = matrixInertia (Matrix.diagonal fun i ↦ ((D i i : ℚ) : ℝ)) := by
      rw [hDRdiag]
    _ = rationalDiagonalInertia (fun i ↦ D i i) :=
      matrixInertia_ratCast_diagonal _
    _ = target := htarget

/-- Soundness of the inverse-carrying certificate format. -/
theorem matrixInertia_eq_of_certifiesInertiaWithInverse
    (A P Pinv : Matrix ι ι ℚ) (target : Inertia)
    (hcert : CertifiesInertiaWithInverse A P Pinv target) :
    matrixInertia (ratCastMatrix A) = target := by
  rcases hcert with ⟨hinv, hdiag, htarget⟩
  let D : Matrix ι ι ℚ := P.transpose * A * P
  let AR : Matrix ι ι ℝ := ratCastMatrix A
  let PR : Matrix ι ι ℝ := ratCastMatrix P
  let QR : Matrix ι ι ℝ := ratCastMatrix Pinv
  let DR : Matrix ι ι ℝ := ratCastMatrix D
  have hinvR : QR * PR = 1 := by
    dsimp [QR, PR, ratCastMatrix]
    calc
      Pinv.map (Rat.castHom ℝ) * P.map (Rat.castHom ℝ) =
          (Pinv * P).map (Rat.castHom ℝ) := Matrix.map_mul.symm
      _ = (1 : Matrix ι ι ℚ).map (Rat.castHom ℝ) := by rw [hinv]
      _ = 1 := by simp
  letI : Invertible PR := invertibleOfLeftInverse PR QR hinvR
  have hcongr : DR = PR.transpose * AR * PR := by
    dsimp [DR, PR, AR, D, ratCastMatrix]
    calc
      (P.transpose * A * P).map (Rat.castHom ℝ) =
          (P.transpose * A).map (Rat.castHom ℝ) *
            P.map (Rat.castHom ℝ) := Matrix.map_mul
      _ = (P.transpose.map (Rat.castHom ℝ) *
            A.map (Rat.castHom ℝ)) * P.map (Rat.castHom ℝ) := by
          rw [Matrix.map_mul]
      _ = (P.map (Rat.castHom ℝ)).transpose *
            A.map (Rat.castHom ℝ) * P.map (Rat.castHom ℝ) := by
          rw [Matrix.transpose_map]
  have hdiagD : ∀ i j, i ≠ j → D i j = 0 := by
    simpa [D] using hdiag
  have hDdiag : D = Matrix.diagonal (fun i ↦ D i i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · rw [hdiagD i j hij]
      simp [hij]
  have hDRdiag : DR = Matrix.diagonal (fun i ↦ ((D i i : ℚ) : ℝ)) := by
    calc
      DR = D.map (Rat.castHom ℝ) := rfl
      _ = (Matrix.diagonal fun i ↦ D i i).map (Rat.castHom ℝ) :=
        congrArg (fun M ↦ M.map (Rat.castHom ℝ)) hDdiag
      _ = Matrix.diagonal (fun i ↦ ((D i i : ℚ) : ℝ)) := by
        simp
  calc
    matrixInertia AR = matrixInertia DR :=
      matrixInertia_eq_of_congr AR DR PR hcongr
    _ = matrixInertia (Matrix.diagonal fun i ↦ ((D i i : ℚ) : ℝ)) := by
      rw [hDRdiag]
    _ = rationalDiagonalInertia (fun i ↦ D i i) :=
      matrixInertia_ratCast_diagonal _
    _ = target := htarget

end Certificate
end SpectralGraph
