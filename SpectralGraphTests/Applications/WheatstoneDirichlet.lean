import SpectralGraph.Certificate.SchurDirichlet
import SpectralGraphTests.Dirichlet.BridgeCertificate

/-! Exact all-real Dirichlet response of a named unbalanced weighted bridge. -/

namespace SpectralGraphTests.Dirichlet
open Matrix SpectralGraph.Certificate

noncomputable def harmonic (a b : ℝ) : Fin 2 → ℝ := ![(5*a+6*b)/11, (4*a+7*b)/11]

private theorem harmonic_eq_checked (a b : ℝ) :
    harmonic a b = -(X.map (Rat.castHom ℝ) *ᵥ ![a,b]) := by
  ext i
  fin_cases i <;>
    simp [harmonic, X, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring

private theorem schur_energy_value (a b : ℝ) :
    dotProduct ![a,b] (ratCastMatrix S *ᵥ ![a,b]) =
      (13/11 : ℝ) * (a-b)^2 := by
  simp [S, ratCastMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

private theorem schur_current_value (a b : ℝ) :
    ratCastMatrix S *ᵥ ![a,b] =
      ![(13/11 : ℝ)*(a-b), -(13/11 : ℝ)*(a-b)] := by
  ext i
  fin_cases i <;>
    simp [S, ratCastMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring

/-- Every real interior competitor has energy at least the exact terminal power. -/
theorem bridge_energy_lower (a b p q : ℝ) :
    (13/11 : ℝ) * (a-b)^2 ≤
      dotProduct (Sum.elim ![p,q] ![a,b])
        (weightedBridge *ᵥ Sum.elim ![p,q] ![a,b]) := by
  rw [← real_block_binding, ← schur_energy_value]
  exact checkSchur_energy_min A Q B X D S schur_checked pivot_posDef ![a,b] ![p,q]

/-- The unique interior equality case for arbitrary real terminal voltages. -/
theorem bridge_energy_eq_iff (a b p q : ℝ) :
    dotProduct (Sum.elim ![p,q] ![a,b])
      (weightedBridge *ᵥ Sum.elim ![p,q] ![a,b]) =
      (13/11 : ℝ) * (a-b)^2 ↔ ![p,q] = harmonic a b := by
  rw [← real_block_binding, ← schur_energy_value, harmonic_eq_checked]
  exact checkSchur_energy_eq_iff A Q B X D S schur_checked pivot_posDef ![a,b] ![p,q]

theorem bridge_harmonic_attains (a b : ℝ) :
    dotProduct (Sum.elim (harmonic a b) ![a,b])
      (weightedBridge *ᵥ Sum.elim (harmonic a b) ![a,b]) =
      (13/11 : ℝ) * (a-b)^2 := by
  have h := (bridge_energy_eq_iff a b ((harmonic a b) 0) ((harmonic a b) 1)).2
  simpa [harmonic, Matrix.cons_val_zero, Matrix.cons_val_one] using h (by
    ext i
    fin_cases i <;> rfl)

/-- The full current has zero interior entries and opposite terminal entries. -/
theorem bridge_harmonic_current (a b : ℝ) :
    weightedBridge *ᵥ Sum.elim (harmonic a b) ![a,b] =
      Sum.elim ![0,0]
        ![(13/11 : ℝ)*(a-b), -(13/11 : ℝ)*(a-b)] := by
  rw [← real_block_binding, harmonic_eq_checked, ← schur_current_value]
  have hzero : (0 : Fin 2 → ℝ) = ![0,0] := by
    ext i
    fin_cases i <;> rfl
  simpa only [hzero] using
    checkSchur_harmonic_response A Q B X D S schur_checked ![a,b]

theorem unit_harmonic : harmonic 1 0 = ![(5/11 : ℝ), (4/11 : ℝ)] := by
  ext i
  fin_cases i <;> norm_num [harmonic]

theorem unit_energy_lower (p q : ℝ) :
    (13/11 : ℝ) ≤
      dotProduct (Sum.elim ![p,q] ![(1:ℝ),0])
        (weightedBridge *ᵥ Sum.elim ![p,q] ![(1:ℝ),0]) := by
  simpa using bridge_energy_lower 1 0 p q

theorem unit_energy_eq_iff (p q : ℝ) :
    dotProduct (Sum.elim ![p,q] ![(1:ℝ),0])
      (weightedBridge *ᵥ Sum.elim ![p,q] ![(1:ℝ),0]) =
      (13/11 : ℝ) ↔ ![p,q] = ![(5/11 : ℝ), (4/11 : ℝ)] := by
  simpa [unit_harmonic] using bridge_energy_eq_iff 1 0 p q

theorem unit_harmonic_current :
    weightedBridge *ᵥ Sum.elim ![(5/11 : ℝ),(4/11 : ℝ)] ![(1:ℝ),0] =
      Sum.elim ![0,0] ![(13/11 : ℝ),(-13/11 : ℝ)] := by
  simpa [unit_harmonic, neg_div] using bridge_harmonic_current 1 0

/-- The exact Dirichlet minimum over every real interior vector. -/
theorem unit_energy_isLeast :
    IsLeast {r : ℝ | ∃ x : Fin 2 → ℝ,
      dotProduct (Sum.elim x ![(1:ℝ),0])
        (weightedBridge *ᵥ Sum.elim x ![(1:ℝ),0]) = r} (13/11) := by
  constructor
  · refine ⟨![(5/11 : ℝ),(4/11 : ℝ)], ?_⟩
    simpa [unit_harmonic] using bridge_harmonic_attains 1 0
  · rintro r ⟨x, rfl⟩
    have hx : x = ![x 0, x 1] := by
      ext i
      fin_cases i <;> rfl
    rw [hx]
    exact unit_energy_lower (x 0) (x 1)

theorem equal_terminal_energy (a : ℝ) :
    dotProduct (Sum.elim (harmonic a a) ![a,a])
      (weightedBridge *ᵥ Sum.elim (harmonic a a) ![a,a]) = 0 := by
  simpa using bridge_harmonic_attains a a

theorem equal_terminal_current (a : ℝ) :
    weightedBridge *ᵥ Sum.elim (harmonic a a) ![a,a] = 0 := by
  have h := bridge_harmonic_current a a
  have hz : Sum.elim ![(0:ℝ),0] ![(13/11 : ℝ)*(a-a),
      -(13/11 : ℝ)*(a-a)] = (0 : V → ℝ) := by
    ext (i | i) <;> fin_cases i <;> simp
  exact h.trans hz

theorem equal_terminal_constant (a : ℝ) : harmonic a a = ![a,a] := by
  ext i
  fin_cases i <;> simp [harmonic] <;> ring

end SpectralGraphTests.Dirichlet
