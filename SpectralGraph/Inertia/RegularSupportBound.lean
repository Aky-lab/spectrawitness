import SpectralGraph.Inertia.PosSemidefinite

/-!
# Constant-row-sum bounds from positive semidefiniteness

This is the division-free matrix core of the regular-graph Hoffman bound.
-/

namespace SpectralGraph.Inertia

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A zero principal block in a symmetric constant-row-sum matrix is bounded
by any negative shift making the matrix positive semidefinite. -/
theorem card_mul_sub_le_of_zero_principal_of_posSemidef
    (A : Matrix V V ℝ) (hA : A.IsSymm) (d τ : ℝ)
    (hrow : A *ᵥ (fun _ => 1) = d • (fun _ => 1))
    (hτ : τ < 0) (hpsd : (A - τ • 1).PosSemidef)
    (s : Finset V) (hzero : ∀ i ∈ s, ∀ j ∈ s, A i j = 0) :
    (d - τ) * (s.card : ℝ) ≤ (-τ) * (Fintype.card V : ℝ) := by
  classical
  let x : V → ℝ := fun i => if i ∈ s then 1 else 0
  let n : ℝ := Fintype.card V
  let k : ℝ := s.card
  have hxsum : ∑ i, x i = k := by
    simp [x, k, Finset.sum_ite_mem]
  have hxone : dotProduct x (fun _ => 1) = k := by
    simpa [dotProduct] using hxsum
  have honex : dotProduct (fun _ => 1) x = k := by
    simpa [dotProduct, mul_comm] using hxsum
  have honesum : ∑ i : V, (1 : ℝ) = n := by
    simp [n]
  have honeone : dotProduct (fun _ : V => 1) (fun _ : V => 1) = n := by
    simpa [dotProduct] using honesum
  have hxx : dotProduct x (A *ᵥ x) = 0 := by
    simp only [dotProduct, Matrix.mulVec, x]
    simp_rw [show ∀ i : V, (if i ∈ s then (1 : ℝ) else 0) *
        (∑ j, A i j * if j ∈ s then (1 : ℝ) else 0) =
        if i ∈ s then ∑ j, A i j * if j ∈ s then (1 : ℝ) else 0 else 0 by
      intro i
      split <;> simp]
    rw [Finset.sum_ite_mem]
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_univ, Finset.mem_inter, true_and] at hi
    simp_rw [show ∀ j : V, A i j * (if j ∈ s then (1 : ℝ) else 0) =
        if j ∈ s then A i j else 0 by
      intro j
      split <;> simp]
    rw [Finset.sum_ite_mem]
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_univ, Finset.mem_inter, true_and] at hj
    rw [hzero i hi j hj]
  have hxxnorm : dotProduct x x = k := by
    simp [dotProduct, x, k, Finset.sum_ite_mem]
  have hxAone : dotProduct x (A *ᵥ (fun _ => 1)) = d * k := by
    rw [hrow]
    rw [dotProduct_smul, hxone]
    simp only [smul_eq_mul]
  have honeAx : dotProduct (fun _ => 1) (A *ᵥ x) = d * k := by
    rw [Matrix.dotProduct_mulVec, ← hA.eq, Matrix.vecMul_transpose, dotProduct_comm]
    simpa [dotProduct_comm] using hxAone
  have honeAone : dotProduct (fun _ => 1) (A *ᵥ (fun _ => 1)) = d * n := by
    rw [hrow]
    rw [dotProduct_smul, honeone]
    simp only [smul_eq_mul]
  let y : V → ℝ := n • x - k • (fun _ => 1)
  have hy : 0 ≤ dotProduct y ((A - τ • 1) *ᵥ y) := by
    simpa only [star_trivial] using hpsd.dotProduct_mulVec_nonneg y
  have hyformula : dotProduct y ((A - τ • 1) *ᵥ y) =
      n * k * ((-τ) * n - (d - τ) * k) := by
    simp only [y, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub, dotProduct_smul,
      smul_dotProduct]
    rw [hxx, hxxnorm, hxAone, honeAx, honeAone, hxone, honex, honeone]
    ring
  rw [hyformula] at hy
  change (d - τ) * k ≤ (-τ) * n
  by_cases hs : s.card = 0
  · have hn0 : 0 ≤ n := by
      dsimp [n]
      positivity
    simp only [k, hs, Nat.cast_zero, mul_zero]
    nlinarith
  have hsn : s.Nonempty := Finset.card_ne_zero.mp hs
  have hk : 0 < k := by
    dsimp [k]
    exact_mod_cast Finset.card_pos.mpr hsn
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨hsn.choose⟩
  have hbr : 0 ≤ (-τ) * n - (d - τ) * k := by
    by_contra h
    have hneg : (-τ) * n - (d - τ) * k < 0 := lt_of_not_ge h
    have hprod : n * k * ((-τ) * n - (d - τ) * k) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hn hk) hneg
    linarith
  nlinarith

end SpectralGraph.Inertia
