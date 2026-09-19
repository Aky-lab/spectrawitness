import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

namespace SpectralGraph.Graph

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem lapMatrix_indicator_eq_card_interedges
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) :
    dotProduct (fun i => if i ∈ s then (1 : ℝ) else 0)
      (G.lapMatrix ℝ *ᵥ (fun i => if i ∈ s then (1 : ℝ) else 0)) =
        ((G.interedges s sᶜ).card : ℝ) := by
  classical
  let x : V → ℝ := fun i => if i ∈ s then 1 else 0
  have hpoint (i j : V) :
      (if G.Adj i j then (x i - x j) ^ 2 else 0) =
        (if (i, j) ∈ G.interedges s sᶜ then 1 else 0) +
          (if (i, j) ∈ G.interedges sᶜ s then 1 else 0) := by
    by_cases hi : i ∈ s <;> by_cases hj : j ∈ s <;>
      simp [x, hi, hj, SimpleGraph.mem_interedges_iff]
  have hcard (t : Finset (V × V)) :
      (∑ i : V, ∑ j : V, if (i, j) ∈ t then (1 : ℝ) else 0) = t.card := by
    let f : V × V → ℝ := fun p => if p ∈ t then 1 else 0
    change (∑ i : V, ∑ j : V, f (i, j)) = t.card
    rw [← Fintype.sum_prod_type]
    rw [← Finset.sum_filter]
    simp
  change dotProduct x (G.lapMatrix ℝ *ᵥ x) = _
  rw [← Matrix.toLinearMap₂'_apply' (G.lapMatrix ℝ) x]
  rw [G.lapMatrix_toLinearMap₂' ℝ x]
  simp_rw [hpoint]
  simp_rw [Finset.sum_add_distrib]
  rw [hcard]
  rw [hcard]
  have hcomm : (G.interedges s sᶜ).card = (G.interedges sᶜ s).card := by
    exact Rel.card_interedges_comm G.symm s sᶜ
  rw [← hcomm]
  norm_num

end SpectralGraph.Graph
