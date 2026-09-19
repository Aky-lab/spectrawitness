import SpectralGraph.Graph.Cut

namespace SpectralGraphTests.Cut

open Matrix SpectralGraph.Graph

def path3 : SimpleGraph (Fin 3) where
  Adj i j := (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
    (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)
  symm := by
    intro i j h
    rcases h with h | h | h | h
    · exact Or.inr (Or.inl ⟨h.2, h.1⟩)
    · exact Or.inl ⟨h.2, h.1⟩
    · exact Or.inr (Or.inr (Or.inr ⟨h.2, h.1⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩))
  loopless := by
    constructor
    intro i h
    rcases h with h | h | h | h <;> omega

instance : DecidableRel path3.Adj := by unfold path3; infer_instance

theorem empty_subset_energy :
    dotProduct (fun i : Bool => if i ∈ (∅ : Finset Bool) then (1 : ℝ) else 0)
      ((⊤ : SimpleGraph Bool).lapMatrix ℝ *ᵥ
        (fun i => if i ∈ (∅ : Finset Bool) then (1 : ℝ) else 0)) = 0 := by
  rw [lapMatrix_indicator_eq_card_interedges]
  norm_num [SimpleGraph.interedges, Rel.interedges]

theorem full_subset_energy :
    dotProduct (fun i : Bool => if i ∈ (Finset.univ : Finset Bool) then (1 : ℝ) else 0)
      ((⊤ : SimpleGraph Bool).lapMatrix ℝ *ᵥ
        (fun i => if i ∈ (Finset.univ : Finset Bool) then (1 : ℝ) else 0)) = 0 := by
  rw [lapMatrix_indicator_eq_card_interedges]
  norm_num [SimpleGraph.interedges, Rel.interedges]

theorem fin0_empty_energy :
    dotProduct (fun i : Fin 0 => if i ∈ (∅ : Finset (Fin 0)) then (1 : ℝ) else 0)
      ((⊥ : SimpleGraph (Fin 0)).lapMatrix ℝ *ᵥ
        (fun i => if i ∈ (∅ : Finset (Fin 0)) then (1 : ℝ) else 0)) = 0 := by
  rw [lapMatrix_indicator_eq_card_interedges]
  norm_num [SimpleGraph.interedges, Rel.interedges]

theorem edgeless_singleton_energy :
    dotProduct (fun i : Fin 1 => if i ∈ ({0} : Finset (Fin 1)) then (1 : ℝ) else 0)
      ((⊥ : SimpleGraph (Fin 1)).lapMatrix ℝ *ᵥ
        (fun i => if i ∈ ({0} : Finset (Fin 1)) then (1 : ℝ) else 0)) = 0 := by
  rw [lapMatrix_indicator_eq_card_interedges]
  norm_num [SimpleGraph.interedges, Rel.interedges]

theorem bool_one_edge_cut_once : ((⊤ : SimpleGraph Bool).interedges {true} ({true} : Finset Bool)ᶜ).card = 1 := by
  decide +kernel

theorem bool_one_edge_directed_crossings :
    ((⊤ : SimpleGraph Bool).interedges {true} ({true} : Finset Bool)ᶜ).card +
      ((⊤ : SimpleGraph Bool).interedges ({true} : Finset Bool)ᶜ {true}).card = 2 := by
  decide +kernel

theorem bool_one_edge_indicator_energy :
    dotProduct (fun i : Bool => if i ∈ ({true} : Finset Bool) then (1 : ℝ) else 0)
      ((⊤ : SimpleGraph Bool).lapMatrix ℝ *ᵥ
        (fun i => if i ∈ ({true} : Finset Bool) then (1 : ℝ) else 0)) = 1 := by
  rw [lapMatrix_indicator_eq_card_interedges]
  rw [bool_one_edge_cut_once]
  norm_num

theorem path3_noncontiguous_cut_once :
    (path3.interedges ({0, 2} : Finset (Fin 3)) ({0, 2} : Finset (Fin 3))ᶜ).card = 2 := by
  decide +kernel

theorem path3_noncontiguous_indicator_energy :
    dotProduct (fun i : Fin 3 => if i ∈ ({0, 2} : Finset (Fin 3)) then (1 : ℝ) else 0)
      (path3.lapMatrix ℝ *ᵥ (fun i => if i ∈ ({0, 2} : Finset (Fin 3)) then (1 : ℝ) else 0)) = 2 := by
  rw [lapMatrix_indicator_eq_card_interedges]
  rw [path3_noncontiguous_cut_once]
  norm_num

end SpectralGraphTests.Cut
