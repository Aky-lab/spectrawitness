import SpectralGraph.Graph.SpectralCut
import SpectralGraphTests.Cuts.PrismCertificate

/-! A sharp certified bisection of the triangular prism. -/

namespace SpectralGraphTests.Cuts

open SpectralGraph.Graph

/-- The single exact inertia certificate bounds every balanced prism cut. -/
theorem prism_balanced_cut_lower (s : Finset (Fin 6)) (hs : s.card = 3) :
    3 ≤ (prism.interedges s sᶜ).card := by
  have h := gap_mul_card_mul_compl_le_card_mul_cut_of_inertia
    prism 2 prism_centered_two_neg_zero s
  rw [hs] at h
  norm_num at h
  have hreal : (3 : ℝ) ≤ ((prism.interedges s sᶜ).card : ℝ) := by
    linarith
  exact_mod_cast hreal

/-- Three edges are the minimum over all three-vertex subsets. -/
theorem prism_bisection_isLeast :
    IsLeast {k : ℕ | ∃ s : Finset (Fin 6), s.card = 3 ∧
      (prism.interedges s sᶜ).card = k} 3 := by
  refine ⟨⟨face, face_card, face_cut_card⟩, ?_⟩
  intro k hk
  obtain ⟨s, hs, hcut⟩ := hk
  rw [← hcut]
  exact prism_balanced_cut_lower s hs

theorem face_compl_card : faceᶜ.card = 3 := by decide +kernel

/-- Reversing the face has the same once-counted crossing cut. -/
theorem face_compl_cut_card : (prism.interedges faceᶜ face).card = 3 := by
  have h := Rel.card_interedges_comm prism.symm face faceᶜ
  change (prism.interedges face faceᶜ).card =
    (prism.interedges faceᶜ face).card at h
  rw [face_cut_card] at h
  exact h.symm

theorem face_compl_balanced_cut_card :
    (prism.interedges faceᶜ (faceᶜ)ᶜ).card = 3 := by
  simpa using face_compl_cut_card

end SpectralGraphTests.Cuts
