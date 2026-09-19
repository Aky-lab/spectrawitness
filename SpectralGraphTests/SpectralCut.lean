import SpectralGraph.Graph.SpectralCut
import SpectralGraphTests.Cut
import SpectralGraphTests.Applications.PrismBisection
import SpectralGraph.Certificate.IntegerCheck

/-! Boundary and strict-failure checks for certified cuts. -/

namespace SpectralGraphTests.SpectralCut

open SpectralGraph SpectralGraph.Inertia SpectralGraph.Graph
open SpectralGraph.Certificate SpectralGraphTests.Cuts
open Matrix

set_option maxHeartbeats 1600000

theorem empty_negative_matrix_variance (x : Fin 0 → ℝ) :
    (-1 : ℝ) * ((Fintype.card (Fin 0) : ℝ) * dotProduct x x -
      (∑ i, x i)^2) ≤
      (Fintype.card (Fin 0) : ℝ) *
        dotProduct x ((0 : Matrix (Fin 0) (Fin 0) ℝ) *ᵥ x) := by
  have hzero : centeredShift (0 : Matrix (Fin 0) (Fin 0) ℝ) (-1) = 0 := by
    ext i
    exact Fin.elim0 i
  have hpsd : (centeredShift (0 : Matrix (Fin 0) (Fin 0) ℝ) (-1)).PosSemidef := by
    rw [hzero]
    exact Matrix.PosSemidef.zero
  exact variance_le_of_centeredShift_posSemidef _ _ hpsd x

def emptyInput : DenseIntMatrix := DenseIntMatrix.ofFn 0 fun _ _ => 0

theorem empty_checked : emptyInput.checkInertia ⟨0, 0, 0⟩ = true := by
  decide +kernel

theorem empty_binding : ratCastMatrix emptyInput.toRatMatrix =
    centeredShift ((⊥ : SimpleGraph (Fin 0)).lapMatrix ℝ) 0 := by
  ext i
  exact Fin.elim0 i

theorem empty_graph_neg_zero :
    (matrixInertia (centeredShift ((⊥ : SimpleGraph (Fin 0)).lapMatrix ℝ) 0)).neg = 0 := by
  have h := DenseIntMatrix.checkInertia_sound emptyInput ⟨0, 0, 0⟩ empty_checked
  rw [empty_binding] at h
  exact congrArg Inertia.neg h

theorem empty_graph_cut_bound :
    (0 : ℝ) * (0 : ℝ) * (0 - 0) ≤
      0 * (((⊥ : SimpleGraph (Fin 0)).interedges ∅ (∅ : Finset (Fin 0))ᶜ).card : ℝ) := by
  simpa using gap_mul_card_mul_compl_le_card_mul_cut_of_inertia
    (⊥ : SimpleGraph (Fin 0)) 0 empty_graph_neg_zero ∅

def singletonInput : DenseIntMatrix := DenseIntMatrix.ofFn 1 fun _ _ => 0

theorem singleton_checked : singletonInput.checkInertia ⟨0, 1, 0⟩ = true := by
  decide +kernel

theorem singleton_binding (γ : ℝ) : ratCastMatrix singletonInput.toRatMatrix =
    centeredShift ((⊥ : SimpleGraph (Fin 1)).lapMatrix ℝ) γ := by
  have hone (i j : Fin 1) : (1 : Matrix (Fin 1) (Fin 1) ℝ) i j = 1 := by
    have hij : i = j := Subsingleton.elim i j
    subst j
    exact Matrix.one_apply_eq i
  ext i j
  fin_cases i
  fin_cases j
  simp [ratCastMatrix, singletonInput, DenseIntMatrix.toRatMatrix,
    centeredShift, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
    SimpleGraph.adjMatrix, hone]

theorem singleton_neg_zero (γ : ℝ) :
    (matrixInertia (centeredShift ((⊥ : SimpleGraph (Fin 1)).lapMatrix ℝ) γ)).neg = 0 := by
  have h := DenseIntMatrix.checkInertia_sound singletonInput ⟨0, 1, 0⟩ singleton_checked
  rw [singleton_binding γ] at h
  exact congrArg Inertia.neg h

theorem singleton_empty_cut_bound :
    (0 : ℝ) * 0 * (1 - 0) ≤
      1 * (((⊥ : SimpleGraph (Fin 1)).interedges ∅ (∅ : Finset (Fin 1))ᶜ).card : ℝ) := by
  simpa using gap_mul_card_mul_compl_le_card_mul_cut_of_inertia
    (⊥ : SimpleGraph (Fin 1)) 0 (singleton_neg_zero 0) ∅

theorem singleton_full_negative_cut_bound :
    (-1 : ℝ) * 1 * (1 - 1) ≤
      1 * (((⊥ : SimpleGraph (Fin 1)).interedges Finset.univ
        (Finset.univ : Finset (Fin 1))ᶜ).card : ℝ) := by
  simpa using gap_mul_card_mul_compl_le_card_mul_cut_of_inertia
    (⊥ : SimpleGraph (Fin 1)) (-1) (singleton_neg_zero (-1)) Finset.univ

def pathInput : DenseIntMatrix := DenseIntMatrix.ofFn 3 fun i j =>
  3 * ((if i = j then (if i = 1 then 2 else 1) else 0) -
    (if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
      (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then 1 else 0)) -
    ((if i = j then 3 else 0) - 1)

theorem path_degrees_unequal :
    SpectralGraphTests.Cut.path3.degree 0 = 1 ∧
      SpectralGraphTests.Cut.path3.degree 1 = 2 := by
  decide +kernel

theorem pathInput_rat : pathInput.toRatMatrix =
    (3 : ℚ) • SpectralGraphTests.Cut.path3.lapMatrix ℚ -
      ((3 : ℚ) • (1 : Matrix (Fin 3) (Fin 3) ℚ) -
        Matrix.of (fun (_ : Fin 3) (_ : Fin 3) => (1 : ℚ))) := by
  decide +kernel

theorem pathInput_checked : pathInput.checkInertia ⟨1, 2, 0⟩ = true := by
  decide +kernel

theorem pathInput_real : ratCastMatrix pathInput.toRatMatrix =
    centeredShift (SpectralGraphTests.Cut.path3.lapMatrix ℝ) 1 := by
  rw [pathInput_rat]
  ext i j
  have hone : ((1 : Matrix (Fin 3) (Fin 3) ℚ) i j : ℝ) =
      (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := by
    change ((1 : Matrix (Fin 3) (Fin 3) ℚ).map (Rat.castHom ℝ)) i j = _
    rw [Matrix.map_one] <;> simp
  simp [ratCastMatrix, centeredShift, SimpleGraph.lapMatrix,
    SimpleGraph.degMatrix, SimpleGraph.adjMatrix, Matrix.diagonal_apply,
    hone]
  split_ifs <;> norm_num [hone]

theorem path_neg_zero :
    (matrixInertia (centeredShift (SpectralGraphTests.Cut.path3.lapMatrix ℝ) 1)).neg = 0 := by
  have h := DenseIntMatrix.checkInertia_sound pathInput ⟨1, 2, 0⟩ pathInput_checked
  rw [pathInput_real] at h
  exact congrArg Inertia.neg h

theorem path_nontrivial_cut_bound :
    (1 : ℝ) * 1 * (3 - 1) ≤
      3 * ((SpectralGraphTests.Cut.path3.interedges ({0} : Finset (Fin 3))
        ({0} : Finset (Fin 3))ᶜ).card : ℝ) := by
  simpa using gap_mul_card_mul_compl_le_card_mul_cut_of_inertia
    SpectralGraphTests.Cut.path3 1 path_neg_zero {0}

theorem prism_two_singular :
    (matrixInertia (centeredShift (prism.lapMatrix ℝ) 2)).zero = 2 := by
  rw [prism_centered_two_inertia]

theorem prism_three_negative :
    (matrixInertia (centeredShift (prism.lapMatrix ℝ) 3)).neg = 1 := by
  rw [prism_centered_three_inertia]

theorem prism_three_false_face_bound :
    ¬ ((3 : ℝ) * (face.card : ℝ) * (6 - (face.card : ℝ)) ≤
      6 * ((prism.interedges face faceᶜ).card : ℝ)) := by
  rw [face_card, face_cut_card]
  norm_num

def twoTriangles : SimpleGraph (Fin 6) where
  Adj i j := i ≠ j ∧ i.val / 3 = j.val / 3
  symm := by intro i j h; exact ⟨h.1.symm, h.2.symm⟩
  loopless := ⟨fun i h => h.1 rfl⟩

instance : DecidableRel twoTriangles.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

theorem twoTriangles_lap_psd : (twoTriangles.lapMatrix ℝ).PosSemidef :=
  twoTriangles.posSemidef_lapMatrix ℝ

theorem twoTriangles_face_cut_zero :
    (twoTriangles.interedges face faceᶜ).card = 0 := by decide +kernel

theorem twoTriangles_false_if_ordinary_psd_only :
    ¬ ((2 : ℝ) * (face.card : ℝ) * (6 - (face.card : ℝ)) ≤
      6 * ((twoTriangles.interedges face faceᶜ).card : ℝ)) := by
  rw [face_card, twoTriangles_face_cut_zero]
  norm_num

end SpectralGraphTests.SpectralCut
