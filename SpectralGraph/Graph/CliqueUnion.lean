import SpectralGraph.Inertia.PosSemidefinite
import SpectralGraph.GraphMatrix
import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Shifted adjacency and disjoint unions of cliques

For a finite simple graph `G`, the matrix `I + A(G)` is positive semidefinite
exactly when the complement of `G` is complete multipartite.  Equivalently,
`G` is a disjoint union of cliques.  The reverse implication is witnessed by
the vertex-to-clique incidence Gram factorization.
-/

namespace SpectralGraph.Graph

open Matrix
open scoped SimpleGraph

universe u

private abbrev CliqueClass {V : Type u} {G : SimpleGraph V}
    (hG : Gᶜ.IsCompleteMultipartite) := Quotient hG.setoid

noncomputable instance cliqueClassFintype
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : Gᶜ.IsCompleteMultipartite) : Fintype (CliqueClass hG) :=
  Fintype.ofFinite _

noncomputable instance cliqueClassDecidableEq
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : Gᶜ.IsCompleteMultipartite) : DecidableEq (CliqueClass hG) :=
  Classical.decEq _

/-- Vertex-to-clique incidence matrix for a graph whose complement is
complete multipartite. -/
private noncomputable def cliqueIncidenceMatrix
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Gᶜ.IsCompleteMultipartite) : Matrix (CliqueClass hG) V ℝ := by
  classical
  exact fun c v ↦ if Quotient.mk hG.setoid v = c then 1 else 0

/-- The shifted adjacency matrix of a disjoint union of cliques is the Gram
matrix of its vertex-to-clique incidence matrix. -/
private theorem one_add_adjMatrix_eq_cliqueGram
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Gᶜ.IsCompleteMultipartite) :
    1 + G.adjMatrix ℝ =
      (cliqueIncidenceMatrix G hG).transpose * cliqueIncidenceMatrix G hG := by
  classical
  ext v w
  simp only [Matrix.add_apply, Matrix.one_apply,
    SimpleGraph.adjMatrix_apply, Matrix.mul_apply,
    Matrix.transpose_apply, cliqueIncidenceMatrix]
  change (if v = w then 1 else 0) + (if G.Adj v w then 1 else 0) =
    ∑ c : CliqueClass hG,
      (if Quotient.mk hG.setoid v = c then 1 else 0) *
      (if Quotient.mk hG.setoid w = c then 1 else 0)
  rw [Finset.sum_eq_single (Quotient.mk hG.setoid v)]
  · simp only [if_pos, one_mul]
    simp only [Quotient.eq_iff_equiv]
    change ((if v = w then (1 : ℝ) else 0) +
      (if G.Adj v w then 1 else 0)) =
      if hG.setoid.r w v then 1 else 0
    have hrel : hG.setoid.r w v ↔ v = w ∨ G.Adj v w := by
      change (¬Gᶜ.Adj w v) ↔ v = w ∨ G.Adj v w
      constructor
      · intro h
        by_cases hvw : v = w
        · exact Or.inl hvw
        · exact Or.inr (Classical.byContradiction fun hnot ↦
            h ((G.compl_adj w v).mpr ⟨Ne.symm hvw, fun hwv ↦ hnot hwv.symm⟩))
      · rintro (rfl | hadj)
        · simp
        · intro hcomp
          exact ((G.compl_adj w v).mp hcomp).2 hadj.symm
    rw [hrel]
    by_cases hvw : v = w
    · subst w
      simp
    · by_cases hadj : G.Adj v w <;> simp [hvw, hadj]
  · intro c _ hcv
    simp [Ne.symm hcv]
  · simp

/-- `I + A(G)` is positive semidefinite exactly when `G` is a disjoint union
of cliques, expressed by the standard complete-multipartite predicate on its
complement. -/
theorem one_add_adjMatrix_posSemidef_iff_compl_isCompleteMultipartite
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (1 + G.adjMatrix ℝ).PosSemidef ↔ Gᶜ.IsCompleteMultipartite := by
  constructor
  · intro hpsd
    refine ⟨fun x y z hxy hyz ↦ ?_⟩
    intro hxz
    have hxz_ne : x ≠ z := ((G.compl_adj x z).mp hxz).1
    have hxz_not : ¬G.Adj x z := ((G.compl_adj x z).mp hxz).2
    have hzx_not : ¬G.Adj z x := fun hzx ↦ hxz_not hzx.symm
    have hxy' : x = y ∨ G.Adj x y := by
      by_cases heq : x = y
      · exact Or.inl heq
      · exact Or.inr (Classical.byContradiction fun hnot ↦
          hxy ((G.compl_adj x y).mpr ⟨heq, hnot⟩))
    have hyz' : y = z ∨ G.Adj y z := by
      by_cases heq : y = z
      · exact Or.inl heq
      · exact Or.inr (Classical.byContradiction fun hnot ↦
          hyz ((G.compl_adj y z).mpr ⟨heq, hnot⟩))
    rcases hxy' with rfl | hxyG
    · exact hyz hxz
    rcases hyz' with rfl | hyzG
    · exact hxy hxz
    have hxy_ne : x ≠ y := hxyG.ne
    have hyz_ne : y ≠ z := hyzG.ne
    let e : Fin 3 → V := ![x, y, z]
    have hsub := hpsd.submatrix e
    let q : Fin 3 → ℝ := ![1, -1, 1]
    have hnonneg := hsub.dotProduct_mulVec_nonneg q
    simp [q, e, dotProduct, mulVec, Fin.sum_univ_succ, Matrix.one_apply,
      SimpleGraph.adjMatrix_apply, hxyG, hxyG.symm, hyzG, hyzG.symm,
      hxz_not, hzx_not,
      hxz_ne, hxz_ne.symm,
      hxy_ne, hxy_ne.symm, hyz_ne, hyz_ne.symm] at hnonneg
    norm_num at hnonneg
  · intro hG
    classical
    rw [one_add_adjMatrix_eq_cliqueGram G hG]
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      posSemidef_conjTranspose_mul_self (cliqueIncidenceMatrix G hG)

/-- Vanishing negative inertia of `I + A(G)` forces `G` to be a disjoint
union of cliques. -/
theorem compl_isCompleteMultipartite_of_one_add_adjMatrix_inertia_neg_eq_zero
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hneg : (matrixInertia (1 + G.adjMatrix ℝ)).neg = 0) :
    Gᶜ.IsCompleteMultipartite := by
  apply (one_add_adjMatrix_posSemidef_iff_compl_isCompleteMultipartite G).mp
  apply matrix_posSemidef_of_matrixInertia_neg_eq_zero
  · exact Matrix.IsSymm.add Matrix.isSymm_one G.isSymm_adjMatrix
  · exact hneg

end SpectralGraph.Graph
