import SpectralGraph.Inertia.PrincipalSpectrum
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Ordered adjacency spectra of induced graphs

The adjacency matrix of `G.induce S` is literally the principal submatrix of
the adjacency matrix of `G` on the subtype `S`.  The interlacing theorem below
keeps the descending, zero-based indexing of `eigenvalues₀`; in particular a
codimension `d` shifts the lower ambient index by exactly `d`.

This file deliberately concerns adjacency matrices only.  Induced Laplacians
are not principal restrictions because vertex degrees change on deletion.
-/

namespace SpectralGraph
namespace Graph

open Matrix
open SpectralGraph.Inertia

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The canonical embedding of an induced-graph vertex type into the ambient
vertex type. -/
def inducedVertexEmbedding (S : Set V) : {v // v ∈ S} ↪ V :=
  ⟨Subtype.val, Subtype.coe_injective⟩

@[simp] theorem inducedVertexEmbedding_apply (S : Set V) (v : {v // v ∈ S}) :
    inducedVertexEmbedding S v = v.1 := rfl

@[simp] theorem induced_adjMatrix_eq_submatrix
    (G : SimpleGraph V) (S : Set V) [DecidablePred (· ∈ S)]
    [DecidableRel G.Adj] [DecidableRel (G.induce S).Adj] :
    (G.induce S).adjMatrix ℝ =
      (G.adjMatrix ℝ).submatrix (inducedVertexEmbedding S)
        (inducedVertexEmbedding S) := by
  ext v w
  simp only [SimpleGraph.adjMatrix_apply, Matrix.submatrix_apply,
    SimpleGraph.induce_adj]
  rfl

/-- Over the reals, a graph adjacency matrix is Hermitian. -/
theorem adjMatrix_isHermitian (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.adjMatrix ℝ).IsHermitian := by
  simpa only [Matrix.IsHermitian, Matrix.IsSymm,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    (G.isSymm_adjMatrix)

/-- The induced adjacency matrix is Hermitian, with the proof supplied by the
exact principal-submatrix identity. -/
theorem induced_adjMatrix_isHermitian
    (G : SimpleGraph V) (S : Set V) [DecidablePred (· ∈ S)]
    [DecidableRel G.Adj] [DecidableRel (G.induce S).Adj] :
    ((G.induce S).adjMatrix ℝ).IsHermitian := by
  rw [induced_adjMatrix_eq_submatrix]
  exact (adjMatrix_isHermitian G).submatrix (inducedVertexEmbedding S)

/-- Ordered Cauchy interlacing for the adjacency matrix of an induced graph.

For `card V = card S + d`, the retained `k`th eigenvalue lies between the
ambient eigenvalues at `k+d` and `k`.  The endpoint `k+d` is supplied as a
`Fin` value, so no invalid endpoint is silently clamped. -/
theorem induced_adjacency_eigenvalue_interlaces
    (G : SimpleGraph V) (S : Set V) [DecidablePred (· ∈ S)]
    [DecidableRel G.Adj] [DecidableRel (G.induce S).Adj] (d : Nat)
    (hcard : Fintype.card V = Fintype.card {v // v ∈ S} + d)
    (k : Fin (Fintype.card {v // v ∈ S}))
    (hk : k.val + d < Fintype.card V)
    (hA : (G.adjMatrix ℝ).IsHermitian)
    (hP : ((G.induce S).adjMatrix ℝ).IsHermitian) :
    hA.eigenvalues₀ ⟨k.val + d, hk⟩ ≤ hP.eigenvalues₀ k ∧
      hP.eigenvalues₀ k ≤ hA.eigenvalues₀
          ⟨k.val, by omega⟩ := by
  let e := inducedVertexEmbedding S
  have hident := induced_adjMatrix_eq_submatrix G S
  have hcore := principalSubmatrix_eigenvalues₀_interlace
    (G.adjMatrix ℝ) hA e d hcard k
  have hAS := hA.submatrix e
  have hAS' : ((G.induce S).adjMatrix ℝ).IsHermitian := by
    simpa only [hident] using hAS
  have hres : hA.eigenvalues₀ ⟨k.val + d, hk⟩ ≤ hAS'.eigenvalues₀ k ∧
      hAS'.eigenvalues₀ k ≤ hA.eigenvalues₀ ⟨k.val, by omega⟩ := by
    simpa only [hident] using hcore
  have hproof : hAS' = hP := Subsingleton.elim _ _
  simpa only [hproof] using hres

/-- A convenience form of `induced_adjacency_eigenvalue_interlaces` that
constructs both real-Hermitian proofs internally. -/
theorem induced_adjacency_eigenvalue_interlaces_default
    (G : SimpleGraph V) (S : Set V) [DecidablePred (· ∈ S)]
    [DecidableRel G.Adj] [DecidableRel (G.induce S).Adj] (d : Nat)
    (hcard : Fintype.card V = Fintype.card {v // v ∈ S} + d)
    (k : Fin (Fintype.card {v // v ∈ S}))
    (hk : k.val + d < Fintype.card V) :
    (adjMatrix_isHermitian G).eigenvalues₀ ⟨k.val + d, hk⟩ ≤
        (induced_adjMatrix_isHermitian G S).eigenvalues₀ k ∧
      (induced_adjMatrix_isHermitian G S).eigenvalues₀ k ≤
        (adjMatrix_isHermitian G).eigenvalues₀ ⟨k.val, by omega⟩ := by
  exact induced_adjacency_eigenvalue_interlaces G S d hcard k hk
    (adjMatrix_isHermitian G) (induced_adjMatrix_isHermitian G S)

/-- Graph-first Cauchy interlacing for an induced adjacency matrix.

The consumer supplies only the ambient graph, the retained vertex set, and a
valid retained index.  The codimension and both ambient endpoint proofs are
computed from the canonical subtype embedding. -/
theorem inducedAdjacencySpectrumInterlaces
    (G : SimpleGraph V) (S : Set V) [DecidablePred (· ∈ S)]
    [DecidableRel G.Adj] [DecidableRel (G.induce S).Adj]
    (k : Fin (Fintype.card {v // v ∈ S})) :
    (adjMatrix_isHermitian G).eigenvalues₀
        ⟨k.val + (Fintype.card V - Fintype.card {v // v ∈ S}), by
          have hle := Fintype.card_le_of_injective
            (inducedVertexEmbedding S) (inducedVertexEmbedding S).injective
          omega⟩ ≤
        (induced_adjMatrix_isHermitian G S).eigenvalues₀ k ∧
      (induced_adjMatrix_isHermitian G S).eigenvalues₀ k ≤
        (adjMatrix_isHermitian G).eigenvalues₀ ⟨k.val, by
          have hle := Fintype.card_le_of_injective
            (inducedVertexEmbedding S) (inducedVertexEmbedding S).injective
          omega⟩ := by
  have hle := Fintype.card_le_of_injective
    (inducedVertexEmbedding S) (inducedVertexEmbedding S).injective
  exact induced_adjacency_eigenvalue_interlaces_default G S
    (Fintype.card V - Fintype.card {v // v ∈ S}) (by omega) k (by omega)

end Graph
end SpectralGraph
