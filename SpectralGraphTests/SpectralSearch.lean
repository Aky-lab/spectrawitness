import SpectralGraph.Graph.Search
import SpectralGraph.Certificate.IntegerCheck

/-! A complete spectral search: two distinct labelings, one checked representative. -/

namespace SpectralGraphTests.SpectralSearch
open SpectralGraph SpectralGraph.Certificate

def decode (b : Bool) : SimpleGraph (Fin 3) :=
  SimpleGraph.fromRel (fun i j ↦ if b then i = 0 ∧ j = 1 else i = 1 ∧ j = 2)

instance (b : Bool) : DecidableRel (decode b).Adj := by
  unfold decode
  infer_instance

def candidates : Search.Certificate (fun _ : Bool ↦ True) :=
  ⟨[false, true], by intro b _; cases b <;> simp⟩

def representatives : Search.DedupCertificate Bool (List Nat) :=
  ⟨[true], [(0, [2, 0, 1]), (0, [0, 1, 2])]⟩

def representativeMatrix : DenseIntMatrix := ⟨3, #[0, 1, 0, 1, 0, 0, 0, 0, 0]⟩

theorem representative_inertia :
    matrixInertia ((decode true).adjMatrix ℝ) = ⟨1, 1, 1⟩ := by
  have h := representativeMatrix.checkInertia_sound ⟨1, 1, 1⟩ (by decide +kernel)
  have hm : ratCastMatrix representativeMatrix.toRatMatrix = (decode true).adjMatrix ℝ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [ratCastMatrix, DenseIntMatrix.toRatMatrix, DenseIntMatrix.entry,
        representativeMatrix, decode, SimpleGraph.adjMatrix, SimpleGraph.fromRel_adj] <;>
      decide +kernel
  rwa [hm] at h

/-- The universal conclusion is obtained by coverage, isomorphism checks and
one semantic integer computation, not by checking both matrices independently. -/
theorem all_candidates_inertia (b : Bool) :
    matrixInertia ((decode b).adjMatrix ℝ) = ⟨1, 1, 1⟩ := by
  have h := Graph.verifyInertia decode candidates representatives
    (by decide +kernel) 0 (fun I ↦ I = ⟨1, 1, 1⟩) (fun b ↦ b)
    (by
      intro x hx
      cases x with
      | false => contradiction
      | true => simpa using representative_inertia)
    (by decide +kernel) b trivial
  simpa using h

end SpectralGraphTests.SpectralSearch
