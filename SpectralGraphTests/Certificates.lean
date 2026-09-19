import SpectralGraph.Certificate.IntegerCheck
import SpectralGraph.Graph.Search
import SpectralGraph.Graph.InertiaIso

open SpectralGraph SpectralGraph.Certificate

namespace SpectralGraphTests.Certificates

def singularWeighted : DenseIntMatrix := ⟨3, #[0, 3, 0, 3, 0, 0, 0, 0, 0]⟩

example : matrixInertia (ratCastMatrix singularWeighted.toRatMatrix) = ⟨1, 1, 1⟩ :=
  singularWeighted.checkInertia_sound _ (by decide +kernel)

-- Both signs of diagonal pivot and a singular remainder.
example : (⟨3, #[-2, 0, 0, 0, 5, 0, 0, 0, 0]⟩ : DenseIntMatrix).checkInertia
    ⟨1, 1, 1⟩ = true := by decide +kernel

example : (⟨0, #[]⟩ : DenseIntMatrix).checkInertia ⟨0, 0, 0⟩ = true := by decide +kernel
example : (⟨2, #[0]⟩ : DenseIntMatrix).checkInertia ⟨0, 2, 0⟩ = false := by decide +kernel
example : (⟨1, #[0, 0]⟩ : DenseIntMatrix).checkInertia ⟨0, 1, 0⟩ = false := by decide +kernel
example : (⟨2, #[0, 1, 0, 0]⟩ : DenseIntMatrix).checkInertia ⟨1, 0, 1⟩ = false := by decide +kernel
example : singularWeighted.checkInertia ⟨3, 0, 0⟩ = false := by decide +kernel

example : Graph.checkIsomorphism (⊤ : SimpleGraph (Fin 3)) ⊤ [2, 0, 1] = true := by
  decide +kernel
example : Graph.checkIsomorphism (⊤ : SimpleGraph (Fin 3)) ⊥ [2, 0, 1] = false := by
  decide +kernel
example : Graph.checkIsomorphism (⊤ : SimpleGraph (Fin 3)) ⊤ [0, 1, 2, 99] = false := by
  decide +kernel
example : Graph.checkIsomorphism (⊤ : SimpleGraph (Fin 3)) ⊤ [0, 0, 2] = false := by
  decide +kernel
example : Graph.checkIsomorphism (⊤ : SimpleGraph (Fin 3)) ⊤ [0, 1] = false := by
  decide +kernel
example : Graph.checkIsomorphism (⊤ : SimpleGraph (Fin 0)) ⊤ [] = true := by
  decide +kernel

-- Exhaustive candidates reduce to parity representatives. No uniqueness or
-- equivalence machinery is needed by the generic relation interface.
def exhaustive : Search.Certificate (fun n : Nat ↦ n ∈ [0, 1, 2, 3]) :=
  ⟨[0, 1, 2, 3], fun _ h ↦ h⟩

def parityCheck (x y : Nat) (_ : Unit) : Bool := decide (x % 2 = y % 2)
def parityDedup : Search.DedupCertificate Nat Unit :=
  ⟨[0, 1], [(0, ()), (1, ()), (0, ()), (1, ())]⟩

example : Search.dedupCertificateValid parityCheck [0, 1, 2, 3] parityDedup = true := by
  decide +kernel
example : Search.dedupCertificateValid parityCheck [0]
    ⟨[0], [(1, ())]⟩ = false := by decide +kernel
example : Search.dedupCertificateValid parityCheck [0]
    ⟨[0], []⟩ = false := by decide +kernel
example : Search.dedupCertificateValid parityCheck []
    ⟨[0], [(0, ())]⟩ = false := by decide +kernel

-- A complete generic coverage-to-property proof using a sound checker.
example : ∀ n : Nat, n ∈ [0, 1, 2, 3] → n % 2 ≤ 1 := by
  let C : Search.Cover (fun n : Nat ↦ n ∈ [0, 1, 2, 3])
      (fun x y ↦ x % 2 = y % 2) :=
    ⟨exhaustive.candidates, fun x hx ↦ ⟨x, hx, rfl⟩⟩
  let D := C.deduplicate parityCheck
    (fun _ _ _ h ↦ of_decide_eq_true h) (fun h₁ h₂ ↦ h₁.trans h₂)
    parityDedup (by decide +kernel)
  exact D.verify (fun n ↦ n % 2 ≤ 1) (fun n ↦ decide (n % 2 ≤ 1))
    (fun _ h ↦ of_decide_eq_true h)
    (fun _ _ h hp ↦ by dsimp at *; rw [h]; exact hp) (by decide +kernel)

end SpectralGraphTests.Certificates
