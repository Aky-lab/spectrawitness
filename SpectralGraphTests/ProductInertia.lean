import SpectralGraph.Certificate.ProductInertia

namespace SpectralGraphTests.ProductInertia
open SpectralGraph SpectralGraph.Certificate

def form : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 1, 0]
def cert : ProductInertiaCertificate (Fin 2) where
  change := !![1, 1; 1, -1]
  inverse := !![1/2, 1/2; 1/2, -1/2]
  image := !![1, -1; 1, 1]
  diagonal := ![2, -2]
  target := ⟨1, 0, 1⟩

example : cert.check form = true := by decide +kernel
example : ({ cert with image := 0 }).check form = false := by decide +kernel
example : ({ cert with diagonal := ![2, 2] }).check form = false := by decide +kernel
example : ({ cert with inverse := 1 }).check form = false := by decide +kernel
example : ({ cert with target := ⟨2, 0, 0⟩ }).check form = false := by decide +kernel
example : matrixInertia (ratCastMatrix form) = ⟨1, 0, 1⟩ := cert.sound form (by decide +kernel)

/-- Singular forms need no special determinant convention. -/
example : (ProductInertiaCertificate.mk (1 : Matrix (Fin 2) (Fin 2) ℚ) 1
    !![1, 0; 0, 0] ![1, 0] ⟨1, 1, 0⟩).check !![1, 0; 0, 0] = true := by decide +kernel
example : (ProductInertiaCertificate.mk (1 : Matrix (Fin 0) (Fin 0) ℚ) 1
    0 (fun i ↦ Fin.elim0 i) ⟨0, 0, 0⟩).check 0 = true := by decide +kernel

#print axioms ProductInertiaCertificate.sound
end SpectralGraphTests.ProductInertia
