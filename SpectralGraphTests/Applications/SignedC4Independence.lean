import SpectralGraph.Graph.Independence
import SpectralGraph.Graph.IntegerSpectrum
import SpectralGraphTests.Independence.SignedC4Certificate

/-! The signed supported matrix gives a sharp bound where ordinary C4 adjacency does not. -/

namespace SpectralGraphTests.Applications.SignedC4Independence

open SpectralGraph SpectralGraph.Graph SpectralGraph.Certificate
open SpectralGraphTests.Independence

def C4 : SimpleGraph (Fin 4) := SimpleGraph.cycleGraph 4

instance : DecidableRel C4.Adj := by unfold C4; infer_instance

private theorem signed_inertia :
    matrixInertia (ratCastMatrix Definitions.signedC4) = ⟨2, 0, 2⟩ := by
  simpa [SignedC4Certificate.input] using SignedC4Certificate.inertia

theorem indepSet_card_le_two (s : Finset (Fin 4))
    (hs : C4.IsIndepSet (↑s : Set (Fin 4))) : s.card ≤ 2 := by
  have h := indepSet_card_le_inertia_of_supported C4
    (ratCastMatrix Definitions.signedC4)
    (by simpa [C4] using Definitions.signedC4_real_supported) s hs
  simpa [signed_inertia] using h

theorem indepNum_eq_two : C4.indepNum = 2 := by
  have hu := indepNum_le_inertia_of_supported C4
    (ratCastMatrix Definitions.signedC4)
    (by simpa [C4] using Definitions.signedC4_real_supported)
  have hu' : C4.indepNum ≤ 2 := by simpa [signed_inertia] using hu
  have hset : C4.IsIndepSet ({0, 2} : Finset (Fin 4)) := by decide +kernel
  have hl := hset.card_le_indepNum
  have hcard : ({0, 2} : Finset (Fin 4)).card = 2 := by decide +kernel
  rw [hcard] at hl
  exact Nat.le_antisymm hu' hl

theorem ordinary_adjacency_inertia :
    matrixInertia (C4.adjMatrix ℝ) = ⟨1, 2, 1⟩ := by
  have h := checkAdjacencyInertiaAt_sound C4 0 ⟨1, 2, 1⟩
    (by decide +kernel)
  simpa using h

theorem ordinary_bound_eq_three :
    (matrixInertia (C4.adjMatrix ℝ)).zero +
      min (matrixInertia (C4.adjMatrix ℝ)).pos
          (matrixInertia (C4.adjMatrix ℝ)).neg = 3 := by
  rw [ordinary_adjacency_inertia]
  decide

end SpectralGraphTests.Applications.SignedC4Independence
