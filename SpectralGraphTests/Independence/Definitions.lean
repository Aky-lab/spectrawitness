import SpectralGraph.Graph.IntegerSpectrum
import Mathlib.Combinatorics.SimpleGraph.Circulant

/-! Independently named finite objects for the two independence certificates. -/

namespace SpectralGraphTests.Independence.Definitions

open SpectralGraph SpectralGraph.Certificate

def signedC4 : Matrix (Fin 4) (Fin 4) ℚ :=
  !![ 0, 1, 0, -1;
      1, 0, 1,  0;
      0, 1, 0,  1;
     -1, 0, 1,  0]

theorem signedC4_isSymm : signedC4.IsSymm := by
  decide +kernel

theorem signedC4_supported :
    ∀ u v : Fin 4, ¬(SimpleGraph.cycleGraph 4).Adj u v → signedC4 u v = 0 := by
  decide +kernel

theorem signedC4_real_supported :
    ∀ u v : Fin 4, ¬(SimpleGraph.cycleGraph 4).Adj u v →
      ratCastMatrix signedC4 u v = 0 := by
  intro u v h
  simp [ratCastMatrix, signedC4_supported u v h]

def petersen : SimpleGraph (Fin 10) := SimpleGraph.fromRel fun i j =>
  (i.val < 5 ∧ j.val < 5 ∧ j.val = (i.val + 1) % 5) ∨
  (5 ≤ i.val ∧ 5 ≤ j.val ∧ j.val - 5 = (i.val - 5 + 2) % 5) ∨
  (i.val < 5 ∧ j.val = i.val + 5)

instance : DecidableRel petersen.Adj := by unfold petersen; infer_instance

end SpectralGraphTests.Independence.Definitions
