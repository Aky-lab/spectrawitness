import SpectralGraph.Inertia.ShiftedGramGeneral
import SpectralGraph.Inertia.ShiftedGram

/-! Arbitrary-threshold Gram transfer, including empty and rectangular matrices. -/
namespace SpectralGraphTests.ShiftedGramGeneral
open SpectralGraph SpectralGraph.Inertia Matrix

-- Existing shift-two definitions have precisely the same semantics.
example (N : Matrix (Fin 3) (Fin 2) ℝ) : rowGramAt N 2 = shiftedRowGram N := rfl
example (N : Matrix (Fin 3) (Fin 2) ℝ) : colGramAt N 2 = shiftedColGram N := rfl

-- A nonintegral threshold requires no arithmetic or integrality assumptions on N.
example (N : Matrix (Fin 7) (Fin 3) ℝ) :
    (matrixInertia (rowGramAt N (3 / 7))).neg =
      (matrixInertia (colGramAt N (3 / 7))).neg + 4 := by
  simpa using gramAt_neg_eq_add N (by norm_num : (0 : ℝ) < 3 / 7) (by decide)

-- Real thresholds may be arbitrary, not merely rational certificates.
example (N : Matrix (Fin 2) (Fin 5) ℝ) {t : ℝ} (ht : 0 < t) :
    matrixSignature (rowGramAt N t) = matrixSignature (colGramAt N t) + 3 := by
  have h := gramAt_signature_eq N ht
  simp only [Fintype.card_fin, Nat.cast_ofNat] at h
  omega

-- Rectangular matrices with an empty column type are included in the API.
example (N : Matrix (Fin 4) (Fin 0) ℝ) {t : ℝ} (ht : 0 < t) :
    (matrixInertia (rowGramAt N t)).neg = 4 := by
  have h := gramAt_neg_add_card_eq N ht
  have ho := matrixInertia_order (colGramAt N t)
  simp only [Inertia.order, Fintype.card_fin] at h ho
  omega

-- The transfer specializes to both zero and strictly positive spectral counts.
example (N : Matrix (Fin 3) (Fin 8) ℝ) :
    (matrixInertia (rowGramAt N (1 / 5))).zero =
      (matrixInertia (colGramAt N (1 / 5))).zero :=
  gramAt_zero_eq N (by norm_num)

#print axioms SpectralGraph.Inertia.gramAt_inertia_relations
#print axioms SpectralGraph.Inertia.gramAt_signature_eq

end SpectralGraphTests.ShiftedGramGeneral
