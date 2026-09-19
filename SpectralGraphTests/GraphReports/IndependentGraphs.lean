import SpectralGraph.Graph.EncodingCheck

namespace SpectralGraphTests.GraphReports.IndependentGraphs

def completeThree : SimpleGraph (Fin 3) := ⊤
instance : DecidableRel completeThree.Adj := by unfold completeThree; infer_instance

def edge02 : SimpleGraph (Fin 3) := SimpleGraph.fromRel fun i j =>
  (i.val = 0 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0)
instance : DecidableRel edge02.Adj := by unfold edge02; infer_instance

end SpectralGraphTests.GraphReports.IndependentGraphs
