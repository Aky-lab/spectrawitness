import SpectralGraph
import SpectralGraphTests.Batches
import SpectralGraphTests.Biadjacency
import SpectralGraphTests.Bipartite
import SpectralGraphTests.Certificates
import SpectralGraphTests.CliqueUnionCertificate
import SpectralGraphTests.CliqueUnion
import SpectralGraphTests.Encoding
import SpectralGraphTests.EncodingInvariant
import SpectralGraphTests.EnumeratedInertia
import SpectralGraphTests.Extension
import SpectralGraphTests.Generated
import SpectralGraphTests.GraphReports
import SpectralGraphTests.Independence.Definitions
import SpectralGraphTests.Independence.SignedC4Certificate
import SpectralGraphTests.Independence.PetersenReport
import SpectralGraphTests.Independence
import SpectralGraphTests.Hoffman.Definitions
import SpectralGraphTests.Hoffman.RookReport
import SpectralGraphTests.Hoffman
import SpectralGraphTests.Cut
import SpectralGraphTests.Cuts.Definitions
import SpectralGraphTests.Cuts.PrismCertificate
import SpectralGraphTests.Applications.PrismBisection
import SpectralGraphTests.SpectralCut
import SpectralGraphTests.Dirichlet.Definitions
import SpectralGraphTests.Dirichlet.BridgeCertificate
import SpectralGraphTests.Applications.WheatstoneDirichlet
import SpectralGraphTests.SchurDirichlet
import SpectralGraphTests.RegularSupportBound
import SpectralGraphTests.ZeroPrincipal
import SpectralGraphTests.IntegerSpectralInterval
import SpectralGraphTests.IntegerSpectrum
import SpectralGraphTests.LinearSolve
import SpectralGraphTests.NegativeSpectrum
import SpectralGraphTests.NormalizedGraphInertia
import SpectralGraphTests.NormalizedInteger
import SpectralGraphTests.PackedEnumeration
import SpectralGraphTests.PackedEnumerationFast
import SpectralGraphTests.PackedInertia
import SpectralGraphTests.ProductInertia
import SpectralGraphTests.ProductWitnessSubspace
import SpectralGraphTests.PrincipalSpectrum
import SpectralGraphTests.PartitionSpectrum
import SpectralGraphTests.EquitableSpectrum
import SpectralGraphTests.RankOneGeneral
import SpectralGraphTests.RankOneSpectrum
import SpectralGraphTests.RankOneUpdate
import SpectralGraphTests.ShiftedGramGeneral
import SpectralGraphTests.SpectralSearch
import SpectralGraphTests.Spectrum
import SpectralGraphTests.SubsetCheck
import SpectralGraphTests.Trust
import SpectralGraphTests.Witness
import SpectralGraphTests.Applications.InducedCliqueSpectrum
import SpectralGraphTests.Applications.CycleLaplacianUpdate
import SpectralGraphTests.Applications.FriendshipPartition
import SpectralGraphTests.Applications.CliqueUnionSix
import SpectralGraphTests.Applications.SignedC4Independence
import SpectralGraphTests.Applications.PetersenIndependence
import SpectralGraphTests.Applications.RookHoffman

open SpectralGraph SpectralGraph.Certificate

namespace SpectralGraphTests

/-- Zero diagonal forces an off-diagonal pivot; the form is also singular. -/
def pathThree : Matrix (Fin 3) (Fin 3) ℚ := !![0, 1, 0; 1, 0, 1; 0, 1, 0]

example : matrixInertia (ratCastMatrix pathThree) = ⟨1, 1, 1⟩ := by
  have h : fastInertiaCertificateBool pathThree = true := by decide +kernel
  rw [matrixInertia_eq_fastComputedInertia pathThree h]
  decide +kernel

def hyperbolic : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 1, 0]

def hyperbolicCertificate : InertiaCertificate (Fin 2) where
  change := !![1, 1; 1, -1]
  inverse := !![1/2, 1/2; 1/2, -1/2]
  target := ⟨1, 0, 1⟩

example : matrixInertia (ratCastMatrix hyperbolic) = ⟨1, 0, 1⟩ :=
  hyperbolicCertificate.sound hyperbolic (by decide +kernel)

-- Reject both a corrupt inverse and a false target.
example : ({ hyperbolicCertificate with inverse := 0 }).check hyperbolic = false := by
  decide +kernel

example : ({ hyperbolicCertificate with target := ⟨2, 0, 0⟩ }).check hyperbolic = false := by
  decide +kernel

example : matrixInertia (ratCastMatrix (0 : Matrix (Fin 0) (Fin 0) ℚ)) = ⟨0, 0, 0⟩ := by
  have h : fastInertiaCertificateBool (0 : Matrix (Fin 0) (Fin 0) ℚ) = true := by
    decide +kernel
  rw [matrixInertia_eq_fastComputedInertia _ h]
  decide +kernel

-- A graph-level result at a nonzero threshold, including an exact zero index.
example : matrixInertia
    ((⊥ : SimpleGraph (Fin 2)).adjMatrix ℝ - (1 : ℝ) • 1) = ⟨0, 0, 2⟩ := by
  let c : InertiaCertificate (Fin 2) := ⟨1, 1, ⟨0, 0, 2⟩⟩
  simpa [c] using Graph.inertia_at_threshold ⊥ 1 c (by decide +kernel)

end SpectralGraphTests
