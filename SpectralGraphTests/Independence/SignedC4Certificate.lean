import SpectralGraph.Certificate.ProductInertia
import SpectralGraphTests.Independence.Definitions

/- Generated from exact JSON, SHA256 ede61dd77ee17758cf8c016c09ca6af5ae606a14d8c02032ddce7cfee4a36a5f.
The external producer is untrusted; the theorem checks the certificate in Lean.
-/
namespace SpectralGraphTests.Independence.SignedC4Certificate
open SpectralGraph SpectralGraph.Certificate

def input : Matrix (Fin 4) (Fin 4) ℚ := _root_.SpectralGraphTests.Independence.Definitions.signedC4

def certificate : ProductInertiaCertificate (Fin 4) where
  change := !![1, (-1 / 2), -1, (1 / 2);
    1, (1 / 2), 1, (1 / 2);
    0, 0, 1, (-1 / 2);
    0, 0, 1, (1 / 2)]
  inverse := !![(1 / 2), (1 / 2), (1 / 2), (-1 / 2);
    -1, 1, -1, -1;
    0, 0, (1 / 2), (1 / 2);
    0, 0, -1, 1]
  image := !![1, (1 / 2), 0, 0;
    1, (-1 / 2), 0, 0;
    1, (1 / 2), 2, 1;
    -1, (1 / 2), 2, -1]
  diagonal := ![2, (-1 / 2), 4, -1]
  target := ⟨2, 0, 2⟩

theorem inertia : matrixInertia (ratCastMatrix input) = ⟨2, 0, 2⟩ :=
  certificate.sound input (by decide +kernel)

end SpectralGraphTests.Independence.SignedC4Certificate
