import SpectralGraph.Certificate.Basic

/- Generated from exact JSON, SHA256 a9661c0866ef9af79f2ff1b20116e7d05a3db4169dd1183198b375fc10452917.
The external producer is untrusted; the theorem checks the certificate in Lean.
-/
namespace GeneratedCertificate
open SpectralGraph SpectralGraph.Certificate

def input : Matrix (Fin 3) (Fin 3) ℚ := !![0, (1 / 2), 0;
    (1 / 2), 0, (3 / 2);
    0, (3 / 2), 0]

def certificate : InertiaCertificate (Fin 3) where
  change := !![1, (-1 / 2), -3;
    1, (1 / 2), 0;
    0, 0, 1]
  inverse := !![(1 / 2), (1 / 2), (3 / 2);
    -1, 1, -3;
    0, 0, 1]
  target := ⟨1, 1, 1⟩

theorem inertia : matrixInertia (ratCastMatrix input) = ⟨1, 1, 1⟩ :=
  certificate.sound input (by decide +kernel)

end GeneratedCertificate
