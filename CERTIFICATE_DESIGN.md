# Certificate boundaries

The library separates externally supplied data, executable acceptance checks, and
the semantic theorem proved from accepted data. Producer success, a JSON digest,
or a Boolean result without a soundness theorem is not a certificate.

| Interface | Checked obligations | Conclusion |
| --- | --- | --- |
| `InertiaCertificate` | inverse, congruence diagonal, and diagonal signs | real quadratic-form inertia equals the target |
| `ProductInertiaCertificate` | `QP=I`, checked supplied image, diagonal identity, and signs | the same inertia conclusion |
| `DenseIntMatrix.checkNormalizedInertia` | storage length, symmetry, and normalized elimination result | inertia of the interpreted real matrix |
| `checkInertiaAt` | storage and positive-denominator-cleared shift | inertia at a rational threshold |
| Negative-subspace certificates | exact negative diagonal Gram identity | a lower bound on negative index |
| Kernel witnesses | symmetry, nonzero vector, and exact matrix-vector product | positive nullity and singularity |
| Solve and Schur interfaces | inverse/solve equations and block identities | inverse bilinear or Schur conclusions |

Matrix spectral statements require the symmetry or Hermitian hypotheses in their
theorems. For a nonsymmetric matrix, `matrixInertia` is a quadratic-form notion;
its zero index is not generally the kernel dimension. Graph adjacency interfaces
provide their appropriate symmetry facts.

All JSON input is parsed strictly. Dense data must have the declared shape;
sparse data must have in-range, distinct, nonzero coordinates. A supplied image
or inverse is checked rather than trusted. Generated Lean source is only a
candidate until it compiles.

Exact arithmetic avoids floating-point assumptions. Threshold clearing and
common-factor reduction have explicit correctness conditions and do not relax
the original storage contract. Enumeration and batch interfaces likewise require
proved coverage rather than relying on counts, filenames, or external status.
