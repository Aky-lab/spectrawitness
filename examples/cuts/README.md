# Certified cuts of the triangular prism

`gap_mul_card_mul_compl_le_card_mul_cut_of_inertia` derives a cut lower bound
from zero negative index of a centered Laplacian shift. The premise permits a
singular attained gap. The prism example checks the exact integer matrix and
proves that every three-vertex side has at least three crossing edges, with a
triangular face attaining the bound.

Compile the application from the package root with explicit local inputs:

```text
python validate_local.py --lean PATH_TO_LEAN --packages PATH_TO_EXISTING_LAKE_PACKAGES --output-dir .validation-cuts --modules SpectralGraphTests.Applications.PrismBisection SpectralGraphTests.SpectralCut
```

The exact Boolean checker and its soundness theorem are the acceptance boundary;
no external solver output is trusted.
