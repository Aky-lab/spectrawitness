# Checked Dirichlet response of an unbalanced bridge

`checkSchur_harmonic_response` checks an exact rational block solve and Schur
remainder. With a positive-definite interior block, the companion theorems prove
the harmonic extension and its minimum energy for every real terminal vector.
The example's full Laplacian is singular; its interior block is the object
inverted by the certificate.

For terminal voltages `a,b`, the bridge has minimum energy
`(13/11) * (a-b)^2`; at unit voltage difference the terminal power is `13/11`.
This is conductance under the displayed once-per-edge convention, not resistance.

```text
python validate_local.py --lean PATH_TO_LEAN --packages PATH_TO_EXISTING_LAKE_PACKAGES --output-dir .validation-dirichlet --modules SpectralGraphTests.Applications.WheatstoneDirichlet SpectralGraphTests.SchurDirichlet
```
