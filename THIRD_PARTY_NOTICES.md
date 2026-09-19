# Third-party dependencies

The source export does not vendor dependency checkouts. Lake obtains the pinned
packages below from their upstream repositories. Their licenses apply to those
packages, not as substitutes for SpectraWitness's Apache-2.0 license.

| Package | Revision | License | Source |
| --- | --- | --- | --- |
| mathlib | `c5ea00351c28e24afc9f0f84379aa41082b1188f` | Apache-2.0 | https://github.com/leanprover-community/mathlib4 |
| plausible | `a456461b368b71d2accd95234832cd9c174b5437` | Apache-2.0 | https://github.com/leanprover-community/plausible |
| LeanSearchClient | `c5d5b8fe6e5158def25cd28eb94e4141ad97c843` | Apache-2.0 | https://github.com/leanprover-community/LeanSearchClient |
| importGraph | `515cf9d0c00ece5e661f6de4326a53dedc1e8ea1` | Apache-2.0 | https://github.com/leanprover-community/import-graph |
| proofwidgets | `a84b3e2475d5c5ab979567b1ad8aea21b764bcf8` | Apache-2.0 | https://github.com/leanprover-community/ProofWidgets4 |
| aesop | `558915ae105bfd8074e22d597613d1961822adc2` | Apache-2.0 | https://github.com/leanprover-community/aesop |
| Qq | `a6e6c34c4ef182f83b219a3a5a385f51f44bdc4c` | Apache-2.0 | https://github.com/leanprover-community/quote4 |
| batteries | `32dc18cde3684679f3c003de608743b57498c56f` | Apache-2.0 | https://github.com/leanprover-community/batteries |
| Cli | `6b907cf12b2e445ccb7c24bc208ef04a1f39e84c` | MIT | https://github.com/leanprover/lean4-cli |

These revisions are recorded in `lake-manifest.json`. The listed upstream roots
contained no `NOTICE` file at the inspected revisions. Consult each dependency's
repository for its complete license text and any attribution that applies when
redistributing that dependency. This inventory covers the nine pinned Lake
packages at their root license level; it is not a claim about every asset or
nested component that an upstream package may obtain separately.

Documentary source relationships for package files are recorded separately in
the `PROVENANCE*.json` files. Those records describe adaptations within the
Apache-2.0-licensed package and are not runtime dependency listings.
