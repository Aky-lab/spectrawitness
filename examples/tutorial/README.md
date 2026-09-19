# From a triangle to a checked spectral statement

This tutorial certifies two eigenvalue counts for the triangle graph, then
shows Lean rejecting a deliberately incorrect count. Python proposes the
certificate; Lean checks the resulting theorem.

## 1. Install and build

You need Git, Python 3, and Lean's `elan` toolchain manager. Install Lean using
the [official instructions](https://lean-lang.org/install/). The repository's
`lean-toolchain` selects Lean 4.30.0. On systems where Python is named `python3`,
use that instead of `python` below. No Python packages are required.

```text
git clone https://github.com/Aky-lab/spectrawitness.git
cd spectrawitness
lake exe cache get
lake build
```

The first run downloads dependencies and compiled mathlib artifacts; allow
several minutes and several gigabytes of disk space. Keep `lake-manifest.json`
to use the checked dependency revisions. Run the remaining commands from this
repository root. The package name is `spectral_graph` and the Lean namespace is
`SpectralGraph`, even though the project is called SpectraWitness.

## 2. Describe the graph and questions

Open [`triangle.json`](triangle.json):

```json
{
  "rows": [6, 4, 0],
  "queries": [
    {"kind": "count", "lower": -2, "upper": -1},
    {"kind": "count", "lower": -1, "upper": 2}
  ]
}
```

Vertices are numbered 0, 1, 2. Each row stores edges to higher-numbered
vertices as bits: 6 = 2 + 4 records edges 0--1 and 0--2, and 4 in the second
row records 1--2. The last row is zero. Together these encode a triangle.

Each query asks how many adjacency eigenvalues, counted with multiplicity,
lie in the interval `(lower, upper]`: the lower endpoint is excluded and the
upper endpoint is included. The expected answers are **2 in (-2, -1]** and
**1 in (-1, 2]**. The triangle's familiar spectrum is -1, -1, 2; that knowledge
helps interpret the example but is not trusted by the checker. These two
queries prove interval counts, not by themselves the exact spectrum.

## 3. Generate and check the report

```text
python tools/certify_graph.py examples/tutorial/triangle.json .validation-tutorial/Triangle.lean --namespace Tutorial.Triangle --graph-module SpectralGraphTests.GraphReports.IndependentGraphs --graph-name SpectralGraphTests.GraphReports.IndependentGraphs.completeThree
lake env lean .validation-tutorial/Triangle.lean
```

The producer prints `Wrote ...; compile to verify`. The Lean command should
exit successfully; it may print nothing. Generation alone is not verification.
The output path must be new: on a second run choose another filename.

The named-graph arguments bind the encoded rows to `completeThree`, defined
independently as the complete simple graph on three vertices in the example
support module. Lean checks this equality in `graph_matches`; it does not
merely accept a graph name written in a comment.

Look inside the generated file:

- `rows_valid` checks the packed graph representation.
- `graph_matches` proves that the encoded graph is the named triangle.
- `inertia_0`, `inertia_1`, and `inertia_2` certify shifted adjacency matrices
  at -2, -1, and 2. Inertia triples mean positive, zero, negative counts.
- `query_0` proves the first eigenvalue count is 2; `query_1` proves the
  second count is 1, using the library's inertia-to-spectrum theorem.

## 4. Check that a false claim is rejected

Make a separate copy that claims the first count is 3 instead of 2:

```text
python -c "from pathlib import Path; p=Path('.validation-tutorial/Triangle.lean'); s=p.read_text(encoding='utf-8'); old='.card = 2 := by'; assert s.count(old)==1; Path('.validation-tutorial/FalseTriangle.lean').write_text(s.replace(old,'.card = 3 := by'),encoding='utf-8')"
lake env lean .validation-tutorial/FalseTriangle.lean
```

**The final command is supposed to fail with a nonzero exit code.** Lean
should report that the `decide` tactic found the count equality false. This
is the successful negative check, not an installation failure. A missing
import or missing-file error does not count as the expected rejection.

The original `Triangle.lean` remains valid. The experiment demonstrates that
editing a claimed answer in the generated report cannot make Lean accept it.
It does not establish the absence of all possible bugs; soundness depends on
the stated theorems and Lean's trusted kernel and standard axioms.

## Next example

[`../graph_reports/p5.json`](../graph_reports/p5.json) describes a five-vertex
path and includes an exact rational bracket for its largest adjacency
eigenvalue. Generate it with a new output filename and compile it in the same
way. See the [graph-report guide](../graph_reports/README.md) for input rules.
