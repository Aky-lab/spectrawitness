"""Deterministic exact fixtures for the weighted endpoint-edge application.

This is deliberately an application-local producer.  Its output is untrusted
until the emitted arrays are bound to the independently defined Lean matrix.
All arithmetic uses :class:`fractions.Fraction`; no floating point is used.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction as F
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from certify_matrix import diagonalize, identity, multiply, transpose  # noqa: E402


def path_laplacian(n: int):
    """Unit-weight path Laplacian, with vertices numbered 0,...,n-1."""
    a = [[F(0) for _ in range(n)] for _ in range(n)]
    for i in range(n - 1):
        a[i][i] += 1
        a[i + 1][i + 1] += 1
        a[i][i + 1] -= 1
        a[i + 1][i] -= 1
    return a


def outer(u):
    return [[x * y for y in u] for x in u]


def add(a, b):
    return [[x + y for x, y in zip(ra, rb)] for ra, rb in zip(a, b)]


def scale(a, c):
    return [[c * x for x in row] for row in a]


def matvec(a, x):
    return [sum((a[i][j] * x[j] for j in range(len(x))), F(0)) for i in range(len(a))]


def inverse(a):
    n = len(a)
    aug = [row[:] + identity(n)[i] for i, row in enumerate(a)]
    for j in range(n):
        pivot = next((i for i in range(j, n) if aug[i][j]), None)
        if pivot is None:
            raise ValueError("singular matrix")
        aug[j], aug[pivot] = aug[pivot], aug[j]
        q = aug[j][j]
        aug[j] = [x / q for x in aug[j]]
        for i in range(n):
            if i != j and aug[i][j]:
                q = aug[i][j]
                aug[i] = [x - q * y for x, y in zip(aug[i], aug[j])]
    return [row[n:] for row in aug]


def qjson(x):
    return int(x) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def encode_matrix(a):
    return [[qjson(x) for x in row] for row in a]


def encode_vector(x):
    return [qjson(v) for v in x]


def application_case(n: int, c_factor: F):
    t = F(16, n * n)
    u = [F(i == 0) - F(i == n - 1) for i in range(n)]
    base = add(path_laplacian(n), scale(identity(n), -t))
    inv = inverse(base)
    solve_u = matvec(inv, u)
    v = sum((u[i] * solve_u[i] for i in range(n)), F(0))
    cstar = -F(1, 1) / v
    c = c_factor * cstar
    matrix = add(base, scale(outer(u), c))
    target = diagonalize(matrix)[2]
    return {
        "n": n, "threshold": qjson(t), "c_factor": qjson(c_factor),
        "c": qjson(c), "c_star": qjson(cstar), "u": encode_vector(u),
        "matrix": encode_matrix(matrix), "base_matrix": encode_matrix(base),
        "base_inverse": encode_matrix(inv), "solve_u": encode_vector(solve_u),
        "inverse_quadratic": qjson(v), "inertia": list(target),
    }


def witness_case(n=8):
    """A c*/2 matrix and a rectangular, non-coordinate two-column witness."""
    case = application_case(n, F(1, 2))
    a = [[F(x) for x in row] for row in case["matrix"]]
    # Both columns are non-coordinate vectors; W is intentionally rectangular-safe.
    # The constant mode and the centred linear mode span a strictly negative
    # plane for this below-transition matrix.  The scale 2*i-(n-1) makes the
    # cross term exactly zero, matching the diagonal-d checker route.
    u = [[F(1), F(2 * i - (n - 1))] for i in range(n)]
    w = [[sum((a[i][j] * u[j][k] for j in range(n)), F(0)) for k in range(2)] for i in range(n)]
    gram = [[sum((u[i][r] * w[i][s] for i in range(n)), F(0)) for s in range(2)] for r in range(2)]
    case.update({"witness": {"k": 2, "U": encode_matrix(u), "W": encode_matrix(w),
                              "gram": encode_matrix(gram),
                              "gram_inertia": list(diagonalize(gram)[2])}})
    return case


def generate(destination: Path):
    destination.mkdir(parents=True, exist_ok=True)
    cases = {}
    for n in (6, 8, 12):
        for label, factor in (("zero", F(0)), ("half", F(1, 2)),
                              ("star", F(1)), ("double", F(2))):
            cases[f"n{n}_{label}"] = application_case(n, factor)
    for n in (6, 8, 12):
        cases[f"n{n}_half_witness"] = witness_case(n)
    manifest = {"schema": "weighted-path-application-v1", "cases": {}}
    for name, value in cases.items():
        raw = (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()
        path = destination / f"{name}.json"
        path.write_bytes(raw)
        manifest["cases"][name] = {"sha256": hashlib.sha256(raw).hexdigest(),
                                     "bytes": len(raw)}
    (destination / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return cases


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1] / "examples" / "application")
    args = parser.parse_args()
    cases = generate(args.output)
    print(f"generated {len(cases)} deterministic application fixtures in {args.output}")


if __name__ == "__main__":
    main()
