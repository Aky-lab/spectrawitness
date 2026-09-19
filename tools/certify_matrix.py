"""Emit a kernel-checkable Lean inertia certificate from an exact JSON matrix.

Input: {"matrix": [[0, "1/2"], ["1/2", 0]]}
Entries are integers or exact integer/fraction strings, never floating point.
The producer is untrusted: the emitted theorem checks all matrix identities.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re

def unique_object(pairs):
    """Reject duplicate keys before a JSON object loses that information."""
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f'Duplicate JSON key: {key!r}')
        result[key] = value
    return result

def reject_constant(value):
    raise ValueError(f'Nonstandard JSON constant is forbidden: {value}')

def load_matrix(raw):
    """Read the strict external schema, including JSON-level validation."""
    return read_matrix(json.loads(raw, object_pairs_hook=unique_object,
                                  parse_constant=reject_constant))

def rational(value):
    if isinstance(value, bool):
        raise ValueError('Boolean entries are not rational numbers')
    if isinstance(value, int):
        return Fraction(value)
    if isinstance(value, str) and re.fullmatch(r'[+-]?[0-9]+(?:/[0-9]+)?', value):
        try:
            return Fraction(value)
        except (ValueError, ZeroDivisionError) as exc:
            raise ValueError('Invalid exact rational entry') from exc
    raise ValueError('Entries must be integers or exact fraction strings; floats are rejected')

def read_matrix(data):
    if not isinstance(data, dict) or set(data) != {'matrix'}:
        raise ValueError('Input must be an object with exactly the key "matrix"')
    rows = data['matrix']
    if not isinstance(rows, list) or any(not isinstance(row, list) or len(row) != len(rows) for row in rows):
        raise ValueError('Matrix must be a square array of rows')
    a = [[rational(x) for x in row] for row in rows]
    if any(a[i][j] != a[j][i] for i in range(len(a)) for j in range(len(a))):
        raise ValueError('Matrix must be symmetric')
    return a

def identity(n):
    return [[Fraction(i == j) for j in range(n)] for i in range(n)]

def multiply(a, b):
    n = len(a)
    return [[sum((a[i][k] * b[k][j] for k in range(n)), Fraction())
             for j in range(n)] for i in range(n)]

def transpose(a):
    return [list(row) for row in zip(*a)]

def diagonalize(a):
    """Exact symmetric elimination carrying a basis and its alleged inverse."""
    n = len(a)
    form = [row[:] for row in a]
    change, inverse = identity(n), identity(n)

    def swap(i, j):
        if i == j:
            return
        form[i], form[j] = form[j], form[i]
        for row in form:
            row[i], row[j] = row[j], row[i]
        for row in change:
            row[i], row[j] = row[j], row[i]
        inverse[i], inverse[j] = inverse[j], inverse[i]

    def add(source, target, c):
        # P <- P E, Q <- E^-1 Q, A <- E^T A E.
        old = [row[:] for row in form]
        for i in range(n):
            for j in range(n):
                form[i][j] = old[i][j] + (c * old[source][j] if i == target else 0) + (c * old[i][source] if j == target else 0) + (c*c*old[source][source] if i == target and j == target else 0)
        for i in range(n):
            change[i][target] += c * change[i][source]
        inverse[source] = [x - c*y for x, y in zip(inverse[source], inverse[target])]

    for k in range(n):
        pivot = next((i for i in range(k, n) if form[i][i]), None)
        if pivot is None:
            pair = next(((i, j) for i in range(k, n) for j in range(i+1, n) if form[i][j]), None)
            if pair is None:
                break
            i, j = pair
            add(j, i, Fraction(1))
            pivot = i
        swap(k, pivot)
        for j in range(k+1, n):
            if form[k][j]:
                add(k, j, -form[k][j] / form[k][k])

    # Producer-side sanity checks are diagnostics, not part of Lean's trust.
    if multiply(inverse, change) != identity(n) or multiply(multiply(transpose(change), a), change) != form:
        raise RuntimeError('Producer failed its exact consistency check')
    if any(form[i][j] for i in range(n) for j in range(n) if i != j):
        raise RuntimeError('Producer did not diagonalize the matrix')
    diagonal = [form[i][i] for i in range(n)]
    target = (sum(x > 0 for x in diagonal), sum(x == 0 for x in diagonal), sum(x < 0 for x in diagonal))
    return change, inverse, target

def lean_fraction(x):
    if x.denominator == 1:
        return str(x.numerator)
    return f'({x.numerator} / {x.denominator})'

def lean_matrix(a):
    if not a:
        return 'fun i => Fin.elim0 i'
    return '!![' + ';\n    '.join(', '.join(lean_fraction(x) for x in row) for row in a) + ']'

def lean_vector(a):
    if not a:
        return 'fun i => Fin.elim0 i'
    return '![' + ', '.join(lean_fraction(x) for x in a) + ']'


def emit(a, source_hash, namespace='GeneratedCertificate', format='congruence',
         matrix_module=None, matrix_name=None):
    # This value is emitted in a Lean comment. Validate even library callers,
    # rather than allowing a crafted hash to close the comment and inject code.
    if not isinstance(source_hash, str) or not re.fullmatch(r'[0-9a-fA-F]{64}', source_hash):
        raise ValueError('Source hash must be exactly 64 hexadecimal characters')
    if (not isinstance(namespace, str) or
            not re.fullmatch(r'[A-Z][A-Za-z0-9_]*(?:\.[A-Z][A-Za-z0-9_]*)*', namespace) or
            any(part in {'Type', 'Sort', 'Prop'} for part in namespace.split('.'))):
        raise ValueError('Namespace must contain dot-separated ASCII identifiers starting with uppercase letters, excluding Type/Sort/Prop')
    if format not in ('congruence', 'product'):
        raise ValueError('Certificate format must be congruence or product')
    if (matrix_module is None) != (matrix_name is None):
        raise ValueError('matrix_module and matrix_name must be supplied together')
    if matrix_module is not None:
        if (not isinstance(matrix_module, str) or
                not re.fullmatch(r'[A-Z][A-Za-z0-9_]*(?:\.[A-Z][A-Za-z0-9_]*)*', matrix_module) or
                any(part in {'Type', 'Sort', 'Prop'} for part in matrix_module.split('.'))):
            raise ValueError('Matrix module must be dot-separated ASCII identifiers starting with uppercase letters')
        reserved = {'by', 'def', 'theorem', 'axiom', 'sorry', 'admit', 'fun', 'let', 'in',
                    'if', 'then', 'else', 'match', 'with', 'where', 'import', 'open',
                    'namespace', 'end', 'instance', 'example', 'structure', 'inductive',
                    'class', 'Type', 'Sort', 'Prop'}
        if (not isinstance(matrix_name, str) or
                not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z][A-Za-z0-9_]*)*', matrix_name) or
                any(part in reserved for part in matrix_name.split('.'))):
            raise ValueError('Matrix name must be a dot-separated ASCII identifier, not a Lean expression')
    p, q, target = diagonalize(a)
    n = len(a)
    module, certificate_type, extra = 'Basic', 'InertiaCertificate', ''
    if format == 'product':
        image = multiply(a, p)
        gram = multiply(transpose(p), image)
        diagonal = [gram[i][i] for i in range(n)]
        module, certificate_type = 'ProductInertia', 'ProductInertiaCertificate'
        extra = f'  image := {lean_matrix(image)}\n  diagonal := {lean_vector(diagonal)}\n'
    independent_import = f'\nimport {matrix_module}' if matrix_module else ''
    input_expression = f'_root_.{matrix_name}' if matrix_name is not None else lean_matrix(a)
    return f'''import SpectralGraph.Certificate.{module}{independent_import}

/- Generated from exact JSON, SHA256 {source_hash}.
The external producer is untrusted; the theorem checks the certificate in Lean.
-/
namespace {namespace}
open SpectralGraph SpectralGraph.Certificate

def input : Matrix (Fin {n}) (Fin {n}) ℚ := {input_expression}

def certificate : {certificate_type} (Fin {n}) where
  change := {lean_matrix(p)}
  inverse := {lean_matrix(q)}
{extra}  target := ⟨{target[0]}, {target[1]}, {target[2]}⟩

theorem inertia : matrixInertia (ratCastMatrix input) = ⟨{target[0]}, {target[1]}, {target[2]}⟩ :=
  certificate.sound input (by decide +kernel)

end {namespace}
'''

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('input', type=Path)
    p.add_argument('output', type=Path)
    p.add_argument('--namespace', default='GeneratedCertificate',
                   help='Use a distinct namespace when importing multiple generated certificates')
    p.add_argument('--format', choices=('congruence', 'product'), default='congruence',
                   help='Product supplies an extra checked intermediate to avoid nested matrix products')
    p.add_argument('--matrix-module', help='Import containing an independently defined Lean matrix (paired with --matrix-name)')
    p.add_argument('--matrix-name', help='Qualified Lean matrix name to certify instead of emitting the JSON matrix')
    args = p.parse_args()
    try:
        raw = args.input.read_bytes()
        a = load_matrix(raw)
        output = emit(a, hashlib.sha256(raw).hexdigest(), args.namespace, args.format,
                      args.matrix_module, args.matrix_name)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        # Exclusive creation also protects input=output and existing symlinks.
        with args.output.open('x', encoding='utf-8', newline='\n') as f:
            f.write(output)
    except (ValueError, RuntimeError, OSError) as exc:
        p.error(str(exc))
    print(f'Wrote {args.output}: order {len(a)} (compile the emitted theorem to verify)')

if __name__ == '__main__':
    main()
