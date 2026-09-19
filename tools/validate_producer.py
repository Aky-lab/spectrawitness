"""Generate exact test inputs and kernel-compile their emitted certificates.

Uses an already-built SpectralGraph .validation tree and an existing read-only
mathlib package cache. Never runs Lake. All generated input, Lean, log, object,
and report files stay under this project's .validation/producer directory.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True
from certify_matrix import diagonalize, emit, identity, load_matrix, multiply, transpose


def congruence_case(name, weights):
    """An explicitly unit-triangular basis preserves known diagonal inertia."""
    n = len(weights)
    basis = identity(n)
    for i in range(n):
        for j in range(i + 1, n):
            basis[i][j] = F(((i + 2) * (j + 1)) % 5 - 2, 2 + (j-i) % 3)
    diagonal = [[F(weights[i]) if i == j else F() for j in range(n)] for i in range(n)]
    matrix = multiply(multiply(transpose(basis), diagonal), basis)
    target = (sum(x > 0 for x in weights), sum(x == 0 for x in weights), sum(x < 0 for x in weights))
    return name, matrix, target, 'unit-triangular congruence of known diagonal'


def suite():
    # Every diagonal entry vanishes: diagonal-only pivot discovery would fail.
    hyperbolic = [[F() for _ in range(4)] for _ in range(4)]
    hyperbolic[0][2] = hyperbolic[2][0] = F(3, 7)
    hyperbolic[1][3] = hyperbolic[3][1] = F(-5, 2)
    yield 'hyperbolic4', hyperbolic, (2, 0, 2), 'two independent nonzero hyperbolic planes'
    yield congruence_case('singular5', [F(2, 3), -2, 0, 0, 5])
    # Three identical 2x2 blocks each have trace 1 and determinant -2:
    # actual repeated eigenvalues 2 and -1, not just repeated sign counts.
    repeated = [[F() for _ in range(6)] for _ in range(6)]
    for i in range(0, 6, 2):
        repeated[i][i], repeated[i+1][i+1] = F(2, 25), F(23, 25)
        repeated[i][i+1] = repeated[i+1][i] = F(36, 25)
    yield 'repeated_roots6', repeated, (3, 0, 3), 'three rational orthogonal conjugates of diag(2,-1)'
    yield congruence_case('semidefinite7', [1, 0, F(3, 4), 0, 2, 0, 2])
    yield congruence_case('indefinite8', [1, -1, F(1, 2), 0, -3, 0, 2, -3])


def scalability_suite():
    for n in (4, 8, 12, 16, 20):
        weights = [F((1 if i % 2 == 0 else -1) * (1 + i % 3), 1 + i % 2)
                   for i in range(n)]
        yield congruence_case(f'scale{n}', weights)


def corrupt_field(source, field, value='0'):
    """Replace exactly one certificate field without consuming later fields."""
    pattern = rf'(?ms)^  {re.escape(field)} := .*?(?=^  [A-Za-z][A-Za-z0-9_]* :=|\n\n)'
    result, count = re.subn(pattern, f'  {field} := {value}\n', source)
    if count != 1:
        raise ValueError(f'Expected exactly one certificate field: {field}')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', required=True, type=Path)
    parser.add_argument('--packages', required=True, type=Path)
    parser.add_argument('--timeout', type=int, default=180, help='Seconds per Lean process')
    parser.add_argument('--scalability', action='store_true',
                        help='Instead run orders 4,8,12,16,20; stop after the first failure/timeout')
    parser.add_argument('--format', choices=('congruence', 'product'), default='congruence')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    local = root/'.validation'
    if not (local/'SpectralGraph/Certificate/Basic.olean').is_file():
        parser.error('Build the library first; .validation/SpectralGraph/Certificate/Basic.olean is required')
    if args.format == 'product' and not (local/'SpectralGraph/Certificate/ProductInertia.olean').is_file():
        parser.error('Build Certificate/ProductInertia first for product-format validation')
    if not args.lean.is_file() or not args.packages.is_dir() or args.timeout <= 0:
        parser.error('Provide existing Lean/package paths and a positive timeout')
    output_base = local/'producer'
    output_base.mkdir(parents=True, exist_ok=True)
    output = Path(tempfile.mkdtemp(prefix='roundtrip-', dir=output_base))
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join([str(local)] +
        [str(p/'.lake/build/lib/lean') for p in sorted(args.packages.resolve().iterdir()) if p.is_dir()])
    results = []
    started = time.monotonic()

    def compile_case(name, source, expected_accept):
        lean_file = output/(name+'.lean')
        lean_file.write_text(source, encoding='utf-8', newline='\n')
        begin = time.monotonic()
        timed_out, returncode = False, None
        try:
            run = subprocess.run([str(args.lean.resolve()), '-o', str(output/(name+'.olean')),
                                  str(lean_file.relative_to(root))], cwd=root, env=env,
                                 encoding='utf-8', stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                 timeout=args.timeout)
            accepted = run.returncode == 0
            returncode = run.returncode
            log = run.stdout
            # Require rejection at the actual checker obligation. A compiler
            # crash, syntax error, or unrelated elaboration error is not evidence.
            expected = accepted if expected_accept else (
                run.returncode == 1 and 'error:' in log and 'certificate.check input = true' in log)
        except subprocess.TimeoutExpired as exc:
            timed_out = True
            accepted, expected = False, False
            partial = exc.stdout or ''
            log = (partial.decode('utf-8', errors='replace') if isinstance(partial, bytes) else partial)
            log += '\nVALIDATOR TIMEOUT\n'
        elapsed = round(time.monotonic() - begin, 3)
        (output/(name+'.log')).write_text(log, encoding='utf-8')
        item = {'case': name, 'expected_accept': expected_accept, 'accepted': accepted,
                'pass': expected, 'seconds': elapsed,
                'timed_out': timed_out, 'returncode': returncode,
                'lean_sha256': hashlib.sha256(source.encode()).hexdigest()}
        results.append(item)
        print(f'{name}: {"PASS" if expected else "FAIL"} ({elapsed}s)', flush=True)
        if not expected:
            print(log, flush=True)
        return expected

    skipped = []
    cases = list(scalability_suite() if args.scalability else suite())
    if args.format == 'product' and not args.scalability:
        cases.insert(0, ('empty0', [], (0, 0, 0), 'zero-dimensional space'))
    for position, (name, matrix, target, oracle) in enumerate(cases):
        generation_start = time.monotonic()
        raw = (json.dumps({'matrix': [[str(x) for x in row] for row in matrix]}, indent=2)+'\n').encode()
        (output/(name+'.json')).write_bytes(raw)
        decoded = load_matrix(raw)
        if diagonalize(decoded)[2] != target:
            raise RuntimeError(f'Producer disagrees with independent known-inertia construction: {name}')
        source = emit(decoded, hashlib.sha256(raw).hexdigest(), format=args.format)
        source += ('\nexample : SpectralGraph.matrixInertia '
                   '(SpectralGraph.Certificate.ratCastMatrix GeneratedCertificate.input) = '
                   f'⟨{target[0]}, {target[1]}, {target[2]}⟩ := GeneratedCertificate.inertia\n')
        generation_seconds = round(time.monotonic() - generation_start, 3)
        passed = compile_case(name, source, True)
        results[-1].update({'order': len(matrix), 'expected_inertia': target, 'oracle': oracle,
                           'generation_seconds': generation_seconds,
                           'lean_bytes': len(source.encode()),
                           'max_input_numerator_bits': max((x.numerator.bit_length() for row in matrix for x in row), default=0),
                           'max_input_denominator_bits': max((x.denominator.bit_length() for row in matrix for x in row), default=0)})
        if args.scalability and not passed:
            skipped = [case[0] for case in cases[position+1:]]
            print('Stopped scalability sweep; unattempted: ' + ', '.join(skipped), flush=True)
            break

    if not args.scalability:
        small = emit([[F(0), F(1)], [F(1), F(0)]], '0'*64, format=args.format)
        # Mutate both target and theorem conclusion so rejection exercises the
        # checker, rather than just a mismatch between their displayed types.
        compile_case('reject_wrong_target', small.replace('⟨1, 0, 1⟩', '⟨2, 0, 0⟩'), False)
        compile_case('reject_wrong_inverse', corrupt_field(small, 'inverse'), False)
        if args.format == 'product':
            compile_case('reject_wrong_image', corrupt_field(small, 'image'), False)
            compile_case('reject_wrong_diagonal', corrupt_field(small, 'diagonal'), False)
    report = {'pass': all(r['pass'] for r in results),
              'seconds': round(time.monotonic()-started, 3),
              'trust_boundary': 'Every accepted theorem uses decide +kernel; Python is only a producer.',
              'mode': 'scalability' if args.scalability else 'correctness',
              'format': args.format,
              'timeout_seconds': args.timeout,
              'skipped_after_failure': skipped,
              'cases': results}
    (output/'report.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(f'Report: {output / "report.json"}', flush=True)
    return 0 if report['pass'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
