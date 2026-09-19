import unittest
import random
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from fractions import Fraction
from certify_matrix import load_matrix, read_matrix, diagonalize, multiply, transpose, identity, emit
from validate_producer import corrupt_field

class CertificateProducerTests(unittest.TestCase):
    def test_malformed(self):
        for data in [[], {}, {'matrix': [[1, 0]]}, {'matrix': [[0, 1], [0, 0]]},
                     {'matrix': [[True]]}, {'matrix': [[0.5]]}, {'matrix': [['1/0']]},
                     {'matrix': [['1); axiom evil : False']]}, {'matrix': [], 'extra': 1}]:
            with self.subTest(data=data), self.assertRaises(ValueError):
                read_matrix(data)

    def test_zero_hyperbolic_and_fractional(self):
        for raw, target in [([], (0, 0, 0)), ([[0]], (0, 1, 0)),
                            ([[0, '3/7'], ['3/7', 0]], (1, 0, 1))]:
            self.assertEqual(diagonalize(read_matrix({'matrix': raw}))[2], target)

    def test_congruence_constructed_families(self):
        rng = random.Random(9122026)
        for n in range(1, 9):
            for case in range(12):
                # An invertible triangular P supplies an independent known inertia.
                p = identity(n)
                for i in range(n):
                    for j in range(i+1, n):
                        p[i][j] = Fraction(rng.randrange(-3, 4), rng.randrange(1, 5))
                weights = [Fraction(rng.randrange(-2, 3)) for _ in range(n)]
                d = [[weights[i] if i == j else Fraction() for j in range(n)] for i in range(n)]
                a = multiply(multiply(transpose(p), d), p)
                expected = (sum(x > 0 for x in weights), sum(x == 0 for x in weights), sum(x < 0 for x in weights))
                with self.subTest(n=n, case=case):
                    self.assertEqual(diagonalize(a)[2], expected)

    def test_emits_kernel_boundary(self):
        out = emit(read_matrix({'matrix': [[0, 1], [1, 0]]}), '0'*64)
        self.assertIn('certificate.sound input (by decide +kernel)', out)
        self.assertNotIn('native_decide', out)

    def test_json_syntax_boundary(self):
        for raw in ['{"matrix": [[1]], "matrix": [[-1]]}',
                    '{"matrix": [[NaN]]}', '{"matrix": [[Infinity]]}',
                    '{"matrix": [[-Infinity]]}', '{"matrix": [[1.0]]}',
                    '{"matrix": [[1e0]]}', '{"matrix": [[null]]}',
                    '{"matrix": [[" 1"]]}', '{"matrix": [["1/2 "]]}',
                    '{"matrix": [["1/-2"]]}', '{"matrix": [["1/+2"]]}',
                    '{"matrix": [["١"]]}', '{"matrix": [["1\\n"]]}',
                    '{"matrix": [[1]]} {"matrix": [[2]]}']:
            with self.subTest(raw=raw), self.assertRaises(ValueError):
                load_matrix(raw)
        self.assertEqual(load_matrix('{"matrix": [["+6/8"]]}'), [[Fraction(3, 4)]])

    def test_comment_injection_rejected(self):
        for source_hash in ['0'*63, 'g'*64, '0'*64 + '\n-/\naxiom evil : False', None]:
            with self.subTest(source_hash=source_hash), self.assertRaises(ValueError):
                emit([[Fraction(1)]], source_hash)

    def test_namespace_validation(self):
        matrix = [[Fraction(1)]]
        for namespace in ['by', 'Type', 'Examples.Prop', 'X\naxiom Evil : False', 'X;Y', '«X»']:
            with self.subTest(namespace=namespace), self.assertRaises(ValueError):
                emit(matrix, '0'*64, namespace)
        output = emit(matrix, '0'*64, 'Examples.Certificate17')
        self.assertIn('namespace Examples.Certificate17\n', output)
        self.assertIn('end Examples.Certificate17\n', output)

    def test_product_format(self):
        matrix = [[Fraction(2), Fraction()], [Fraction(), Fraction(-3)]]
        output = emit(matrix, '0'*64, format='product')
        self.assertIn('import SpectralGraph.Certificate.ProductInertia', output)
        self.assertIn('certificate : ProductInertiaCertificate (Fin 2)', output)
        self.assertIn('  image := !![2, 0;\n    0, -3]', output)
        self.assertIn('  diagonal := ![2, -3]', output)
        self.assertIn('certificate.sound input (by decide +kernel)', output)
        self.assertEqual(emit(matrix, '0'*64), emit(matrix, '0'*64, format='congruence'))
        self.assertNotIn('  image :=', emit(matrix, '0'*64))
        self.assertIn('  diagonal := fun i => Fin.elim0 i', emit([], '0'*64, format='product'))
        with self.assertRaises(ValueError):
            emit(matrix, '0'*64, format='product\naxiom Evil : False')

    def test_corruption_preserves_other_fields(self):
        output = emit([[Fraction(2)]], '0'*64, format='product')
        inverse = corrupt_field(output, 'inverse')
        self.assertIn('  inverse := 0\n  image := !![2]\n  diagonal := ![2]', inverse)
        image = corrupt_field(output, 'image')
        self.assertIn('  inverse := !![1]\n  image := 0\n  diagonal := ![2]', image)
        diagonal = corrupt_field(output, 'diagonal')
        self.assertIn('  image := !![2]\n  diagonal := 0\n  target := ⟨1, 0, 0⟩', diagonal)
        with self.assertRaises(ValueError):
            corrupt_field(output, 'nonexistent')

    def test_independent_matrix_binding(self):
        a = [[Fraction(1)]]
        for fmt in ('congruence', 'product'):
            output = emit(a, '0'*64, format=fmt, matrix_module='Research.Matrices',
                          matrix_name='Research.actualMatrix')
            self.assertIn('import Research.Matrices\n', output)
            self.assertIn('def input : Matrix (Fin 1) (Fin 1) ℚ := _root_.Research.actualMatrix\n', output)
            self.assertIn('certificate.sound input (by decide +kernel)', output)
        for module, name in [('Research', None), (None, 'Research.matrix'),
                             ('Research\naxiom Evil : False', 'Research.matrix'),
                             ('Research', 'Research.matrix + 0'), ('Research', 'by'),
                             ('Research', 'Research.matrix\nend X'), ('../Research', 'Research.matrix')]:
            with self.subTest(module=module, name=name), self.assertRaises(ValueError):
                emit(a, '0'*64, matrix_module=module, matrix_name=name)

    def test_cli_preserves_existing_outputs_and_input(self):
        root = Path(__file__).resolve().parents[1] / '.validation'
        root.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='producer-unit-', dir=root) as temp:
            directory = Path(temp)
            source, target = directory/'input.json', directory/'output.lean'
            raw = b'{"matrix": [[0, "1/2"], ["1/2", 0]]}'
            source.write_bytes(raw)
            env = os.environ.copy()
            env['PYTHONDONTWRITEBYTECODE'] = '1'
            def run(output, *options):
                return subprocess.run([sys.executable, str(Path(__file__).with_name('certify_matrix.py')),
                                       str(source), str(output), *options], env=env,
                                      capture_output=True, text=True)
            first = run(target)
            self.assertEqual(first.returncode, 0, first.stderr)
            original = target.read_bytes()
            self.assertIn(hashlib.sha256(raw).hexdigest().encode(), original)
            product_target = directory/'product.lean'
            self.assertEqual(run(product_target, '--format', 'product').returncode, 0)
            self.assertIn('ProductInertiaCertificate', product_target.read_text(encoding='utf-8'))
            second = run(target)
            self.assertNotEqual(second.returncode, 0)
            self.assertNotIn('Traceback', second.stderr)
            self.assertEqual(target.read_bytes(), original)
            self.assertNotEqual(run(source).returncode, 0)
            self.assertEqual(source.read_bytes(), raw)
            source.write_text('{"matrix": [], "matrix": [[1]]}', encoding='utf-8')
            rejected = directory/'rejected.lean'
            self.assertNotEqual(run(rejected).returncode, 0)
            self.assertFalse(rejected.exists())

if __name__ == '__main__':
    unittest.main()
