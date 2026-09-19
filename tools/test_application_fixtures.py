import json
import sys
import tempfile
import unittest
from fractions import Fraction as F
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from application_fixtures import (application_case, generate, matvec, path_laplacian,
                                  witness_case)
from certify_matrix import diagonalize


class WeightedPathApplicationTests(unittest.TestCase):
    def test_candidate_crossings_and_inertia(self):
        expected = {6: (F(-2169, 329), F(329, 2169)),
                    8: (F(-2008, 223), F(223, 2008)),
                    12: (F(-3072159, 225679), F(225679, 3072159))}
        for n, (v, cstar) in expected.items():
            for factor, inertia in ((F(0), (n-2, 0, 2)), (F(1, 2), (n-2, 0, 2)),
                                    (F(1), (n-2, 1, 1)), (F(2), (n-1, 0, 1))):
                case = application_case(n, factor)
                self.assertEqual(F(case["inverse_quadratic"]), v)
                self.assertEqual(F(case["c_star"]), cstar)
                self.assertEqual(tuple(case["inertia"]), inertia)

    def test_inverse_and_solve_are_exact(self):
        for n in (6, 8, 12):
            case = application_case(n, F(1, 2))
            a = [[F(x) for x in row] for row in case["base_matrix"]]
            inv = [[F(x) for x in row] for row in case["base_inverse"]]
            u = [F(x) for x in case["u"]]
            self.assertEqual(matvec(a, [sum(inv[i][j] * u[j] for j in range(n)) for i in range(n)]), u)
            self.assertEqual(matvec(inv, matvec(a, [F(i == 0) for i in range(n)])), [F(i == 0) for i in range(n)])

    def test_rectangular_supplied_image_and_negative_subspace(self):
        expected = {6: (F(-8, 3), F(-850, 241)), 8: (F(-2), F(-3129, 1004)),
                    12: (F(-4, 3), F(-5463458, 3072159))}
        for n, ds in expected.items():
            case = witness_case(n)
            U = [[F(x) for x in row] for row in case["witness"]["U"]]
            W = [[F(x) for x in row] for row in case["witness"]["W"]]
            A = [[F(x) for x in row] for row in case["matrix"]]
            self.assertEqual([[sum(A[i][j] * U[j][k] for j in range(n)) for k in range(2)] for i in range(n)], W)
            gram = [[sum(U[i][r] * W[i][s] for i in range(n)) for s in range(2)] for r in range(2)]
            self.assertEqual(gram, [[ds[0], F(0)], [F(0), ds[1]]])
            self.assertEqual(diagonalize(gram)[2], (0, 0, 2))
            self.assertEqual(len(U), n)
            self.assertEqual(len(U[0]), len(W[0]), 2)

    def test_generation_is_deterministic_and_has_all_cases(self):
        with tempfile.TemporaryDirectory() as d1, tempfile.TemporaryDirectory() as d2:
            generate(Path(d1)); generate(Path(d2))
            a = {p.name: p.read_bytes() for p in Path(d1).glob('*.json')}
            b = {p.name: p.read_bytes() for p in Path(d2).glob('*.json')}
            self.assertEqual(a, b)
            self.assertEqual(len(a), 16)

    def test_rejections_for_corrupted_application_data(self):
        case = witness_case()
        U = [[F(x) for x in row] for row in case["witness"]["U"]]
        W = [[F(x) for x in row] for row in case["witness"]["W"]]
        W[0][0] += 1
        self.assertNotEqual(W, [[sum(F(x) * U[j][k] for j, x in enumerate(row)) for k in range(2)] for row in case["matrix"]])
        self.assertNotEqual(F(case["c_star"]), F(case["c"]))


if __name__ == '__main__':
    unittest.main()
