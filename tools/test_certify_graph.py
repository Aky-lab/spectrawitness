"""Fast exact-input and file-boundary tests for certify_graph.

The kernel roundtrips are in validate_graph_reports.py; this module never
substitutes Python's discovery for Lean verification.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
from certify_graph import discover, emit, load_graph


TOOL = Path(__file__).with_name('certify_graph.py')
SCRATCH = Path(__file__).resolve().parents[1] / '.validation' / 'graph-input-tests'


def raw(rows, queries):
    return (json.dumps({'rows': rows, 'queries': queries}, separators=(',', ':')) + '\n').encode()


def count(lower=-2, upper=-1):
    return {'kind': 'count', 'lower': lower, 'upper': upper}


def bracket(lower=-2, upper=-1, index=1):
    return {'kind': 'bracket', 'lower': lower, 'upper': upper, 'index': index}


class GraphInputTests(unittest.TestCase):
    def test_canonical_endpoint_reuse_and_nearby_distinction(self):
        blob = raw([6, 4, 0], [count(-2, -1), count('-4/2', '-2/2'),
                                count('-6/3', '-1001/1000')])
        graph = load_graph(blob)
        self.assertEqual(len(graph.queries), 3)
        self.assertEqual(graph.queries[0].lower, graph.queries[1].lower)
        self.assertEqual(graph.queries[1].lower, graph.queries[2].lower)
        self.assertNotEqual(graph.queries[1].upper, graph.queries[2].upper)
        source = emit(graph, discover(graph), hashlib.sha256(blob).hexdigest())
        self.assertEqual(source.count('checkAdjacencyInertiaAt_sound'), 3)
        self.assertIn('endpoint_0', source)
        self.assertIn('query_2', source)

    def test_valid_boundary_graphs(self):
        for rows, queries in [([], [count(-1, 0)]), ([0], [count(-1, 0)]),
                              ([2, 0], [bracket(0, 1, 0)]),
                              ([0, 1], [bracket(0, 1, 0)]),
                              ([2, 1], [bracket(0, 1, 0)])]:
            with self.subTest(rows=rows):
                graph = load_graph(raw(rows, queries))
                emit(graph, discover(graph), '0' * 64)

    def test_reject_bad_json_and_schema(self):
        bad = [b'', b'\xff', b'{}', b'[]', b'null', b'NaN',
               b'{"rows":[],"queries":[],"rows":[]}',
               b'{"rows":[],"queries":[{"kind":"count","lower":0,"upper":1,"upper":2}]}',
               b'{"rows":[],"queries":[],"extra":0}',
               b'{"rows":[],"queries":[{"kind":"count","lower":0}]}',
               b'{"rows":[],"queries":[{"kind":"other","lower":0,"upper":1}]}',
               b'{"rows":[],"queries":[{"kind":"count","lower":0,"upper":1,"index":0}]}',
               b'{"rows":[],"queries":[{"kind":"bracket","lower":0,"upper":1}]}',
               b'{"rows":[],"queries":[{"kind":"count","lower":NaN,"upper":1}]}',
               b'{"rows":[],"queries":[{"kind":"count","lower":Infinity,"upper":1}]}',
               b'{"rows":[],"queries":[{"kind":"count","lower":0,"upper":1}]} trailing']
        for blob in bad:
            with self.subTest(blob=blob), self.assertRaises(ValueError):
                load_graph(blob)

    def test_reject_rows_and_order(self):
        cases = [([True], [count()]), ([0.0], [count()]), ([-1], [count()]),
                 (['0'], [count()]), ([2], [count()]), ([1], [count()]),
                 ([0, 4], [count()]), ([0, 2], [count()]),
                 ([0] * 13, [count()])]
        for rows, queries in cases:
            with self.subTest(rows=rows), self.assertRaises(ValueError):
                load_graph(raw(rows, queries))

    def test_reject_query_types_bounds_and_caps(self):
        cases = [([0], []), ([0], [count()] * 33),
                 ([0], [count(2, 1)]), ([0], [bracket(-1, 1, True)]),
                 ([0], [bracket(-1, 1, -1)]), ([0], [bracket(-1, 1, 1)]),
                 ([], [bracket(-1, 1, 0)]), ([0], [bracket(0, 1, 0)]),
                 ([0], [count(True, 1)]), ([0], [count(0.5, 1)]),
                 ([0], [count('1/0', 1)]), ([0], [count('1/-2', 1)]),
                 ([0], [count('1/+2', 1)]), ([0], [count('١', 1)]),
                 ([0], [count(' 1', 2)]), ([0], [count('1\n', 2)]),
                 ([0], [count('1); axiom bad : False', 2)]),
                 ([0], [count(i, i+1) for i in range(17)])]
        for rows, queries in cases:
            with self.subTest(rows=rows, queries=queries), self.assertRaises(ValueError):
                graph = load_graph(raw(rows, queries))
                discover(graph)

    def test_whole_report_rejects_one_false_bracket(self):
        graph = load_graph(raw([6, 4, 0], [count(-2, -1), bracket(0, 1, 2)]))
        with self.assertRaises(ValueError):
            discover(graph)

    def test_emit_validates_hash_and_names(self):
        graph = load_graph(raw([0], [count(-1, 0)]))
        result = discover(graph)
        for digest in ('0' * 63, 'g' * 64, '0' * 64 + '\naxiom bad : False', None):
            with self.subTest(digest=digest), self.assertRaises(ValueError):
                emit(graph, result, digest)
        for namespace in ('by', 'Type', 'A;B', 'A\naxiom bad : False', '«A»'):
            with self.subTest(namespace=namespace), self.assertRaises(ValueError):
                emit(graph, result, '0' * 64, namespace=namespace)
        for module, name in [('A', None), (None, 'A.g'), ('A;B', 'A.g'),
                             ('A', 'A.g + 0'), ('A', 'by'), ('../A', 'A.g')]:
            with self.subTest(module=module, name=name), self.assertRaises(ValueError):
                emit(graph, result, '0' * 64, graph_module=module, graph_name=name)

    def test_cli_exclusive_creation_and_no_partial_output(self):
        SCRATCH.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='fast-', dir=SCRATCH) as temp:
            folder = Path(temp)
            inp, out = folder/'in.json', folder/'out.lean'
            blob = raw([6, 4, 0], [count(-2, -1)])
            inp.write_bytes(blob)
            env = os.environ.copy()
            env['PYTHONDONTWRITEBYTECODE'] = '1'
            def run(target, *options):
                return subprocess.run([sys.executable, str(TOOL), str(inp), str(target), *options],
                                      cwd=TOOL.parent.parent, env=env, text=True,
                                      stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            first = run(out)
            self.assertEqual(first.returncode, 0, first.stderr)
            original = out.read_bytes()
            self.assertIn(hashlib.sha256(blob).hexdigest().encode(), original)
            again = run(out)
            self.assertNotEqual(again.returncode, 0)
            self.assertEqual(out.read_bytes(), original)
            self.assertNotEqual(run(inp).returncode, 0)
            self.assertEqual(inp.read_bytes(), blob)
            for options in [('--graph-module', 'A'), ('--graph-name', 'A.g'),
                            ('--namespace', 'A\naxiom bad : False')]:
                rejected = folder/('reject' + str(len(list(folder.iterdir()))) + '.lean')
                self.assertNotEqual(run(rejected, *options).returncode, 0)
                self.assertFalse(rejected.exists())
            inp.write_bytes(raw([6, 4, 0], [count(-2, -1), bracket(0, 1, 2)]))
            rejected = folder/'false.lean'
            self.assertNotEqual(run(rejected).returncode, 0)
            self.assertFalse(rejected.exists())


if __name__ == '__main__':
    unittest.main()
