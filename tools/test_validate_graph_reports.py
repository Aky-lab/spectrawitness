"""Unit tests for negative-outcome classification without launching Lean."""
import unittest

from validate_graph_reports import classify, lean_version_matches


class OutcomeClassificationTests(unittest.TestCase):
    def test_accept_is_clean_exit_only(self):
        self.assertTrue(classify(0, '', 'accept', False))
        self.assertFalse(classify(0, 'error: hidden', 'accept', False))
        self.assertFalse(classify(1, '', 'accept', False))

    def test_rejection_requires_exact_obligation_and_ordinary_exit(self):
        good = 'Case.lean:12:1: error: Tactic `decide` proved that the proposition\n  packedRowsValid 3 rows = true\nis false'
        self.assertTrue(classify(1, good, 'storage', False))
        self.assertFalse(classify(2, good, 'storage', False))
        self.assertFalse(classify(-11, good, 'storage', False, True))
        self.assertFalse(classify(1, good, 'storage', True))
        self.assertFalse(classify(1, good, 'query', False))
        self.assertFalse(classify(1, 'Case.lean:12:1: error: unrelated proof failed',
                                  'storage', False))

    def test_parser_import_crash_and_timeout_are_not_negative_passes(self):
        cases = [
            ('error: unknown module prefix SpectralGraph', 'endpoint'),
            ('error: unexpected token\n⊢ checkAdjacencyInertiaAt', 'endpoint'),
            ('error: parser error\n⊢ query_0', 'query'),
            ('error: unknown constant emittedGraph', 'equality'),
            ('error: failed to load object\n⊢ packedRowsValid', 'storage'),
            ('error: stack overflow\n⊢ checkAdjacencyInertiaAt', 'endpoint'),
        ]
        for log, expected in cases:
            with self.subTest(log=log):
                self.assertFalse(classify(1, log, expected, False))
        self.assertFalse(classify(None, 'VALIDATOR TIMEOUT', 'query', True))

    def test_each_negative_class_has_designated_marker(self):
        for kind, marker in [('storage', 'packedRowsValid'),
                             ('equality', 'emittedGraph.Adj i j ↔ graph.Adj i j'),
                             ('endpoint', 'checkAdjacencyInertiaAt'),
                             ('query', '.pos - '),
                             ('type', 'Type mismatch\ncompleteThree\nis expected to have type'),
                             ('reduction', 'Tactic `unfold` failed to unfold `graph` in\n  DecidableRel graph.Adj\n  did not reduce to `isTrue` or `isFalse`')]:
            with self.subTest(kind=kind):
                log = ('Case.lean:1:1: error: Tactic `decide` proved that the proposition\n⊢ '+
                       marker+'\nis false')
                self.assertTrue(classify(1, log,
                                         kind, False))

    def test_version_check_is_path_independent(self):
        self.assertTrue(lean_version_matches('Lean (version 4.30.0, x86_64)', '4.30.0'))
        self.assertFalse(lean_version_matches('Lean (version 4.29.0)', '4.30.0'))


if __name__ == '__main__':
    unittest.main()
