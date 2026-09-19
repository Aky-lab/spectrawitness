"""Source-bound, kernel-compiled graph-report roundtrips (no Lake invocation).

All artifacts are written beneath the caller's explicit package-local output
directory. A negative case is successful only when Lean reports its designated
proof/type obligation; parser errors, unrelated elaboration failures, crashes
and timeouts are failures of this validator.
"""
from __future__ import annotations

import argparse
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
from certify_graph import discover, emit, load_graph

ROOT = Path(__file__).resolve().parents[1]


def sha(blob: bytes) -> str:
    return hashlib.sha256(blob).hexdigest()


def file_hash(path: Path) -> str:
    return sha(path.read_bytes())


def within(path: Path, parent: Path) -> bool:
    return path == parent or parent in path.parents


def expected_lean_version() -> str:
    toolchain = (ROOT / 'lean-toolchain').read_text(encoding='utf-8').strip()
    match = re.fullmatch(r'leanprover/lean4:v(\d+\.\d+\.\d+)', toolchain)
    if match is None:
        raise ValueError(f'unsupported lean-toolchain declaration: {toolchain!r}')
    return match.group(1)


def lean_version_matches(version_output: str, expected: str) -> bool:
    return re.search(rf'Lean \(version {re.escape(expected)}(?:[,) ]|$)', version_output) is not None


def validate_paths(lean: Path, packages: Path, library: Path, output: Path, timeout: int):
    if timeout <= 0:
        raise ValueError('timeout must be positive')
    if not lean.is_file() or not packages.is_dir() or not library.is_dir():
        raise ValueError('lean, packages and library-dir must already exist')
    expected = expected_lean_version()
    try:
        version = subprocess.check_output([str(lean.resolve()), '--version'], text=True,
                                          encoding='utf-8', stderr=subprocess.STDOUT)
    except (OSError, subprocess.CalledProcessError) as exc:
        raise ValueError(f'cannot inspect Lean version: {exc}') from exc
    if not lean_version_matches(version, expected):
        raise ValueError(f'Lean version does not match lean-toolchain v{expected}')
    if not within(library.resolve(), ROOT.resolve()):
        raise ValueError('library-dir must be inside this source package')
    if not within(output.resolve(), ROOT.resolve()):
        raise ValueError('output-dir must be package-local')
    required = ('SpectralGraph/Graph/EncodingCheck.olean',
                'SpectralGraph/Graph/IntegerSpectrum.olean')
    for name in required:
        if not (library/name).is_file():
            raise ValueError(f'missing built library object: {name}')


def import_roots(packages: Path, library: Path, project_root: Path | None = None) -> list[Path]:
    roots = ([project_root.resolve()] if project_root is not None else []) + [library.resolve()]
    for folder in sorted(packages.iterdir(), key=lambda p: p.name):
        if folder.is_dir():
            obj = folder/'.lake/build/lib/lean'
            if obj.is_dir():
                roots.append(obj.resolve())
    return roots


def direct_imports(source: str, roots: list[Path]) -> dict[str, dict[str, str]]:
    found = {}
    for module in re.findall(r'^import ([A-Za-z_][A-Za-z_0-9.]*)$', source, re.M):
        path = Path(*module.split('.')).with_suffix('.olean')
        matches = [r/path for r in roots if (r/path).is_file()]
        if not matches:
            raise ValueError(f'no direct import object for {module}')
        selected = matches[0]
        found[module] = {'path': str(selected), 'sha256': file_hash(selected)}
    return found


def classify(returncode: int | None, log: str, expected: str, timed_out: bool,
             crashed: bool = False) -> bool:
    """Classify an actual Lean process by a required, case-specific diagnostic.

    `expected='accept'` requires a clean exit. Negative names select the
    stable proposition printed by Lean in the failing proof/type goal.
    """
    if timed_out or crashed or returncode is None:
        return False
    if expected == 'accept':
        return returncode == 0 and 'error:' not in log
    if returncode != 1 or 'error:' not in log:
        return False
    forbidden = ('unknown module prefix', 'unknown constant', 'unexpected token',
                 'parser error', 'failed to load', 'invalid character', 'uncaught exception',
                 'segmentation fault', 'stack overflow', 'deterministic) timeout',
                 'validator timeout')
    if any(x in log.lower() for x in forbidden):
        return False
    lines = log.splitlines()
    headers = [i for i, line in enumerate(lines) if re.search(
        r'\.lean:\d+:\d+: (?:error|warning)(?:\([^)]*\))?:', line)]
    if not headers or 'error' not in lines[headers[0]]:
        return False
    first = '\n'.join(lines[headers[0]:headers[1] if len(headers) > 1 else len(lines)])
    markers = {
        'storage': 'packedRowsValid',
        'equality': 'emittedGraph.Adj i j ↔ graph.Adj i j',
        'endpoint': 'checkAdjacencyInertiaAt',
        'query': '.pos - ',
        'type': 'Type mismatch',
        'reduction': 'Tactic `unfold` failed to unfold `graph` in',
    }
    marker = markers.get(expected)
    if marker is None:
        raise ValueError(f'unknown outcome class: {expected}')
    if expected in {'storage', 'equality', 'endpoint', 'query'}:
        if 'Tactic `decide` proved that the proposition' not in first or 'is false' not in first:
            return False
    if expected == 'type' and ('completeThree' not in first or
            'is expected to have type' not in first):
        return False
    if expected == 'reduction' and ('DecidableRel graph.Adj' not in first or
            'did not reduce to `isTrue` or `isFalse`' not in log):
        return False
    return marker.lower() in first.lower()


def as_json(rows, queries) -> bytes:
    return (json.dumps({'rows': rows, 'queries': queries}, separators=(',', ':'))+'\n').encode()


def bracket(a, b, k):
    return {'kind': 'bracket', 'lower': a, 'upper': b, 'index': k}


def count(a, b):
    return {'kind': 'count', 'lower': a, 'upper': b}


def input_cases():
    yield 'p5_mixed', as_json([2, 4, 8, 16, 0], [bracket('1732/1000', '1733/1000', 0),
        bracket(0, 1, 1), count(0, 1), count(0, 2)]), None, None
    yield 'k3_repeated', as_json([6, 4, 0], [bracket(-2, -1, 1),
        bracket('-4/2', '-2/2', 2), count('-6/3', -1), count(-1, 2), count(-1, -1)]), None, None
    yield 'k2_oriented_upper', as_json([2, 0], [bracket(0, 1, 0), count(0, 1)]), None, None
    yield 'k2_oriented_lower', as_json([0, 1], [bracket(0, 1, 0), count(0, 1)]), None, None
    yield 'k2_both', as_json([2, 1], [bracket(0, 1, 0), count(0, 1)]), None, None
    yield 'empty_count', as_json([], [count(-1, 0)]), None, None
    yield 'singleton_count', as_json([0], [count(-1, 0)]), None, None
    yield ('k3_bound', as_json([6, 4, 0], [bracket(-2, -1, 1),
        bracket(-2, -1, 2), count(-2, -1), count(-1, 2)]),
        'SpectralGraphTests.GraphReports.IndependentGraphs',
        'SpectralGraphTests.GraphReports.IndependentGraphs.completeThree')


def produce(blob: bytes, namespace: str, module: str | None = None,
            name: str | None = None) -> str:
    graph = load_graph(blob)
    return emit(graph, discover(graph), sha(blob), namespace=namespace,
                graph_module=module, graph_name=name)


def replace_once(source: str, before: str, after: str) -> str:
    if source.count(before) != 1:
        raise ValueError(f'expected unique mutation target {before!r}; found {source.count(before)}')
    return source.replace(before, after, 1)


def negative_cases():
    """Mutations preserve parseability and isolate the stated proof boundary."""
    k3 = as_json([6, 4, 0], [bracket(-2, -1, 1), count(-2, -1)])
    source = produce(k3, 'GraphReportValidation.NegativeK3')
    # Keep both the endpoint theorem's target and checker argument consistent.
    yield ('bad_endpoint', k3, source.replace('⟨3,0,0⟩', '⟨2,1,0⟩'),
           'endpoint', 'replace the first claimed inertia triple in both uses')
    yield ('bad_count', k3, replace_once(source, '.card = 2 := by', '.card = 1 := by'),
           'query', 'change only the derived count while endpoint facts stay valid')
    yield ('loop_storage', k3, replace_once(source, '#[6, 4, 0]', '#[7, 4, 0]'),
           'storage', 'introduce a stored loop but retain the semantic graph')
    yield ('high_bit_storage', k3, replace_once(source, '#[6, 4, 0]', '#[14, 4, 0]'),
           'storage', 'introduce a high bit but retain the semantic graph')
    edge_blob = as_json([2, 0, 0], [count(-2, -1), count(-1, 1)])
    edge = produce(edge_blob, 'GraphReportValidation.EdgeMismatch',
        'SpectralGraphTests.GraphReports.IndependentGraphs',
        'SpectralGraphTests.GraphReports.IndependentGraphs.edge02')
    yield ('isospectral_mismatch', edge_blob, edge, 'equality',
           'edge 01 versus named edge 02; labelled graphs differ but spectra agree')
    bound = produce(k3, 'GraphReportValidation.BadBinding',
        'SpectralGraphTests.GraphReports.IndependentGraphs',
        'SpectralGraphTests.GraphReports.IndependentGraphs.completeThree')
    graph_def = ('def graph : SimpleGraph (Fin 3) := '
        '_root_.SpectralGraphTests.GraphReports.IndependentGraphs.completeThree')
    wrong_dimension = replace_once(bound, graph_def, graph_def.replace('Fin 3', 'Fin 2'))
    # Stop immediately after the ill-typed binding, so recovery errors from
    # later theorem elaboration cannot masquerade as a clean type rejection.
    prefix = 'instance : DecidableRel graph.Adj'
    wrong_dimension = wrong_dimension.split(prefix, 1)[0] + 'end GraphReportValidation.BadBinding\n'
    yield ('wrong_dimension', k3, wrong_dimension, 'type',
        'named graph dimension differs from the generated Fin 3 graph')
    wrong_type = replace_once(bound, graph_def, graph_def.replace('SimpleGraph (Fin 3)', 'Nat'))
    wrong_type = wrong_type.split(prefix, 1)[0] + 'end GraphReportValidation.BadBinding\n'
    yield ('wrong_type', k3, wrong_type, 'type',
        'named graph has an incompatible non-graph type')
    yield ('opaque_adjacency', k3, replace_once(bound, graph_def,
        graph_def.replace('def graph', 'opaque graph')), 'reduction',
        'opaque named adjacency cannot be reduced to a decidable relation')


def p5_one_shot_source() -> str:
    """An independently written check using the pre-existing one-shot API."""
    return '''import SpectralGraph.Graph.EncodingCheck
import SpectralGraph.Graph.IntegerSpectrum

namespace GraphReportValidation.P5OneShot
open SpectralGraph SpectralGraph.Graph
def rows : PackedAdjacencyRows := #[2, 4, 8, 16, 0]
def graph : SimpleGraph (Fin 5) := graphOfPackedRows 5 rows
instance : DecidableRel graph.Adj := by unfold graph; infer_instance

theorem top_bracket :
    ((433 / 250 : ℚ) : ℝ) < (adjacency_isHermitian graph).eigenvalues₀ ⟨0, by decide⟩ ∧
    (adjacency_isHermitian graph).eigenvalues₀ ⟨0, by decide⟩ ≤ ((1733 / 1000 : ℚ) : ℝ) :=
  checkAdjacencyEigenvalueBracket_sound graph (433 / 250) (1733 / 1000)
    ⟨1,0,4⟩ ⟨0,0,5⟩ ⟨0, by decide⟩ (by decide +kernel)

theorem count_zero_two :
    (Finset.univ.filter fun i => ((0 : ℚ) : ℝ) < (adjacency_isHermitian graph).eigenvalues i ∧
      (adjacency_isHermitian graph).eigenvalues i ≤ ((2 : ℚ) : ℝ)).card = 2 :=
  checkAdjacencyEigenvaluesIoc_sound graph 0 2 ⟨2,1,2⟩ ⟨0,0,5⟩ 2 (by decide +kernel)
end GraphReportValidation.P5OneShot
'''


def orientation_equivalence_source() -> str:
    return '''import SpectralGraph.Graph.EncodingCheck
namespace GraphReportValidation.OrientationEquivalence
open SpectralGraph.Graph
theorem upper_lower :
    graphOfPackedRows 2 (#[2, 0] : PackedAdjacencyRows) =
      graphOfPackedRows 2 (#[0, 1] : PackedAdjacencyRows) := by
  have h : ∀ i j : Fin 2,
      (graphOfPackedRows 2 (#[2, 0] : PackedAdjacencyRows)).Adj i j ↔
      (graphOfPackedRows 2 (#[0, 1] : PackedAdjacencyRows)).Adj i j := by decide +kernel
  ext i j
  exact h i j
theorem upper_both :
    graphOfPackedRows 2 (#[2, 0] : PackedAdjacencyRows) =
      graphOfPackedRows 2 (#[2, 1] : PackedAdjacencyRows) := by
  have h : ∀ i j : Fin 2,
      (graphOfPackedRows 2 (#[2, 0] : PackedAdjacencyRows)).Adj i j ↔
      (graphOfPackedRows 2 (#[2, 1] : PackedAdjacencyRows)).Adj i j := by decide +kernel
  ext i j
  exact h i j
end GraphReportValidation.OrientationEquivalence
'''


class Runner:
    def __init__(self, lean: Path, roots: list[Path], output: Path, timeout: int):
        self.lean = lean.resolve()
        self.roots = roots
        self.output = output
        self.timeout = timeout
        self.cases = []
        self.env = os.environ.copy()
        self.env['LEAN_PATH'] = os.pathsep.join(str(p) for p in roots)

    def compile(self, name: str, blob: bytes, source: str, expected='accept',
                mutation: str | None = None):
        case = self.output/name
        case.mkdir()
        jpath, lpath, logpath, opath, cpath = [case/(name+ext) for ext in
            ('.json', '.lean', '.log', '.olean', '.command.json')]
        jpath.write_bytes(blob)
        lpath.write_text(source, encoding='utf-8', newline='\n')
        command = [str(self.lean), '-o', str(opath), str(lpath)]
        command_record = {'argv': command, 'cwd': str(ROOT),
            'ordered_import_roots': [str(p) for p in self.roots],
            'direct_import_objects': direct_imports(source, self.roots),
            'lean_executable_sha256': file_hash(self.lean)}
        cpath.write_text(json.dumps(command_record, indent=2)+'\n', encoding='utf-8')
        begin = time.monotonic()
        timed_out = crashed = False
        exit_status = None
        try:
            result = subprocess.run(command, cwd=ROOT, env=self.env, timeout=self.timeout,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, encoding='utf-8', errors='replace')
            exit_status, log = result.returncode, result.stdout
            crashed = result.returncode < 0
        except subprocess.TimeoutExpired as exc:
            timed_out = True
            partial = exc.stdout or b''
            log = partial.decode('utf-8', 'replace') if isinstance(partial, bytes) else partial
            log += '\nVALIDATOR TIMEOUT\n'
        runtime = round(time.monotonic()-begin, 3)
        logpath.write_text(log, encoding='utf-8')
        passed = classify(exit_status, log, expected, timed_out, crashed)
        record = {'name': name, 'expected': expected, 'mutation': mutation,
            'pass': passed, 'exit_status': exit_status, 'timed_out': timed_out,
            'crashed': crashed, 'observed_runtime_seconds': runtime,
            'files': {p.name: file_hash(p) for p in (jpath, lpath, logpath, cpath)
                      if p.is_file()}, 'direct_import_objects': command_record['direct_import_objects']}
        if opath.is_file():
            record['files'][opath.name] = file_hash(opath)
        self.cases.append(record)
        print(f'{name}: {"PASS" if passed else "FAIL"} ({runtime}s)', flush=True)
        if not passed:
            print(log[-5000:].encode('ascii', 'backslashreplace').decode('ascii'), flush=True)
        return passed


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', required=True, type=Path)
    parser.add_argument('--packages', required=True, type=Path)
    parser.add_argument('--library-dir', required=True, type=Path)
    parser.add_argument('--project-import-root', type=Path,
                        help='Optional package-local root for newly compiled test modules')
    parser.add_argument('--output-dir', required=True, type=Path)
    parser.add_argument('--timeout', type=int, default=180)
    args = parser.parse_args(argv)
    try:
        validate_paths(args.lean, args.packages, args.library_dir, args.output_dir, args.timeout)
        if args.project_import_root is not None and (not args.project_import_root.is_dir() or
                not within(args.project_import_root.resolve(), ROOT.resolve())):
            raise ValueError('project-import-root must be an existing package-local directory')
    except ValueError as exc:
        parser.error(str(exc))
    args.output_dir.mkdir(parents=True, exist_ok=True)
    output = Path(tempfile.mkdtemp(prefix='roundtrip-', dir=args.output_dir))
    roots = import_roots(args.packages, args.library_dir, args.project_import_root)
    runner = Runner(args.lean, roots, output, args.timeout)
    for name, blob, module, graph_name in input_cases():
        try:
            namespace = 'GraphReportValidation.' + ''.join(part.capitalize() for part in name.split('_'))
            source = produce(blob, namespace, module, graph_name)
            runner.compile(name, blob, source)
        except Exception as exc:
            runner.cases.append({'name': name, 'expected': 'accept', 'pass': False,
                                 'producer_error': f'{type(exc).__name__}: {exc}'})
            print(f'{name}: FAIL (producer: {exc})', flush=True)
    runner.compile('p5_one_shot', as_json([2, 4, 8, 16, 0],
        [bracket('1732/1000', '1733/1000', 0), count(0, 2)]),
        p5_one_shot_source(), 'accept', 'independent existing one-shot API')
    runner.compile('orientation_equivalence', as_json([2, 0], [count(0, 1)]),
        orientation_equivalence_source(), 'accept',
        'kernel equality for upper, lower, and both orientations')
    for name, blob, source, expected, mutation in negative_cases():
        try:
            runner.compile(name, blob, source, expected, mutation)
        except Exception as exc:
            runner.cases.append({'name': name, 'expected': expected, 'pass': False,
                                 'validator_error': f'{type(exc).__name__}: {exc}'})
            print(f'{name}: FAIL (validator: {exc})', flush=True)
    report = {'pass': all(x['pass'] for x in runner.cases),
        'lean_executable_sha256': file_hash(args.lean),
        'ordered_import_roots': [str(p) for p in roots],
        'source_files': {str(p): file_hash(p) for p in
            (Path(__file__), Path(__file__).with_name('certify_graph.py'))},
        'timeout_seconds': args.timeout, 'cases': runner.cases}
    (output/'report.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(f'Report: {output / "report.json"}', flush=True)
    return 0 if report['pass'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
