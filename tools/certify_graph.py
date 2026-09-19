"""Generate exact, kernel-checkable Lean reports for bounded packed graphs.

The Python discovery is untrusted. Compile the emitted Lean module to verify it.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re

from certify_matrix import diagonalize, rational, unique_object, reject_constant

MAX_ORDER = 12
MAX_QUERIES = 32
MAX_ENDPOINTS = 16
_NAMESPACE = re.compile(r'[A-Z][A-Za-z0-9_]*(?:\.[A-Z][A-Za-z0-9_]*)*\Z', re.ASCII)
_NAME = re.compile(r'[A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z][A-Za-z0-9_]*)*\Z', re.ASCII)
_RESERVED = {'by', 'def', 'theorem', 'axiom', 'sorry', 'admit', 'fun', 'let', 'in',
             'if', 'then', 'else', 'match', 'with', 'where', 'import', 'open',
             'namespace', 'end', 'instance', 'example', 'structure', 'inductive',
             'class', 'Type', 'Sort', 'Prop'}


@dataclass(frozen=True)
class Query:
    kind: str
    lower: Fraction
    upper: Fraction
    index: int | None = None


@dataclass(frozen=True)
class GraphInput:
    rows: tuple[int, ...]
    queries: tuple[Query, ...]


@dataclass(frozen=True)
class Discovery:
    endpoints: tuple[Fraction, ...]
    inertias: tuple[tuple[int, int, int], ...]
    counts: tuple[int | None, ...]


def _exact_keys(value, keys, place):
    if not isinstance(value, dict) or set(value) != set(keys):
        raise ValueError(f'{place} must have exactly keys {sorted(keys)}')


def _integer(value, place):
    if type(value) is not int:
        raise ValueError(f'{place} must be a JSON integer')
    return value


def read_graph(data) -> GraphInput:
    _exact_keys(data, {'rows', 'queries'}, 'input')
    rows = data['rows']
    if not isinstance(rows, list) or len(rows) > MAX_ORDER:
        raise ValueError(f'rows must be an array of order at most {MAX_ORDER}')
    n = len(rows)
    for i, value in enumerate(rows):
        _integer(value, f'row {i}')
        if value < 0 or value >= 2 ** n or value & (1 << i):
            raise ValueError(f'row {i} has negative/high bits or a stored loop')
    raw_queries = data['queries']
    if not isinstance(raw_queries, list) or not 1 <= len(raw_queries) <= MAX_QUERIES:
        raise ValueError(f'queries must contain 1–{MAX_QUERIES} entries')
    queries = []
    for i, item in enumerate(raw_queries):
        if (not isinstance(item, dict) or type(item.get('kind')) is not str or
                item.get('kind') not in {'bracket', 'count'}):
            raise ValueError(f'query {i} has an unknown kind')
        kind = item['kind']
        _exact_keys(item, {'kind', 'lower', 'upper', 'index'} if kind == 'bracket'
                    else {'kind', 'lower', 'upper'}, f'query {i}')
        lower, upper = rational(item['lower']), rational(item['upper'])
        if lower > upper:
            raise ValueError(f'query {i} has reversed endpoints')
        index = None
        if kind == 'bracket':
            index = _integer(item['index'], f'query {i} index')
            if not 0 <= index < n:
                raise ValueError(f'query {i} index is outside Fin {n}')
        queries.append(Query(kind, lower, upper, index))
    endpoints = {x for q in queries for x in (q.lower, q.upper)}
    if len(endpoints) > MAX_ENDPOINTS:
        raise ValueError(f'at most {MAX_ENDPOINTS} distinct rational endpoints are supported')
    return GraphInput(tuple(rows), tuple(queries))


def load_graph(raw: bytes) -> GraphInput:
    if not isinstance(raw, bytes):
        raise ValueError('input must be raw UTF-8 bytes')
    return read_graph(json.loads(raw.decode('utf-8'), object_pairs_hook=unique_object,
                                 parse_constant=reject_constant))


def discover(graph: GraphInput) -> Discovery:
    # Revalidate programmatic inputs before using their data in generated Lean.
    if (type(graph) is not GraphInput or type(graph.rows) is not tuple or
            type(graph.queries) is not tuple or any(
                type(q) is not Query or type(q.lower) is not Fraction or
                type(q.upper) is not Fraction for q in graph.queries)):
        raise ValueError('expected canonical GraphInput')
    canonical = read_graph({'rows': list(graph.rows), 'queries': [
        {'kind': q.kind, 'lower': str(q.lower), 'upper': str(q.upper),
         **({'index': q.index} if q.kind == 'bracket' else {})}
        for q in graph.queries]})
    if canonical != graph:
        raise ValueError('GraphInput is not canonical')
    n = len(graph.rows)
    adjacency = [[Fraction(int(i != j and bool((graph.rows[i] >> j) & 1 or
                      (graph.rows[j] >> i) & 1))) for j in range(n)] for i in range(n)]
    endpoints = tuple(sorted({x for q in graph.queries for x in (q.lower, q.upper)}))
    inertias = tuple(diagonalize([[adjacency[i][j] - (x if i == j else 0)
                                  for j in range(n)] for i in range(n)])[2]
                     for x in endpoints)
    at = dict(zip(endpoints, inertias))
    counts = []
    for i, q in enumerate(graph.queries):
        left, right = at[q.lower][0], at[q.upper][0]
        if q.kind == 'bracket':
            if not (q.index < left and right <= q.index):
                raise ValueError(f'query {i} bracket is false for the discovered spectrum')
            counts.append(None)
        else:
            if left < right:
                raise RuntimeError(f'query {i} discovery violates endpoint order')
            counts.append(left - right)
    return Discovery(endpoints, inertias, tuple(counts))


def _qualified(value, namespace=False):
    pattern = _NAMESPACE if namespace else _NAME
    if not isinstance(value, str) or not pattern.fullmatch(value) or any(
            part in _RESERVED for part in value.split('.')):
        raise ValueError('unsafe Lean namespace/module/name')
    return value


def _lean_rational(value: Fraction):
    if value.denominator == 1:
        return str(value.numerator)
    return f'({value.numerator} / {value.denominator})'


def emit(graph: GraphInput, discovery: Discovery, source_hash: str,
         namespace: str = 'GeneratedGraphReport', graph_module: str | None = None,
         graph_name: str | None = None) -> str:
    namespace = _qualified(namespace, True)
    if (graph_module is None) != (graph_name is None):
        raise ValueError('graph module and graph name must be supplied together')
    if graph_module is not None:
        _qualified(graph_module, True)
        _qualified(graph_name)
    if not isinstance(source_hash, str) or not re.fullmatch(r'[0-9a-fA-F]{64}', source_hash):
        raise ValueError('source hash must be exactly 64 hexadecimal characters')
    verified = discover(graph)
    if type(discovery) is not Discovery or discovery != verified:
        raise ValueError('discovery does not match the validated graph')
    # Render only fresh, internally discovered values even if a caller supplied
    # objects with surprising equality or string methods inside Discovery.
    discovery = verified
    n = len(graph.rows)
    row_text = ', '.join(str(x) for x in graph.rows)
    lines = ['import SpectralGraph.Graph.EncodingCheck',
             'import SpectralGraph.Graph.IntegerSpectrum']
    if graph_module:
        lines.append(f'import {graph_module}')
    lines += ['', f'/- Generated from exact JSON, SHA256 {source_hash.lower()}.',
              'The external producer is untrusted; compile this file for kernel verification. -/',
              f'namespace {namespace}', 'open SpectralGraph SpectralGraph.Graph', '',
              f'def rows : PackedAdjacencyRows := #[{row_text}]',
              f'theorem rows_valid : packedRowsValid {n} rows = true := by decide +kernel',
              f'def emittedGraph : SimpleGraph (Fin {n}) := graphOfPackedRows {n} rows',
              'instance : DecidableRel emittedGraph.Adj := by unfold emittedGraph; infer_instance']
    if graph_name:
        lines += [f'def graph : SimpleGraph (Fin {n}) := _root_.{graph_name}',
                  'instance : DecidableRel graph.Adj := by unfold graph; infer_instance',
                  'theorem graph_matches : emittedGraph = graph := by',
                  f'  have h : ∀ i j : Fin {n}, emittedGraph.Adj i j ↔ graph.Adj i j := by decide +kernel',
                  '  ext i j', '  exact h i j']
    target = 'graph' if graph_name else 'emittedGraph'
    lines.append('')
    endpoint_ids = {x: i for i, x in enumerate(discovery.endpoints)}
    for i, (value, triple) in enumerate(zip(discovery.endpoints, discovery.inertias)):
        inertia = f'⟨{triple[0]},{triple[1]},{triple[2]}⟩'
        lines += [f'def endpoint_{i} : ℚ := {_lean_rational(value)}',
                  f'theorem inertia_{i} : matrixInertia ({target}.adjMatrix ℝ - (endpoint_{i} : ℝ) • 1) = {inertia} :=',
                  f'  checkAdjacencyInertiaAt_sound {target} endpoint_{i} {inertia} (by decide +kernel)', '']
    for i, q in enumerate(graph.queries):
        lo, hi = endpoint_ids[q.lower], endpoint_ids[q.upper]
        if q.kind == 'bracket':
            k = q.index
            lines += [f'theorem query_{i} :',
                      f'    (endpoint_{lo} : ℝ) < (adjacency_isHermitian {target}).eigenvalues₀ ⟨{k}, by decide⟩ ∧',
                      f'    (adjacency_isHermitian {target}).eigenvalues₀ ⟨{k}, by decide⟩ ≤ (endpoint_{hi} : ℝ) := by',
                      f'  apply (Inertia.eigenvalues₀_mem_Ioc_iff _ (adjacency_isHermitian {target}) _ _ _).mpr',
                      f'  rw [inertia_{lo}, inertia_{hi}]', '  decide', '']
        else:
            count = discovery.counts[i]
            rewrites = f'inertia_{lo}' if lo == hi else f'inertia_{lo}, inertia_{hi}'
            lines += [f'theorem query_{i} :',
                      f'    (Finset.univ.filter fun j => (endpoint_{lo} : ℝ) < (adjacency_isHermitian {target}).eigenvalues j ∧',
                      f'      (adjacency_isHermitian {target}).eigenvalues j ≤ (endpoint_{hi} : ℝ)).card = {count} := by',
                      f'  rw [Inertia.eigenvalue_count_Ioc_eq _ (adjacency_isHermitian {target}) _ _ (by norm_num [endpoint_{lo}, endpoint_{hi}]),',
                      f'    {rewrites}]', '  decide', '']
    lines += [f'end {namespace}', '']
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--namespace', default='GeneratedGraphReport')
    parser.add_argument('--graph-module')
    parser.add_argument('--graph-name')
    args = parser.parse_args()
    try:
        raw = args.input.read_bytes()
        graph = load_graph(raw)
        found = discover(graph)
        result = emit(graph, found, hashlib.sha256(raw).hexdigest(), args.namespace,
                      args.graph_module, args.graph_name)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with args.output.open('x', encoding='utf-8', newline='\n') as stream:
            stream.write(result)
    except (ValueError, RuntimeError, UnicodeError, OSError) as exc:
        parser.error(str(exc))
    print(f'Wrote {args.output}: order {len(graph.rows)}, {len(graph.queries)} queries; compile to verify')


if __name__ == '__main__':
    main()
