"""Check source boundaries and the compiled public-theorem axiom report.

Run validate_local.py first, then provide its fresh Trust log and report.
This is a validation guard; Lean's kernel, not this Python script, checks proofs.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys


def audit(root, trust_log, report=None):
    failures = []
    sources = list((root / 'SpectralGraph').rglob('*.lean'))
    sources += list((root / 'SpectralGraphTests').rglob('*.lean'))
    sources += [root / 'SpectralGraph.lean', root / 'SpectralGraphTests.lean']
    source_hashes = {}
    local_modules = {'.'.join(path.relative_to(root).with_suffix('').parts) for path in sources}
    allowed_external_roots = {'Lean', 'Std', 'Mathlib'}
    for path in sources:
        text = path.read_text(encoding='utf-8')
        name = '.'.join(path.relative_to(root).with_suffix('').parts)
        source_hashes[name] = hashlib.sha256(path.read_bytes()).hexdigest()
        if re.search(r'\b(sorry|admit|axiom|native_decide)\b', text):
            failures.append(f'Forbidden proof escape in {name}')
        for imported in re.findall(r'^\s*(?:public\s+)?import\s+([A-Za-z_][A-Za-z_0-9.]*)', text, re.M):
            if imported in local_modules:
                continue
            top = imported.split('.', 1)[0]
            if top not in allowed_external_roots:
                failures.append(f'Unknown import root {top!r} in {name}; expected a local module or declared dependency root')
        if re.search(r'^\s*#eval\b', text, re.M):
            failures.append(f'Native evaluation belongs in Benchmarks, not {name}')
    requested = set(re.findall(r'^#print axioms (\S+)',
                    (root / 'SpectralGraphTests/Trust.lean').read_text(encoding='utf-8'), re.M))
    log = trust_log.read_text(encoding='utf-8')
    found = {}
    for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", log):
        found[name] = set(filter(None, (a.strip() for a in axioms.split(','))))
    for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
        found[name] = set()
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    if 'error:' in log:
        failures.append('Trust log contains a compilation error')
    for name in sorted(requested):
        if name not in found:
            failures.append(f'Missing axiom inspection for {name}')
        elif found[name] - allowed:
            failures.append(f'Unexpected axioms for {name}: {sorted(found[name] - allowed)}')
    if report is not None:
        recorded = json.loads(report.read_text(encoding='utf-8'))['source_sha256']
        for name, digest in source_hashes.items():
            if recorded.get(name) != digest:
                failures.append(f'Missing or stale compiled source hash: {name}')
    return {'pass': not failures, 'source_modules': len(sources),
            'audited_theorems': len(requested), 'failures': failures}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--trust-log', required=True, type=Path)
    parser.add_argument('--report', type=Path, help='Also require current hashes for every library/test module')
    args = parser.parse_args()
    result = audit(Path(__file__).resolve().parents[1], args.trust_log, args.report)
    print(json.dumps(result, indent=2))
    return 0 if result['pass'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
