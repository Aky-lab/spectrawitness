"""Bounded native coefficient-growth benchmark; measurements are not proofs.

Compile Benchmarks/Growth.lean first. Each subprocess is limited to 120 seconds,
including Lean startup, elimination, and its independent diagnostic trace.
Elimination timing excludes matrix construction, output and diagnostics.
Stop larger baseline cases after any failure or timeout.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import time

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--lean', required=True, type=Path)
parser.add_argument('--packages', required=True, type=Path)
parser.add_argument('--output', type=Path, default=Path('.validation/benchmarks-growth.json'))
args = parser.parse_args()
root = Path(__file__).resolve().parents[1]
runner = root / '.validation' / 'GrowthRun.lean'
runner.write_text('import Benchmarks.Growth\n#eval SpectralGraphBenchmarks.Growth.main\n', encoding='utf-8')
env = os.environ.copy()
env['LEAN_PATH'] = os.pathsep.join([str(root / '.validation')] + [
    str(path / '.lake/build/lib/lean') for path in args.packages.resolve().iterdir() if path.is_dir()
])
report = {
    'workload': '3I - adjacency(path_n)',
    'expected_inertia': '(n, 0, 0)',
    'timeout_seconds_per_case': 120,
    'measurement': 'native elimination runtime; construction, output, startup and diagnostics excluded',
    'diagnostic': 'independent positive-pivot trace; not a theorem or certificate',
    'results': [],
}
for mode in ('baseline', 'normalized'):
    for n in (16, 20, 24):
        env['SPECTRAL_GROWTH_MODE'] = mode
        env['SPECTRAL_GROWTH_N'] = str(n)
        print(f'Growth benchmark {mode}, order {n}', flush=True)
        start = time.monotonic()
        entry = {'mode': mode, 'order': n}
        try:
            result = subprocess.run([str(args.lean.resolve()), str(runner)], cwd=root, env=env,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, encoding='utf-8', timeout=120)
            entry.update(status='completed' if result.returncode == 0 else 'failed',
                exit_code=result.returncode, output=result.stdout.strip())
        except subprocess.TimeoutExpired as exc:
            partial = exc.stdout or ''
            if isinstance(partial, bytes):
                partial = partial.decode('utf-8', errors='replace')
            entry.update(status='timeout', output=partial.strip())
        entry['wall_seconds'] = round(time.monotonic() - start, 3)
        for line in entry['output'].splitlines():
            parts = line.split('|')
            if parts[0] == 'RESULT':
                entry['inertia'] = list(map(int, parts[1:]))
            elif parts[0] == 'RUNTIME_NS':
                entry['runtime_ns'] = int(parts[1])
            elif parts[0] == 'DIAGNOSTIC_NS':
                entry['diagnostic_ns'] = int(parts[1])
            elif parts[0] == 'GROWTH':
                entry.update(max_stored_bits=int(parts[1]), max_before_reduction_bits=int(parts[2]),
                    positive_pivot_steps=int(parts[3]), diagnostic_valid=parts[4] == 'true')
        report['results'].append(entry)
        output = args.output if args.output.is_absolute() else root / args.output
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
        print(json.dumps(entry), flush=True)
        if mode == 'baseline' and entry['status'] != 'completed':
            print('Stopping larger baseline cases after failure/timeout.', flush=True)
            break
