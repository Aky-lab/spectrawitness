"""Bounded native and kernel benchmark for supplied-product witnesses.

Native timing excludes process startup and argument parsing; matrix entries are
evaluated on demand inside the measured checks. Kernel cases are compiled
separately and include Lean startup/import/elaboration overhead.
This script writes only under spectral_graph/.validation and Benchmarks/results.
"""
import argparse
import json
import os
from pathlib import Path
import platform
import statistics
import subprocess
import time

parser = argparse.ArgumentParser()
parser.add_argument('--lean', required=True, type=Path)
parser.add_argument('--packages', required=True, type=Path)
parser.add_argument('--output', type=Path,
                    default=Path('Benchmarks/results/2026-09-10/product-witness.json'))
parser.add_argument('--environment-output', type=Path,
                    default=Path('Benchmarks/results/2026-09-10/product-witness-environment.json'))
parser.add_argument('--repeats', type=int, default=10)
parser.add_argument('--trials', type=int, default=3)
args = parser.parse_args()
root = Path(__file__).resolve().parents[1]
runner = root / '.validation' / 'ProductWitnessRun.lean'
runner.write_text('import Benchmarks.ProductWitnessSubspace\n#eval SpectralGraphBenchmarks.ProductWitness.main\n', encoding='utf-8')
env = os.environ.copy()
env['LEAN_PATH'] = os.pathsep.join(
    [str(root / '.validation')] +
    [str(path / '.lake/build/lib/lean') for path in args.packages.resolve().iterdir() if path.is_dir()]
)
out = args.output if args.output.is_absolute() else root / args.output
envout = args.environment_output if args.environment_output.is_absolute() else root / args.environment_output
out.parent.mkdir(parents=True, exist_ok=True)
envout.parent.mkdir(parents=True, exist_ok=True)
def native_trial(case, route):
    local = dict(env, SPECTRAL_PRODUCT_CASE=case, SPECTRAL_PRODUCT_ROUTE=route,
                 SPECTRAL_PRODUCT_REPEATS=str(args.repeats))
    started = time.monotonic()
    try:
        proc = subprocess.run([str(args.lean.resolve()), str(runner)], cwd=root, env=local,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                              encoding='utf-8', timeout=30)
        status = 'completed' if proc.returncode == 0 else 'failed'
        output = proc.stdout.strip()
    except subprocess.TimeoutExpired as exc:
        status, output = 'timeout', (exc.stdout or '')
        if isinstance(output, bytes): output = output.decode('utf-8', errors='replace')
    entry = {'case': case, 'route': route, 'status': status,
             'wall_seconds': round(time.monotonic() - started, 3), 'output': output}
    for line in output.splitlines():
        parts = line.split('|')
        if parts[0] == 'RUNTIME_NS':
            entry['runtime_ns'] = int(parts[1]); entry['repeats'] = int(parts[2])
        if parts[0] == 'RESULT': entry['accepted'] = parts[3] == 'true'
    return entry

report = {
    'workload': 'diagonal ±1 ambient matrix; standard basis negative witness (n=6,k=2 and n=8,k=3)',
    'measurement': 'native checker runtime over repeated identical checks; process startup and argument parsing excluded, while matrix entries are evaluated on demand inside RUNTIME_NS',
    'repeats_per_trial': args.repeats, 'trials_per_route': args.trials,
    'limitations': ['timings include Lean runtime dispatch and Bool forcing',
                    'the repeated check is a deterministic closed workload and may benefit from compiler optimization',
                    'supplied image is trusted only as input after checker verifies A*U=W',
                    'kernel compilation cases include startup/import/elaboration overhead'],
    'native': [], 'kernel': []}
for case in ('6x2', '8x3'):
    for route in ('baseline', 'supplied'):
        trials = [native_trial(case, route) for _ in range(args.trials)]
        runtimes = [x['runtime_ns'] for x in trials if 'runtime_ns' in x]
        report['native'].append({'case': case, 'route': route, 'trials': trials,
            'median_runtime_ns': statistics.median(runtimes) if runtimes else None,
            'min_runtime_ns': min(runtimes) if runtimes else None,
            'max_runtime_ns': max(runtimes) if runtimes else None})
        out.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')

# These are the two bounded closed acceptance routes available to kernel
# reduction. Native 6x2 and 8x3 cases above carry the same scalable workloads.
kernel_cases = [('6x2', 'baseline'), ('6x2', 'supplied'),
                ('8x3', 'baseline'), ('8x3', 'supplied')]
for case, route in kernel_cases:
    started = time.monotonic()
    proof = root / '.validation' / f'ProductWitnessKernel_{route}.lean'
    n, k = map(int, case.split('x'))
    if route == 'baseline':
        statement = f'example : SpectralGraph.Certificate.checkNegativeSubspace (SpectralGraphBenchmarks.ProductWitness.ambient {n} {k}) (SpectralGraphBenchmarks.ProductWitness.witness {n} {k}) (SpectralGraphBenchmarks.ProductWitness.diagonal {k}) = true := by decide +kernel\n'
    else:
        statement = f'example : SpectralGraph.Certificate.checkNegativeSubspaceWithImage (SpectralGraphBenchmarks.ProductWitness.ambient {n} {k}) (SpectralGraphBenchmarks.ProductWitness.witness {n} {k}) (SpectralGraphBenchmarks.ProductWitness.image {n} {k}) (SpectralGraphBenchmarks.ProductWitness.diagonal {k}) = true := by decide +kernel\n'
    proof.write_text('import Benchmarks.ProductWitnessSubspace\n' + statement, encoding='utf-8')
    try:
        proc = subprocess.run([str(args.lean.resolve()), str(proof)],
                              cwd=root, env=env, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, encoding='utf-8', timeout=120)
        entry = {'case': case, 'route': route,
                 'status': 'completed' if proc.returncode == 0 else 'failed',
                 'exit_code': proc.returncode,
                 'wall_seconds': round(time.monotonic() - started, 3),
                 'output': proc.stdout.strip()}
    except subprocess.TimeoutExpired as exc:
        output = exc.stdout or ''
        if isinstance(output, bytes):
            output = output.decode('utf-8', errors='replace')
        entry = {'case': case, 'route': route, 'status': 'timeout',
                 'wall_seconds': round(time.monotonic() - started, 3),
                 'output': output.strip()}
    report['kernel'].append(entry)
    out.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')

environment = {'python': platform.python_version(), 'platform': platform.platform(),
               'processor': platform.processor(), 'lean_executable': str(args.lean.resolve()),
               'packages_argument': str(args.packages.resolve()), 'timeout_seconds_native': 30,
               'timeout_seconds_kernel': 120,
               'commands': ['python tools/benchmark_product_witness.py --lean <lean> --packages .lake/packages',
                            'lean Benchmarks/ProductWitnessSubspace.lean',
                            'lean .validation/ProductWitnessRun.lean']}
envout.write_text(json.dumps(environment, indent=2) + '\n', encoding='utf-8')
print(json.dumps(report, indent=2))
