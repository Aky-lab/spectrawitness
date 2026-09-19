"""Run bounded native Lean workloads and record measurements (not proofs).

Precondition: Benchmarks.Driver has been compiled by validate_local.py.
Runtime excludes Lean startup/import overhead; wall time includes it.
Configured dependency caches are read-only.
"""
import argparse, json, os, subprocess, sys, time
from pathlib import Path
sys.stdout.reconfigure(encoding='utf-8')

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--lean', required=True, type=Path)
p.add_argument('--packages', required=True, type=Path)
p.add_argument('--timeout', type=int, default=120)
p.add_argument('--output', type=Path, default=Path('.validation/benchmarks.json'))
p.add_argument('--optimized', action='store_true')
a=p.parse_args()
root=Path(__file__).resolve().parents[1]
runner=root/'.validation/BenchmarkRun.lean'
runner.write_text('import Benchmarks.Driver\n#eval main\n',encoding='utf-8')
env=os.environ.copy()
env['LEAN_PATH']=os.pathsep.join([str(root/'.validation')]+[str(d/'.lake/build/lib/lean') for d in a.packages.resolve().iterdir() if d.is_dir()])
cases=[('integer',n) for n in [4,8,12,16,20]]+[('enumeration',n) for n in [4,5,6,7,8]]
if a.optimized:
    cases=[('normalized',n) for n in [4,8,12,16,20,40,80]]+[('fast-enumeration',n) for n in [4,5,6,7,8]]
results=[]
for kind,n in cases:
    env['SPECTRAL_BENCH_KIND']=kind; env['SPECTRAL_BENCH_N']=str(n)
    start=time.monotonic()
    print(f'Benchmark {kind} order {n}',flush=True)
    try:
        r=subprocess.run([str(a.lean.resolve()),str(runner)],cwd=root,env=env,
                         stdout=subprocess.PIPE,stderr=subprocess.STDOUT,encoding='utf-8',timeout=a.timeout)
        entry={'kind':kind,'order':n,'wall_seconds':round(time.monotonic()-start,3),
               'exit_code':r.returncode,'output':r.stdout.strip()}
        print(r.stdout.strip(),flush=True)
        if r.returncode: entry['status']='failed'
        else: entry['status']='completed'
    except subprocess.TimeoutExpired as exc:
        entry={'kind':kind,'order':n,'wall_seconds':round(time.monotonic()-start,3),'status':'timeout'}
        print('Timed out; no performance result claimed',flush=True)
    results.append(entry)
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps({'timeout_seconds':a.timeout,'results':results},indent=2)+'\n',encoding='utf-8')
