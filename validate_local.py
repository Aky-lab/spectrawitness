"""Compile against an existing cache, reading it without running Lake in it.

Usage: python validate_local.py --lean PATH --packages PATH
All generated objects and logs go into this project's .validation directory.
"""
from pathlib import Path
import argparse, hashlib, json, os, re, subprocess, sys, time
sys.stdout.reconfigure(encoding='utf-8')

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--lean', required=True, type=Path)
p.add_argument('--packages', required=True, type=Path)
p.add_argument('--incremental', action='store_true', help='Reuse local objects newer than their sources and local imports; use only with unchanged toolchain and external cache')
p.add_argument('--output-dir', type=Path, default=Path('.validation'), help='Separate local output directory; use a fresh directory for a from-source rebuild')
p.add_argument('--timeout', type=int, default=300, help='Maximum seconds per compiler process')
p.add_argument('--modules', nargs='+', help='Validate only these modules and their dependencies (for disjoint concurrent development)')
a = p.parse_args()
root = Path(__file__).resolve().parent
packages = a.packages.resolve()
if not packages.is_dir():
    p.error('Packages directory must exist')
out = (root / a.output_dir).resolve()
if not out.is_relative_to(root) or out == root:
    p.error('Output directory must be a child of this source package')
if a.timeout <= 0:
    p.error('Timeout must be positive')
out.mkdir(parents=True, exist_ok=True)
env = os.environ.copy()
package_roots = [x / '.lake/build/lib/lean' for x in packages.iterdir()
                 if x.is_dir() and (x / '.lake/build/lib/lean').is_dir()]
env['LEAN_PATH'] = os.pathsep.join([str(out)] + [str(x) for x in package_roots])
sources = {'.'.join(f.relative_to(root).with_suffix('').parts): f for f in root.rglob('*.lean') if not any(part.startswith('.') for part in f.relative_to(root).parts)}
allowed_external_roots = {'Lean', 'Std', 'Mathlib'}
done = set()
visiting = set()
warnings = {}
compiled = []
reused = []
start = time.monotonic()

def build(name):
    if name in done: return
    if name in visiting:
        raise RuntimeError(f'Import cycle involving {name}')
    if name not in sources:
        raise RuntimeError(f'Unknown local module {name}')
    visiting.add(name)
    f = sources[name]
    s = f.read_text(encoding='utf-8')
    if re.search(r'\b(sorry|admit|axiom|native_decide)\b', s):
        raise RuntimeError(f'Forbidden proof escape or native evaluation in {name}')
    deps = re.findall(r'^import\s+(\S+)', s, re.M)
    for dep in deps:
        if dep in sources:
            build(dep)
            continue
        top = dep.split('.', 1)[0]
        if top not in allowed_external_roots:
            raise RuntimeError(f'Unknown import root {top!r} in {name}; expected a local module or one of {sorted(allowed_external_roots)}')
    dest = out / f.relative_to(root).with_suffix('.olean')
    dest.parent.mkdir(parents=True, exist_ok=True)
    inputs = [f, a.lean] + [out / sources[d].relative_to(root).with_suffix('.olean') for d in deps if d in sources]
    if a.incremental and dest.exists() and all(dest.stat().st_mtime_ns > x.stat().st_mtime_ns for x in inputs):
        done.add(name)
        visiting.remove(name)
        reused.append(name)
        return
    print('Checking ' + name, flush=True)
    run = subprocess.run([str(a.lean.resolve()), '-o', str(dest), str(f.relative_to(root))], cwd=root, env=env, text=True, encoding='utf-8', stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=a.timeout)
    (out / (name + '.log')).write_text(run.stdout, encoding='utf-8')
    if run.returncode:
        print(run.stdout, flush=True)
        sys.exit(run.returncode)
    if 'warning:' in run.stdout:
        warnings[name] = run.stdout
    compiled.append(name)
    visiting.remove(name)
    done.add(name)

for name in (a.modules or sorted(sources)): build(name)
report = {'modules': len(done), 'seconds': round(time.monotonic()-start, 1),
          'incremental': a.incremental, 'output_dir': str(out),
          'compiled_modules': compiled, 'reused_modules': reused, 'warnings': warnings,
          'lean_version': subprocess.check_output([str(a.lean.resolve()), '--version'], encoding='utf-8').strip(),
          'source_sha256': {name: hashlib.sha256(sources[name].read_bytes()).hexdigest() for name in sorted(done)}}
(out / ('report-selected.json' if a.modules else 'report.json')).write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
print(f'PASS: {len(done)} modules compiled in {time.monotonic()-start:.1f}s', flush=True)
