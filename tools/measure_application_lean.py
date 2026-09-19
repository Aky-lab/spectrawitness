"""Source-bound preparation and bounded Lean measurements for path witnesses."""
from __future__ import annotations
import argparse, hashlib, json, math, os, platform, re, statistics, subprocess, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PACKAGE_ROOT = ROOT.resolve()
VALIDATION_ROOT = (ROOT / ".validation" / "application-measurements").resolve()
DEFAULT_PREPARED = VALIDATION_ROOT / "prepared"
DEFAULT_REPORT = VALIDATION_ROOT / "lean-measurement.json"
SOURCE = ROOT / "Benchmarks" / "ApplicationWitnessNative.lean"
DRIVER = Path(__file__).resolve()
CASES, ROUTES = ("n6", "n8", "n12"), ("old", "supplied")
CASE_SPEC = {
    "n6": (6,"4/9","329/4338","-850/241"),
    "n8": (8,"1/4","223/4016","-3129/1004"),
    "n12": (12,"1/9","225679/6144318","-5463458/3072159"),
}
FIXTURES = {c: ROOT / "examples" / "application" / f"{c}_half_witness.json" for c in CASES}
CHECKER_SOURCES = (
    ROOT / "SpectralGraph" / "Certificate" / "WitnessSubspace.lean",
    ROOT / "SpectralGraph" / "Certificate" / "ProductWitnessSubspace.lean",
)
RESULT_RE = re.compile(
    r"RESULT\|case=(n6|n8|n12)\|route=(old|supplied)\|result=(true|false)"
    r"\|repeats=([1-9][0-9]*)\|first_call_ns=([1-9][0-9]*)"
    r"\|runtime_ns=([1-9][0-9]*)\|parse_ns=([0-9]+)")
SCHEMA = "weighted-path-application-lean-measurement-v4"
MANIFEST_SCHEMA = "weighted-path-application-native-prepared-v2"


class ValidationError(RuntimeError): pass


def sha256(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""): h.update(chunk)
    return h.hexdigest()


def is_within(path, root):
    try: Path(path).resolve().relative_to(Path(root).resolve()); return True
    except ValueError: return False


def checked_path(path, root, label, *, exists=True):
    path, root = Path(path).resolve(), Path(root).resolve()
    if not is_within(path, root): raise ValidationError(f"{label} is outside {root}: {path}")
    if exists and not path.exists(): raise ValidationError(f"missing {label}: {path}")
    return path


def timed(cmd, *, cwd, env, cap):
    started = time.perf_counter()
    try:
        run = subprocess.run([str(x) for x in cmd], cwd=cwd, env=env, text=True,
            encoding="utf-8", stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=cap)
        return {"status": "completed" if run.returncode == 0 else "failed",
            "wall_seconds": time.perf_counter()-started, "returncode": run.returncode,
            "output": run.stdout, "command": [str(x) for x in cmd]}
    except subprocess.TimeoutExpired as exc:
        out = exc.stdout or ""
        if isinstance(out, bytes): out = out.decode("utf-8", errors="replace")
        return {"status": "timeout", "wall_seconds": time.perf_counter()-started,
            "returncode": None, "output": out, "command": [str(x) for x in cmd]}


def import_roots(packages, prepared_lib=None):
    packages = Path(packages).resolve()
    if not packages.is_dir(): raise ValidationError(f"missing packages directory: {packages}")
    roots, local = [], ROOT / ".lake" / "build" / "lib" / "lean"
    if local.exists(): roots.append(local.resolve())
    for package in sorted(packages.iterdir(), key=lambda p: p.name):
        candidate = package / ".lake" / "build" / "lib" / "lean"
        if package.is_dir() and candidate.exists():
            roots.append(candidate.resolve())
    if prepared_lib is not None: roots.insert(0, Path(prepared_lib).resolve())
    if not roots: raise ValidationError("no package-local Lean import roots found")
    return roots


def lean_env(roots, temp_dir):
    env = os.environ.copy(); env["LEAN_PATH"] = os.pathsep.join(map(str, roots))
    Path(temp_dir).mkdir(parents=True, exist_ok=True)
    for name in ("TEMP", "TMP", "TMPDIR"): env[name] = str(Path(temp_dir).resolve())
    return env


def locate_import_artifact(module, roots):
    relative = Path(*module.split(".")).with_suffix(".olean")
    matches = [(root / relative).resolve() for root in roots if (root / relative).is_file()]
    # LEAN_PATH is ordered; the first existing module is the artifact Lean imports.
    if not matches: raise ValidationError(f"no artifact found for {module}")
    return matches[0]


def prepare(*, lean, packages, artifact_dir=DEFAULT_PREPARED, cap=180, run=timed):
    artifact_dir = checked_path(artifact_dir, VALIDATION_ROOT, "artifact directory", exists=False)
    if artifact_dir.exists():
        raise ValidationError(f"preparation directory must be fresh and empty: {artifact_dir}")
    artifact_dir.mkdir(parents=True, exist_ok=False)
    prep_report={"schema":"weighted-path-application-native-preparation-v1","pass":False,"steps":[],"failure":None}
    report_path=artifact_dir/"preparation-report.json"; attempt=2
    while report_path.exists():
        report_path=artifact_dir/f"preparation-report-{attempt}.json"; attempt+=1
    def save_prep():
        report_path.write_text(json.dumps(prep_report,indent=2,default=str)+"\n",encoding="utf-8")
    save_prep()
    module_dir = artifact_dir / "lib" / "lean" / "Benchmarks"; module_dir.mkdir(parents=True, exist_ok=True)
    dependency_roots = import_roots(packages)
    lean = Path(lean).resolve()
    if not lean.is_file(): raise ValidationError(f"missing Lean executable: {lean}")
    leanc = lean.with_name("leanc.exe" if os.name == "nt" else "leanc")
    if not leanc.is_file(): raise ValidationError(f"missing leanc executable: {leanc}")
    toolchain_lib=(lean.parent.parent/"lib"/"lean").resolve()
    if not toolchain_lib.is_dir(): raise ValidationError(f"missing pinned toolchain library: {toolchain_lib}")
    source = checked_path(SOURCE, ROOT, "native workload source")
    prepared_lib = artifact_dir / "lib" / "lean"
    roots = [prepared_lib, *dependency_roots]
    env = lean_env(roots, artifact_dir / "tmp")
    validation_cmd=[sys.executable,ROOT/"validate_local.py","--lean",lean,"--packages",Path(packages).resolve(),
                    "--output-dir",prepared_lib,"--timeout",str(cap),
                    "--modules","Benchmarks.ApplicationWitnessNative"]
    validation_row=run(validation_cmd,cwd=ROOT,env=env,cap=cap*20)
    prep_report["steps"].append({"phase":"bounded-source-closure","evidence":validation_row}); save_prep()
    closure_report=prepared_lib/"report-selected.json"
    if validation_row["status"]!="completed" or not closure_report.is_file():
        prep_report["failure"]={"phase":"bounded-source-closure","status":validation_row["status"]}; save_prep()
        raise ValidationError(f"bounded source closure failed: {validation_row['status']}")
    dependency_scan = run([lean,"--deps","-R",ROOT,source],cwd=ROOT,env=env,cap=cap)
    prep_report["steps"].append({"phase":"dependency-scan","evidence":dependency_scan}); save_prep()
    if dependency_scan["status"] != "completed":
        prep_report["failure"]={"phase":"dependency-scan","status":dependency_scan["status"]}; save_prep(); raise ValidationError("Lean dependency scan failed")
    olean, ilean = module_dir / "ApplicationWitnessNative.olean", module_dir / "ApplicationWitnessNative.ilean"
    c_file = artifact_dir / "ApplicationWitnessNative.c"
    executable = artifact_dir / ("ApplicationWitnessNative.exe" if os.name == "nt" else "ApplicationWitnessNative")
    compile_cmd = [lean, "-R", ROOT, "-o", olean, "-i", ilean, "-c", c_file, source]
    compile_row = run(compile_cmd, cwd=ROOT, env=env, cap=cap)
    prep_report["steps"].append({"phase":"workload-compile","evidence":compile_row}); save_prep()
    if compile_row["status"] != "completed":
        prep_report["failure"]={"phase":"workload-compile","status":compile_row["status"]}; save_prep(); raise ValidationError(f"Lean preparation failed: {compile_row['status']}")
    link_cmd = [leanc, "-O3", "-o", executable, c_file]
    link_row = run(link_cmd, cwd=ROOT, env=env, cap=cap)
    prep_report["steps"].append({"phase":"native-link","evidence":link_row}); save_prep()
    # A direct link is retained as diagnostic evidence.  In this checkout it
    # cannot resolve imported package symbols without Lake scheduling a 5,920
    # target native closure, so measurement uses the bounded pinned --run
    # backend below instead of triggering that rebuild.
    for path, label in ((olean,"workload olean"),(c_file,"generated C")):
        if not path.is_file(): raise ValidationError(f"preparation did not create {label}: {path}")
    version = run([lean, "--version"], cwd=ROOT, env=env, cap=min(cap,30))
    prep_report["steps"].append({"phase":"toolchain-version","evidence":version}); save_prep()
    if version["status"] != "completed" or "Lean (version 4.30.0" not in version["output"]:
        raise ValidationError("toolchain is not pinned Lean 4.30.0")
    inputs = [source, DRIVER, ROOT/"validate_local.py", ROOT/"examples"/"application"/"manifest.json", *CHECKER_SOURCES, *FIXTURES.values()]
    source_hashes = {str(p.relative_to(ROOT)): sha256(p) for p in inputs}
    closure=json.loads(closure_report.read_text(encoding="utf-8"))
    for module,expected in closure.get("source_sha256",{}).items():
        path=ROOT/Path(*module.split(".")).with_suffix(".lean")
        if not path.is_file() or sha256(path)!=expected: raise ValidationError(f"closure report source mismatch: {module}")
        source_hashes[str(path.relative_to(ROOT))]=expected
    imported = {}
    for line in dependency_scan["output"].splitlines():
        candidate=Path(line.strip().strip('"'))
        if candidate.suffix==".olean" and candidate.is_file():
            candidate=candidate.resolve()
            if not (is_within(candidate, packages) or is_within(candidate, toolchain_lib)):
                raise ValidationError(f"dependency outside declared dependency roots and pinned toolchain: {candidate}")
            imported[str(candidate)]=sha256(candidate)
    for module in ("SpectralGraph.Certificate.WitnessSubspace", "SpectralGraph.Certificate.ProductWitnessSubspace"):
        path=locate_import_artifact(module,roots); imported[str(path)]=sha256(path)
    for module in closure.get("source_sha256",{}):
        path=(prepared_lib/Path(*module.split("."))).with_suffix(".olean").resolve()
        if not path.is_file(): raise ValidationError(f"closure artifact missing: {module}")
        imported[str(path)]=sha256(path)
    closure_modules = set(closure.get("source_sha256", {}))
    direct_external = {}
    for module in sorted(closure_modules):
        path = ROOT / Path(*module.split(".")).with_suffix(".lean")
        for dep in re.findall(r"^import\s+(\S+)", path.read_text(encoding="utf-8"), re.M):
            if dep in closure_modules:
                continue
            artifact = locate_import_artifact(dep, [*roots, toolchain_lib])
            digest = sha256(artifact)
            imported[str(artifact)] = digest
            direct_external[dep] = {"artifact": str(artifact), "sha256": digest}
    if not imported: raise ValidationError("dependency scan found no imported artifacts")
    if not direct_external: raise ValidationError("bounded closure has no bound direct external imports")
    outputs = {str(p.relative_to(artifact_dir)): sha256(p) for p in (olean,ilean,c_file,executable) if p.is_file()}
    manifest = {"schema": MANIFEST_SCHEMA, "source_root": str(ROOT),
        "toolchain": {"lean":str(lean),"lean_sha256":sha256(lean),"version":version["output"].strip(),
                                              "library_root":str(toolchain_lib)},
        "import_roots":[str(p) for p in roots], "source_and_fixture_hashes":source_hashes,
        "validator_bound":True,
        "dependency_provenance":{"manifest":str(ROOT/"lake-manifest.json"),
            "manifest_sha256":sha256(ROOT/"lake-manifest.json"),
            "cache_roots":[str(p) for p in dependency_roots],
            "precedence":"prepared closure first, then package-local roots; pinned toolchain library last",
            "trust":"transitive prebuilt cache artifacts are trusted by recorded path and SHA-256"},
        "direct_external_imports":direct_external,
        "imported_artifact_hashes":imported, "outputs":outputs,
        "commands":{"compile":[str(x) for x in compile_cmd],"standalone_link_attempt":[str(x) for x in link_cmd],
                    "measurement":[str(lean),"--run",str(source),"<fixture>","<case>","<route>","<positive-repeats>"]},
        "preparation":{"bounded_source_closure":validation_row,"closure_report":str(closure_report.relative_to(artifact_dir)),
                       "dependency_scan":dependency_scan,"compile":compile_row,"standalone_link_attempt":link_row},
        "preparation_report":str(report_path.relative_to(artifact_dir)),
        "backend":"pinned Lean --run with source-bound prepared imports",
        "protocol":"<fixture-path> <case> <old|supplied> <positive-repeats>"}
    (artifact_dir/"manifest.json").write_text(json.dumps(manifest,indent=2)+"\n",encoding="utf-8")
    prep_report["pass"]=True; save_prep()
    return manifest


def load_and_validate_manifest(artifact_dir, *, lean=None):
    artifact_dir = checked_path(artifact_dir, VALIDATION_ROOT, "artifact directory")
    path = checked_path(artifact_dir/"manifest.json", artifact_dir, "prepared manifest")
    try: manifest = json.loads(path.read_text(encoding="utf-8"))
    except (OSError,json.JSONDecodeError) as exc: raise ValidationError(f"malformed prepared manifest: {exc}") from exc
    if manifest.get("schema") != MANIFEST_SCHEMA: raise ValidationError("wrong prepared manifest schema")
    if Path(manifest.get("source_root","")).resolve() != ROOT: raise ValidationError("wrong prepared source root")
    roots = [Path(v).resolve() for v in manifest.get("import_roots",[])]
    if not all(path.is_dir() for path in roots): raise ValidationError("missing manifest import root")
    if not roots: raise ValidationError("prepared manifest has no import roots")
    toolchain_lib=Path(manifest.get("toolchain",{}).get("library_root","")).resolve()
    recorded_lean=Path(manifest.get("toolchain",{}).get("lean","")).resolve()
    expected_toolchain_lib=(recorded_lean.parent.parent/"lib"/"lean").resolve()
    if toolchain_lib!=expected_toolchain_lib or not toolchain_lib.is_dir(): raise ValidationError("wrong or missing pinned toolchain library root")
    source_hashes=manifest.get("source_and_fixture_hashes",{})
    required={str(p.relative_to(ROOT)) for p in (SOURCE,DRIVER,ROOT/"examples"/"application"/"manifest.json",*CHECKER_SOURCES,*FIXTURES.values())}
    if not manifest.get("validator_bound"):
        raise ValidationError("prepared manifest does not bind the validator")
    required.add(str((ROOT/"validate_local.py").relative_to(ROOT)))
    if not required.issubset(source_hashes): raise ValidationError("prepared manifest omits required source or fixture hashes")
    for relative, expected in source_hashes.items():
        p = checked_path(ROOT/relative, ROOT, "manifest source/fixture")
        if sha256(p) != expected: raise ValidationError(f"stale source or fixture: {relative}")
    provenance = manifest.get("dependency_provenance", {})
    dep_manifest = provenance.get("manifest")
    if not dep_manifest or not provenance.get("manifest_sha256"):
        raise ValidationError("prepared manifest omits dependency provenance")
    p = checked_path(Path(dep_manifest), ROOT, "dependency manifest")
    if not p.is_file() or sha256(p) != provenance["manifest_sha256"]:
        raise ValidationError("missing or stale dependency manifest")
    if not provenance.get("cache_roots") or not provenance.get("precedence") or not provenance.get("trust"):
        raise ValidationError("prepared manifest has incomplete cache provenance")
    direct_external = manifest.get("direct_external_imports", {})
    if not direct_external:
        raise ValidationError("prepared manifest omits direct external imports")
    for module, record in direct_external.items():
        artifact = Path(record.get("artifact", "")).resolve()
        if str(artifact) not in manifest.get("imported_artifact_hashes", {}):
            raise ValidationError(f"direct external import is not artifact-bound: {module}")
        if not artifact.is_file() or sha256(artifact) != record.get("sha256"):
            raise ValidationError(f"missing or stale direct external import: {module}")
        selected = locate_import_artifact(module, [*roots, toolchain_lib])
        if selected != artifact or sha256(selected) != record.get("sha256"):
            raise ValidationError(f"resolved direct external import differs from bound artifact: {module}")
    if not manifest.get("imported_artifact_hashes"): raise ValidationError("prepared manifest omits imported artifacts")
    for value, expected in manifest.get("imported_artifact_hashes",{}).items():
        p = Path(value).resolve()
        if not (any(is_within(p,r) for r in roots) or is_within(p,toolchain_lib)): raise ValidationError(f"artifact outside import roots: {p}")
        if not p.is_file() or sha256(p) != expected: raise ValidationError(f"missing or stale imported artifact: {p}")
    outputs=manifest.get("outputs",{})
    required_outputs={str(Path("ApplicationWitnessNative.c")),str(Path("lib")/"lean"/"Benchmarks"/"ApplicationWitnessNative.olean")}
    if not required_outputs.issubset(outputs):
        raise ValidationError("prepared manifest omits required generated artifacts")
    for relative, expected in outputs.items():
        p = checked_path(artifact_dir/relative, artifact_dir, "prepared output")
        if sha256(p) != expected: raise ValidationError(f"stale prepared output: {relative}")
    recorded = recorded_lean
    if lean is not None and Path(lean).resolve() != recorded: raise ValidationError("requested Lean differs from prepared toolchain")
    if not recorded.is_file() or sha256(recorded) != manifest["toolchain"].get("lean_sha256"):
        raise ValidationError("prepared toolchain is missing or stale")
    return manifest, [recorded,"--run",SOURCE], roots


def parse_native(row, *, case, route, repeats):
    parsed = dict(row); parsed.update(accepted=False,first_call_ns=None,runtime_ns=None,parse_ns=None,reported_repeats=None)
    if row.get("status") != "completed" or row.get("returncode") != 0:
        parsed["failure_reason"] = row.get("status","subprocess failure"); return parsed
    lines = [x.strip() for x in row.get("output","").splitlines() if x.strip()]
    matches = [m for m in map(RESULT_RE.fullmatch,lines) if m]
    if len(lines) != 1 or len(matches) != 1:
        parsed["failure_reason"] = "expected exactly one structured RESULT line"; return parsed
    got_case,got_route,result,got_repeats,first_call_ns,runtime_ns,parse_ns = matches[0].groups()
    parsed.update(first_call_ns=int(first_call_ns),runtime_ns=int(runtime_ns),parse_ns=int(parse_ns),reported_repeats=int(got_repeats))
    if got_case != case or got_route != route: parsed["failure_reason"] = "wrong case or route metadata"
    elif result != "true": parsed["failure_reason"] = "checker rejected"
    elif int(got_repeats) != repeats: parsed["failure_reason"] = "wrong exact repeat count"
    else: parsed["accepted"] = True
    return parsed


def persist(path, report):
    path = checked_path(path, VALIDATION_ROOT, "measurement report", exists=False)
    path.parent.mkdir(parents=True,exist_ok=True); path.write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")


def measure(*, artifact_dir=DEFAULT_PREPARED, output=DEFAULT_REPORT, trials=3, pilot=1,
            native_cap=30, target_ns=250_000_000, max_repeats=2000, cases=CASES, run=timed, lean=None):
    if trials<3 or pilot<1 or native_cap<=0 or native_cap>30 or target_ns<=0 or max_repeats<1 or max_repeats>2000:
        raise ValidationError("trials >= 3, pilot >= 1, native-cap in 1..30, positive target, max-repeats in 1..2000 required")
    manifest, runner, roots = load_and_validate_manifest(artifact_dir,lean=lean)
    env = lean_env(roots, VALIDATION_ROOT/"tmp"/"measurement")
    report = {"schema":SCHEMA,"pass":False,"phase":"native",
        "environment":{"python":platform.python_version(),"platform":platform.platform()},
        "prepared_manifest":str(Path(artifact_dir).resolve()/"manifest.json"),
        "prepared_manifest_sha256":sha256(Path(artifact_dir).resolve()/"manifest.json"),
        "backend":manifest["backend"],"caps_seconds":{"native":native_cap},
        "target_runtime_ns":target_ns,"max_repeats":max_repeats,"native":{},"failures":[],
        "successful_complete_pairs":0,
        "limitations":["The --run process includes source processing and startup in wall_seconds; runtime_ns excludes both and times only forced checker iterations.",
                       "Fixture JSON parsing and runtime input construction are outside runtime_ns and reported separately as parse_ns.",
                       "A standalone link was infeasible without a prohibited 5,920-target native dependency build; its failed bounded attempt is preserved in preparation-report.json."]}
    persist(output,report)
    def invoke(case,route,repeats,phase,pair=None):
        fixture = checked_path(FIXTURES[case],ROOT,"runtime fixture")
        raw = run([*runner,fixture,case,route,str(repeats)],cwd=ROOT,env=env,cap=native_cap)
        row = parse_native(raw,case=case,route=route,repeats=repeats)
        if not row["accepted"]: report["failures"].append({"phase":phase,"case":case,"route":route,"pair":pair,"evidence":row})
        return row
    for case_index,case in enumerate(cases):
        if case not in CASES: raise ValidationError(f"unknown case: {case}")
        current = {"pilot":{r:[] for r in ROUTES},"trials":[]}; report["native"][case]=current
        persist(output,report)
        # Keep the forced first evaluator call distinct from timed work.  Every
        # calibration sample is a genuine multi-call batch, with a shared
        # repeat count and a hard three-batch/2000-repeat budget.
        for route in ROUTES:
            row = invoke(case, route, 1, "pilot")
            current["pilot"][route].append(row); persist(output,report)
        current["warmup_policy"] = "one forced evaluator call before repeated timer"
        current["first_call_duration_ns"] = {r: (current["pilot"][r][0].get("first_call_ns")
            if current["pilot"][r][0].get("accepted") else None) for r in ROUTES}
        repeats = 2 if max_repeats >= 2 else 1
        batches = []; current["calibration_batches"] = batches
        for batch_index in range(3):
            batch = {"batch": batch_index + 1, "requested_repeats": repeats, "routes": {}}
            batches.append(batch); persist(output,report)
            for route in ROUTES:
                row = invoke(case, route, repeats, "calibration", batch_index + 1)
                batch["routes"][route] = row; persist(output,report)
            accepted = [v for v in batch["routes"].values() if v["accepted"]]
            if len(accepted) < 2:
                break
            # A shared repeat count is adequate only if the faster route also
            # reaches the requested batch duration.  Calibrate from that
            # smaller actual batch/per-call value, never from a route median.
            achieved = min(v["runtime_ns"] for v in accepted)
            per_call = min(v["runtime_ns"] / repeats for v in accepted)
            current["calibration_achieved_ns"] = achieved
            current["calibration_per_call_ns"] = per_call
            if achieved >= target_ns or repeats >= max_repeats or batch_index == 2:
                break
            repeats = min(max_repeats, max(repeats + 1, math.ceil(target_ns / max(1, per_call))))
        current["calibration_batch_limit"] = 3
        current["calibration_target_ns"] = target_ns
        current["calibration_target_ratio"] = current.get("calibration_achieved_ns", 0) / target_ns
        current["calibration_tolerance"] = "achieved batch is at least 80% of the 250 ms target"
        current["calibration_target_reached"] = current.get("calibration_achieved_ns", 0) >= int(0.8 * target_ns)
        current["calibration_cap_limited"] = repeats >= max_repeats and not current["calibration_target_reached"]
        current["chosen_repeats"] = repeats; persist(output,report)
        for index in range(trials):
            order = ROUTES if (index+case_index)%2==0 else tuple(reversed(ROUTES))
            pair = {"pair":index+1,"order":list(order)}; current["trials"].append(pair); persist(output,report)
            for route in order:
                row = invoke(case,route,repeats,"trial",index+1)
                pair[route] = row; persist(output,report)
        complete = [pair for pair in current["trials"] if all(pair[r]["accepted"] for r in ROUTES)]
        current["successful_complete_pairs"] = len(complete)
        current["median_ns_per_check"] = {r:statistics.median(p[r]["runtime_ns"]/repeats for p in complete) if complete else None for r in ROUTES}
        report["successful_complete_pairs"] += len(complete)
        if len(complete)<3: report["failures"].append({"phase":"accounting","case":case,"reason":"fewer than three successful complete pairs","count":len(complete)})
        persist(output,report)
    report["phase"]="complete"; report["pass"]=not report["failures"]; persist(output,report); return report


def add_kernel_measurements(report, *, artifact_dir, output, trials, cap, cases, run=timed):
    """Run fresh, preserved kernel acceptances after native measurement."""
    report["pass"] = False
    report["phase"] = "kernel-preflight"
    persist(output, report)
    manifest, _, roots = load_and_validate_manifest(artifact_dir)
    lean = Path(manifest["toolchain"]["lean"])
    # Never overwrite prior kernel evidence; each invocation gets an immutable
    # fresh directory and records the exact generated source identity.
    work = checked_path(VALIDATION_ROOT/("kernel-evidence-" + str(int(time.time() * 1_000_000))), VALIDATION_ROOT, "kernel evidence", exists=False)
    work.mkdir(parents=True,exist_ok=True)
    env = lean_env(roots,VALIDATION_ROOT/"tmp"/"kernel")
    imports = ("import Benchmarks.ApplicationWitnessNative\n"
        "open SpectralGraph.Certificate SpectralGraphBenchmarks.ApplicationWitness\n")
    report["phase"]="kernel"; report["caps_seconds"]["kernel"]=cap; report["kernel"]={}; persist(output,report)
    for case_index,case in enumerate(cases):
        n,t,c,d=CASE_SPEC[case]; rows=[]; report["kernel"][case]={"trials":rows}
        for index in range(trials):
            order=ROUTES if (index+case_index)%2==0 else tuple(reversed(ROUTES)); pair={"pair":index+1,"order":list(order)}; rows.append(pair)
            for route in order:
                check=(f"checkNegativeSubspace (pathShift {n} ({t}) ({c})) (witness {n}) (diagonal {n} ({t}) ({d}))"
                    if route=="old" else
                    f"checkNegativeSubspaceWithImage (pathShift {n} ({t}) ({c})) (witness {n}) (image {n} ({t}) ({c})) (diagonal {n} ({t}) ({d}))")
                source=work/f"{case}_{route}_{index+1}.lean"
                source.write_text(imports+f"example : {check} = true := by decide +kernel\n",encoding="utf-8")
                pair.setdefault("generated_source_sha256", {})[route] = sha256(source)
                pair[route]=run([lean,source],cwd=ROOT,env=env,cap=cap)
                if pair[route]["status"]!="completed": report["failures"].append({"phase":"kernel","case":case,"route":route,"pair":index+1,"evidence":pair[route]})
                persist(output,report)
            control=work/f"{case}_control_{index+1}.lean"; control.write_text(imports,encoding="utf-8")
            pair.setdefault("generated_source_sha256", {})["control"] = sha256(control)
            pair["control"]=run([lean,control],cwd=ROOT,env=env,cap=cap)
            if pair["control"]["status"]!="completed": report["failures"].append({"phase":"kernel","case":case,"route":"control","pair":index+1,"evidence":pair["control"]})
            persist(output,report)
        complete=[p for p in rows if all(p[r]["status"]=="completed" for r in (*ROUTES,"control"))]
        report["kernel"][case]["successful_complete_pairs"]=len(complete)
        report["kernel"][case]["median_wall_seconds"]={r:statistics.median(p[r]["wall_seconds"] for p in complete) if complete else None for r in (*ROUTES,"control")}
        if len(complete)<3: report["failures"].append({"phase":"kernel-accounting","case":case,"reason":"fewer than three successful complete kernel pairs","count":len(complete)})
        persist(output,report)
    report["phase"]="complete"; report["pass"]=not report["failures"]; persist(output,report); return report


def parser():
    p=argparse.ArgumentParser(description=__doc__); sub=p.add_subparsers(dest="command",required=True)
    prep=sub.add_parser("prepare"); prep.add_argument("--lean",type=Path,required=True); prep.add_argument("--packages",type=Path,required=True)
    prep.add_argument("--artifact-dir",type=Path,default=DEFAULT_PREPARED); prep.add_argument("--cap",type=int,default=180)
    run=sub.add_parser("measure"); run.add_argument("--artifact-dir",type=Path,default=DEFAULT_PREPARED); run.add_argument("--output",type=Path,default=DEFAULT_REPORT)
    run.add_argument("--lean",type=Path); run.add_argument("--trials",type=int,default=3); run.add_argument("--pilot",type=int,default=1)
    run.add_argument("--native-cap",type=int,default=30); run.add_argument("--kernel-cap",type=int,default=180)
    run.add_argument("--target-ns",type=int,default=250_000_000); run.add_argument("--max-repeats",type=int,default=2000)
    run.add_argument("--skip-kernel",action="store_true",help="do not run kernel checks; the report will state that kernel validation was not run")
    return p


def validate_cli_args(a):
    """Validate all CLI constraints before any manifest access or subprocess."""
    if a.command == "prepare" and a.cap <= 0:
        raise ValidationError("cap must be positive")
    if a.command == "measure" and (a.trials < 3 or a.pilot < 1 or a.native_cap <= 0 or a.native_cap > 30
            or (not a.skip_kernel and a.kernel_cap <= 0) or a.target_ns <= 0
            or a.max_repeats < 1 or a.max_repeats > 2000):
        raise ValidationError("invalid measurement CLI options")


def append_preserved_failure(output, phase, exc):
    output = Path(output)
    existing = json.loads(output.read_text(encoding="utf-8")) if output.is_file() else {
        "schema": SCHEMA, "pass": False, "phase": phase, "failures": []}
    existing["pass"] = False
    existing["phase"] = phase
    existing.setdefault("failures", []).append({"phase": phase, "reason": str(exc)})
    persist(output, existing)


def run_measurement_command(a, *, measure_fn=measure, kernel_fn=add_kernel_measurements):
    try:
        result = measure_fn(artifact_dir=a.artifact_dir, output=a.output, trials=a.trials,
            pilot=a.pilot, native_cap=a.native_cap, target_ns=a.target_ns,
            max_repeats=a.max_repeats, lean=a.lean)
    except ValidationError as exc:
        phase = "native-preflight"
        if Path(a.output).is_file():
            phase = json.loads(Path(a.output).read_text(encoding="utf-8")).get("phase", phase)
        append_preserved_failure(a.output, phase, exc)
        raise
    if a.skip_kernel:
        result["kernel"] = {"status": "not-run", "reason":
            "--skip-kernel was requested; this report contains no kernel validation or inherited kernel timing evidence"}
        result["phase"] = "complete"
        result["pass"] = not result["failures"]
        persist(a.output, result)
        return result
    try:
        return kernel_fn(result, artifact_dir=a.artifact_dir, output=a.output,
            trials=a.trials, cap=a.kernel_cap, cases=CASES)
    except ValidationError as exc:
        append_preserved_failure(a.output, "kernel-preflight", exc)
        raise


def main():
    a=parser().parse_args()
    try:
        validate_cli_args(a)
    except ValidationError as exc:
        print(f"FAIL: {exc}"); raise SystemExit(1) from exc
    try:
        if a.command=="prepare":
            prepare(lean=a.lean,packages=a.packages,artifact_dir=a.artifact_dir,cap=a.cap)
            print(f"PASS: prepared {a.artifact_dir.resolve()/'manifest.json'}")
        else:
            result=run_measurement_command(a)
            print(("PASS" if result["pass"] else "FAIL")+f": report {a.output.resolve()}")
            if not result["pass"]: raise SystemExit(1)
    except ValidationError as exc:
        print(f"FAIL: {exc}"); raise SystemExit(1) from exc


if __name__=="__main__": main()
