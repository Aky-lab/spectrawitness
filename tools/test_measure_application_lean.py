"""Focused fail-closed and calibration tests for the measurement driver."""
from __future__ import annotations
import argparse, json, os, sys, tempfile, unittest
from pathlib import Path

import measure_application_lean as driver


def completed(output, returncode=0):
    return {"status":"completed" if returncode==0 else "failed", "returncode":returncode,
            "output":output, "wall_seconds":0.01, "command":["controlled"]}


def success(case, route, repeats, runtime=100):
    return completed(f"RESULT|case={case}|route={route}|result=true|repeats={repeats}|first_call_ns=50|runtime_ns={runtime}|parse_ns=7\n")


class DriverTest(unittest.TestCase):
    def setUp(self):
        driver.VALIDATION_ROOT.mkdir(parents=True, exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(dir=driver.VALIDATION_ROOT)
        self.base = Path(self.temp.name)

    def tearDown(self): self.temp.cleanup()

    def prepared(self, name="prepared"):
        artifact = self.base/name; artifact.mkdir()
        executable = artifact/"native.exe"; executable.write_bytes(b"native")
        c_file=artifact/"ApplicationWitnessNative.c"; c_file.write_bytes(b"c")
        workload=artifact/"lib"/"lean"/"Benchmarks"/"ApplicationWitnessNative.olean"
        workload.parent.mkdir(parents=True); workload.write_bytes(b"workload")
        import_root = self.base/f"imports-{name}"; import_root.mkdir()
        imported = import_root/"Controlled"/"External.olean"
        imported.parent.mkdir(parents=True); imported.write_bytes(b"olean")
        toolchain=self.base/f"tc-{name}"; (toolchain/"bin").mkdir(parents=True); (toolchain/"lib"/"lean").mkdir(parents=True)
        lean = toolchain/"bin"/"lean.exe"; lean.write_bytes(b"lean")
        sources = [driver.SOURCE,driver.DRIVER,driver.ROOT/"validate_local.py",driver.ROOT/"examples"/"application"/"manifest.json",
                   *driver.CHECKER_SOURCES,*driver.FIXTURES.values()]
        manifest = {"schema":driver.MANIFEST_SCHEMA,"source_root":str(driver.ROOT),
            "toolchain":{"lean":str(lean),"lean_sha256":driver.sha256(lean),"version":"Lean (version 4.30.0)",
                         "library_root":str(toolchain/"lib"/"lean")},
            "import_roots":[str(import_root)],
            "source_and_fixture_hashes":{str(p.relative_to(driver.ROOT)):driver.sha256(p) for p in sources},
            "validator_bound":True,
            "dependency_provenance":{"manifest":str(driver.ROOT/"lake-manifest.json"),
                "manifest_sha256":driver.sha256(driver.ROOT/"lake-manifest.json"),
                "cache_roots":[str(import_root)],"precedence":"controlled","trust":"controlled"},
            "direct_external_imports":{"Controlled.External":{"artifact":str(imported),"sha256":driver.sha256(imported)}},
            "imported_artifact_hashes":{str(imported):driver.sha256(imported)},
            "outputs":{"native.exe":driver.sha256(executable),"ApplicationWitnessNative.c":driver.sha256(c_file),
                       str(Path("lib")/"lean"/"Benchmarks"/"ApplicationWitnessNative.olean"):driver.sha256(workload)},
            "executable":"native.exe",
            "backend":"pinned Lean --run with source-bound prepared imports"}
        (artifact/"manifest.json").write_text(json.dumps(manifest),encoding="utf-8")
        return artifact, manifest, imported

    def test_exact_result_parser(self):
        self.assertTrue(driver.parse_native(success("n8","old",3),case="n8",route="old",repeats=3)["accepted"])
        variants = [
            completed("garbage\n"),
            success("n6","old",3),
            success("n8","supplied",3),
            completed("RESULT|case=n8|route=old|result=false|repeats=3|runtime_ns=9|parse_ns=1\n"),
            completed("RESULT|case=n8|route=old|result=true|repeats=3|first_call_ns=0|runtime_ns=9|parse_ns=1\n"),
            success("n8","old",2),
            completed("RESULT|case=n8|route=old|result=true|repeats=3|first_call_ns=1|runtime_ns=9|parse_ns=1\nextra\n"),
            completed("",returncode=2),
            {"status":"timeout","returncode":None,"output":"","wall_seconds":30,"command":["controlled"]},
        ]
        for row in variants:
            with self.subTest(row=row):
                self.assertFalse(driver.parse_native(row,case="n8",route="old",repeats=3)["accepted"])

    def test_failed_pilot_remains_outcome_affecting(self):
        artifact,_,_ = self.prepared(); calls=0
        def run(cmd, **_):
            nonlocal calls; calls += 1
            if calls == 1: return completed("",returncode=1)
            return success(str(cmd[-3]),str(cmd[-2]),int(cmd[-1]),runtime=100)
        output=self.base/"report.json"
        report=driver.measure(artifact_dir=artifact,output=output,cases=("n8",),run=run,
                              trials=3,pilot=1,target_ns=100,max_repeats=10)
        self.assertFalse(report["pass"])
        self.assertEqual(report["native"]["n8"]["successful_complete_pairs"],3)
        self.assertEqual(report["failures"][0]["phase"],"pilot")
        self.assertEqual(json.loads(output.read_text())["phase"],"complete")

    def test_malformed_wrong_metadata_rejection_and_repeat_flow_through_orchestration(self):
        bad_rows=[completed("garbage\n"),success("n6","old",1),
            completed("RESULT|case=n8|route=old|result=false|repeats=1|first_call_ns=2|runtime_ns=10|parse_ns=1\n"),
            success("n8","old",2)]
        for index,bad in enumerate(bad_rows):
            with self.subTest(index=index):
                artifact,_,_=self.prepared(f"prepared-{index}"); calls=0
                def run(cmd, **_):
                    nonlocal calls; calls+=1
                    return bad if calls==1 else success(str(cmd[-3]),str(cmd[-2]),int(cmd[-1]))
                report=driver.measure(artifact_dir=artifact,output=self.base/f"bad-{index}.json",
                    cases=("n8",),run=run,trials=3,pilot=1,target_ns=100,max_repeats=10)
                self.assertFalse(report["pass"]); self.assertEqual(report["failures"][0]["phase"],"pilot")

    def test_success_has_three_complete_alternating_pairs(self):
        artifact,_,_ = self.prepared()
        def run(cmd, **_):
            repeats = int(cmd[-1])
            return success(str(cmd[-3]),str(cmd[-2]),repeats,runtime=50 + 100 * repeats)
        report=driver.measure(artifact_dir=artifact,output=self.base/"success.json",cases=("n8",),
                              run=run,trials=3,pilot=1,target_ns=300,max_repeats=10)
        case=report["native"]["n8"]
        self.assertTrue(report["pass"]); self.assertEqual(case["chosen_repeats"],3)
        self.assertEqual(case["successful_complete_pairs"],3)
        self.assertEqual([p["order"] for p in case["trials"]],
                         [["old","supplied"],["supplied","old"],["old","supplied"]])
        self.assertEqual(case["median_ns_per_check"]["old"],350/3)

    def test_failed_pair_is_excluded_and_accounting_fails(self):
        artifact,_,_ = self.prepared(); calls=0
        def run(cmd, **_):
            nonlocal calls; calls += 1
            if calls == 6: return {"status":"timeout","returncode":None,"output":"","wall_seconds":30,"command":["controlled"]}
            return success(str(cmd[-3]),str(cmd[-2]),int(cmd[-1]),runtime=100)
        report=driver.measure(artifact_dir=artifact,output=self.base/"partial.json",cases=("n8",),
                              run=run,trials=3,pilot=1,target_ns=100,max_repeats=10)
        self.assertFalse(report["pass"])
        self.assertEqual(report["native"]["n8"]["successful_complete_pairs"],2)
        self.assertTrue(any(f["phase"]=="accounting" for f in report["failures"]))

    def test_missing_and_stale_import_artifacts_are_rejected(self):
        artifact,manifest,imported=self.prepared()
        imported.write_bytes(b"stale")
        with self.assertRaisesRegex(driver.ValidationError,"missing or stale (direct external import|imported artifact)"):
            driver.load_and_validate_manifest(artifact)
        imported.unlink()
        with self.assertRaisesRegex(driver.ValidationError,"(missing or stale (direct external import|imported artifact)|no artifact found)"):
            driver.load_and_validate_manifest(artifact)

    def test_direct_external_resolution_rejects_earlier_shadow(self):
        artifact, manifest, imported = self.prepared("shadow")
        earlier = self.base/"imports-shadow-earlier"
        earlier.mkdir()
        manifest["import_roots"] = [str(earlier), str(imported.parents[1])]
        (artifact/"manifest.json").write_text(json.dumps(manifest), encoding="utf-8")
        driver.load_and_validate_manifest(artifact)

        shadow = earlier/"Controlled"/"External.olean"
        shadow.parent.mkdir(parents=True)
        shadow.write_bytes(b"unbound earlier artifact")
        with self.assertRaisesRegex(
                driver.ValidationError,
                "resolved direct external import differs from bound artifact"):
            driver.load_and_validate_manifest(artifact)

    def test_direct_external_resolution_ignores_lower_priority_duplicate(self):
        artifact, manifest, imported = self.prepared("lower-priority")
        lower = self.base/"imports-lower-priority-duplicate"
        duplicate = lower/"Controlled"/"External.olean"
        duplicate.parent.mkdir(parents=True)
        duplicate.write_bytes(b"different but unselected")
        manifest["import_roots"] = [str(imported.parents[1]), str(lower)]
        (artifact/"manifest.json").write_text(json.dumps(manifest), encoding="utf-8")
        driver.load_and_validate_manifest(artifact)

    def test_calibration_is_multi_call_shared_and_reports_warmup(self):
        artifact, _, _ = self.prepared(); calls = []
        def run(cmd, **_):
            repeats = int(cmd[-1]); route = str(cmd[-2]); calls.append(repeats)
            slope = 200 if route == "old" else 100
            return success(str(cmd[-3]), route, repeats, runtime=50 + slope * repeats)
        report = driver.measure(artifact_dir=artifact, output=self.base/"calibration.json",
            cases=("n8",), run=run, trials=3, pilot=1, target_ns=300, max_repeats=2000)
        case = report["native"]["n8"]
        self.assertTrue(report["pass"])
        self.assertEqual(len(case["calibration_batches"]), 2)
        self.assertTrue(all(len(batch["routes"]) == 2 for batch in case["calibration_batches"]))
        self.assertEqual(case["first_call_duration_ns"], {"old": 50, "supplied": 50})
        self.assertTrue(case["calibration_target_reached"])
        self.assertEqual(case["calibration_achieved_ns"], 350)
        self.assertEqual(case["chosen_repeats"], 3)
        self.assertLessEqual(case["chosen_repeats"], 2000)

    def test_calibration_cap_limited_uses_last_measured_shared_count(self):
        artifact, _, _ = self.prepared()
        def run(cmd, **_):
            repeats = int(cmd[-1])
            return success(str(cmd[-3]), str(cmd[-2]), repeats, runtime=10 * repeats)
        report = driver.measure(artifact_dir=artifact, output=self.base/"cap.json",
            cases=("n8",), run=run, trials=3, pilot=1, target_ns=10_000, max_repeats=3)
        case = report["native"]["n8"]
        self.assertEqual(case["chosen_repeats"], 3)
        self.assertTrue(case["calibration_cap_limited"])
        self.assertFalse(case["calibration_target_reached"])
        self.assertTrue(all(set(batch["routes"]) == set(driver.ROUTES) for batch in case["calibration_batches"]))

    def test_source_edit_with_retained_timestamp_is_rejected(self):
        source = self.base/"RetainedTimestamp.lean"
        source.write_text("def measuredValue : Nat := 1\n", encoding="utf-8")
        original_source = driver.SOURCE
        try:
            driver.SOURCE = source
            artifact, _, _ = self.prepared("timestamp")
            stamp = source.stat().st_mtime_ns
            source.write_text("def measuredValue : Nat := 2\n", encoding="utf-8")
            os.utime(source, ns=(stamp, stamp))
            with self.assertRaisesRegex(driver.ValidationError, "stale source or fixture"):
                driver.load_and_validate_manifest(artifact)
        finally:
            driver.SOURCE = original_source

    def test_invalid_cli_is_rejected_before_dispatch_or_report(self):
        output = self.base/"must-not-exist.json"
        args = argparse.Namespace(command="measure", trials=3, pilot=1, native_cap=31,
            kernel_cap=180, target_ns=250_000_000, max_repeats=2000,
            skip_kernel=False, output=output)
        with self.assertRaisesRegex(driver.ValidationError, "invalid measurement CLI options"):
            driver.validate_cli_args(args)
        self.assertFalse(output.exists())

    def test_skip_kernel_reports_not_run_without_adopting_history(self):
        artifact, _, _ = self.prepared("skip-kernel")
        output = self.base / "skip-kernel.json"
        args = argparse.Namespace(artifact_dir=artifact, output=output, trials=3,
            pilot=1, native_cap=30, target_ns=100, max_repeats=10, lean=None,
            kernel_cap=180, skip_kernel=True)
        def native(**kwargs):
            return driver.measure(cases=("n8",), run=lambda cmd, **_: success(
                str(cmd[-3]), str(cmd[-2]), int(cmd[-1]), runtime=100), **kwargs)
        report = driver.run_measurement_command(args, measure_fn=native)
        self.assertEqual(report["kernel"]["status"], "not-run")
        self.assertNotIn("adopted", report["kernel"]["reason"])

    def test_late_manifest_failure_preserves_native_evidence(self):
        output = self.base/"late.json"
        native = {"schema":driver.SCHEMA,"pass":True,"phase":"complete",
            "native":{"n8":{"trials":[{"pair":1,"old":{"accepted":True}}]}},"failures":[]}
        def measure_fn(**_):
            driver.persist(output, native)
            return native
        def kernel_fn(*_, **__):
            raise driver.ValidationError("controlled stale dependency after native work")
        args = argparse.Namespace(artifact_dir=self.base/"unused", output=output, trials=3,
            pilot=1, native_cap=30, target_ns=250_000_000, max_repeats=2000,
            lean=None, kernel_cap=180, skip_kernel=False)
        with self.assertRaisesRegex(driver.ValidationError, "controlled stale dependency"):
            driver.run_measurement_command(args, measure_fn=measure_fn, kernel_fn=kernel_fn)
        saved = json.loads(output.read_text(encoding="utf-8"))
        self.assertFalse(saved["pass"])
        self.assertEqual(saved["phase"], "kernel-preflight")
        self.assertEqual(saved["native"], native["native"])

    def test_native_failure_after_calibration_preserves_four_rows_and_commands(self):
        artifact, _, _ = self.prepared("late-calibration")
        output = self.base/"late-calibration.json"
        snapshots = []
        calls = 0

        def run(cmd, **_):
            nonlocal calls
            calls += 1
            snapshots.append(json.loads(output.read_text(encoding="utf-8")))
            if calls == 5:
                raise driver.ValidationError("controlled validation failure before next calibration invocation")
            repeats = int(cmd[-1])
            row = success(str(cmd[-3]), str(cmd[-2]), repeats, runtime=10 * repeats)
            row["command"] = [str(value) for value in cmd]
            return row

        def measure_fn(**kwargs):
            return driver.measure(cases=("n8",), run=run, **kwargs)

        args = argparse.Namespace(artifact_dir=artifact, output=output, trials=3,
            pilot=1, native_cap=30, target_ns=10_000, max_repeats=10,
            lean=None, kernel_cap=180, skip_kernel=False)
        with self.assertRaisesRegex(driver.ValidationError, "controlled validation failure"):
            driver.run_measurement_command(args, measure_fn=measure_fn)

        first = snapshots[0]["native"]["n8"]
        self.assertEqual(first["pilot"], {route: [] for route in driver.ROUTES})
        self.assertEqual(len(snapshots[1]["native"]["n8"]["pilot"][driver.ROUTES[0]]), 1)
        before_calibration = snapshots[2]["native"]["n8"]
        self.assertEqual([len(before_calibration["pilot"][route]) for route in driver.ROUTES], [1, 1])
        self.assertEqual(before_calibration["calibration_batches"][0]["routes"], {})
        self.assertEqual(set(snapshots[3]["native"]["n8"]["calibration_batches"][0]["routes"]),
                         {driver.ROUTES[0]})
        before_failure = snapshots[4]["native"]["n8"]
        self.assertEqual([len(before_failure["pilot"][route]) for route in driver.ROUTES], [1, 1])
        self.assertEqual(len(before_failure["calibration_batches"]), 2)
        self.assertEqual(before_failure["calibration_batches"][1]["routes"], {})
        self.assertEqual(set(before_failure["calibration_batches"][0]["routes"]), set(driver.ROUTES))
        saved = json.loads(output.read_text(encoding="utf-8"))
        self.assertFalse(saved["pass"])
        case = saved["native"]["n8"]
        rows = [*case["pilot"]["old"], *case["pilot"]["supplied"],
                *case["calibration_batches"][0]["routes"].values()]
        self.assertEqual(len(rows), 4)
        self.assertTrue(all(row["command"] and row["accepted"] for row in rows))

    def test_native_failure_after_partial_trial_preserves_prior_complete_pair(self):
        artifact, _, _ = self.prepared("late-trial")
        output = self.base/"late-trial.json"
        snapshots = []
        calls = 0

        def run(cmd, **_):
            nonlocal calls
            calls += 1
            snapshots.append(json.loads(output.read_text(encoding="utf-8")))
            if calls == 8:
                raise driver.ValidationError("controlled validation failure after one trial route")
            repeats = int(cmd[-1])
            row = success(str(cmd[-3]), str(cmd[-2]), repeats, runtime=100)
            row["command"] = [str(value) for value in cmd]
            return row

        def measure_fn(**kwargs):
            return driver.measure(cases=("n8",), run=run, **kwargs)

        args = argparse.Namespace(artifact_dir=artifact, output=output, trials=3,
            pilot=1, native_cap=30, target_ns=100, max_repeats=10,
            lean=None, kernel_cap=180, skip_kernel=False)
        with self.assertRaisesRegex(driver.ValidationError, "controlled validation failure"):
            driver.run_measurement_command(args, measure_fn=measure_fn)

        before_first_trial = snapshots[4]["native"]["n8"]
        self.assertEqual(before_first_trial["trials"][0].keys(), {"pair", "order"})
        self.assertIn(before_first_trial["trials"][0]["order"][0],
                      snapshots[5]["native"]["n8"]["trials"][0])
        before_second_trial = snapshots[6]["native"]["n8"]
        self.assertTrue(all(route in before_second_trial["trials"][0] for route in driver.ROUTES))
        self.assertEqual(before_second_trial["trials"][1].keys(), {"pair", "order"})
        before_failure = snapshots[7]["native"]["n8"]
        self.assertEqual(len(before_failure["trials"]), 2)
        self.assertTrue(all(route in before_failure["trials"][0] for route in driver.ROUTES))
        partial = before_failure["trials"][1]
        self.assertIn(partial["order"][0], partial)
        self.assertNotIn(partial["order"][1], partial)
        saved = json.loads(output.read_text(encoding="utf-8"))
        self.assertFalse(saved["pass"])
        case = saved["native"]["n8"]
        self.assertEqual([len(case["pilot"][route]) for route in driver.ROUTES], [1, 1])
        self.assertEqual(set(case["calibration_batches"][0]["routes"]), set(driver.ROUTES))
        self.assertTrue(all(case["trials"][0][route]["accepted"] for route in driver.ROUTES))
        completed_route = case["trials"][1][case["trials"][1]["order"][0]]
        self.assertTrue(completed_route["accepted"])
        self.assertTrue(completed_route["command"])

    def test_failed_kernel_work_retains_completed_rows_and_hashes(self):
        artifact, _, _ = self.prepared("kernel")
        output = self.base/"kernel-failure.json"
        report = {"schema":driver.SCHEMA,"pass":True,"phase":"complete",
            "caps_seconds":{"native":30},"native":{"sentinel":"retained"},"failures":[]}
        calls = 0
        def run(_cmd, **_):
            nonlocal calls
            calls += 1
            return completed("", returncode=1 if calls == 2 else 0)
        result = driver.add_kernel_measurements(report, artifact_dir=artifact, output=output,
            trials=3, cap=1, cases=("n8",), run=run)
        self.assertFalse(result["pass"])
        self.assertEqual(result["native"], {"sentinel":"retained"})
        self.assertEqual(len(result["kernel"]["n8"]["trials"]), 3)
        self.assertIn("generated_source_sha256", result["kernel"]["n8"]["trials"][0])
    def test_out_of_root_artifact_directory_is_rejected(self):
        with self.assertRaisesRegex(driver.ValidationError,"outside"):
            driver.load_and_validate_manifest(driver.ROOT/"examples")

    def test_prepare_uses_lean_then_leanc_and_preserves_outputs(self):
        packages=self.base/"packages"; imports=packages/"fake"/".lake"/"build"/"lib"/"lean"
        for module in ("WitnessSubspace","ProductWitnessSubspace"):
            p=imports/"SpectralGraph"/"Certificate"/f"{module}.olean"; p.parent.mkdir(parents=True,exist_ok=True); p.write_bytes(module.encode())
        toolchain=self.base/"toolchain"; (toolchain/"bin").mkdir(parents=True); (toolchain/"lib"/"lean").mkdir(parents=True)
        lean=toolchain/"bin"/"lean.exe"; leanc=toolchain/"bin"/"leanc.exe"
        lean.write_bytes(b"lean"); leanc.write_bytes(b"leanc")
        (toolchain/"lib"/"lean"/"Lean.olean").write_bytes(b"Lean")
        seen=[]
        def run(cmd, **_):
            seen.append([str(x) for x in cmd])
            if len(cmd)>1 and Path(cmd[1]).name=="validate_local.py":
                out=Path(cmd[cmd.index("--output-dir")+1]); out.mkdir(parents=True,exist_ok=True)
                hashes={}
                for source in (driver.SOURCE,):
                    module=".".join(source.relative_to(driver.ROOT).with_suffix("").parts)
                    hashes[module]=driver.sha256(source)
                    p=out/source.relative_to(driver.ROOT).with_suffix(".olean"); p.parent.mkdir(parents=True,exist_ok=True); p.write_bytes(module.encode())
                (out/"report-selected.json").write_text(json.dumps({"modules":3,"source_sha256":hashes}),encoding="utf-8")
                return completed("PASS: 1 controlled module\n")
            if "--version" in cmd: return completed("Lean (version 4.30.0, controlled)\n")
            if Path(cmd[0]).name=="lean.exe":
                for flag,data in (("-o",b"olean"),("-i",b"ilean"),("-c",b"c")):
                    if flag in cmd:
                        p=Path(cmd[cmd.index(flag)+1]); p.parent.mkdir(parents=True,exist_ok=True); p.write_bytes(data)
            else: return completed("unresolved imported package symbols\n",returncode=1)
            return completed("")
        artifact=self.base/"built"
        manifest=driver.prepare(lean=lean,packages=packages,artifact_dir=artifact,run=run)
        self.assertEqual(manifest["backend"],"pinned Lean --run with source-bound prepared imports")
        self.assertTrue((artifact/"ApplicationWitnessNative.c").is_file())
        self.assertFalse((artifact/"ApplicationWitnessNative.exe").exists())
        self.assertEqual(manifest["preparation"]["standalone_link_attempt"]["status"],"failed")
        self.assertTrue((artifact/"preparation-report.json").is_file())
        self.assertEqual([Path(row[0]).name for row in seen],
                         [Path(sys.executable).name,"lean.exe","lean.exe","leanc.exe","lean.exe"])


if __name__ == "__main__": unittest.main()
