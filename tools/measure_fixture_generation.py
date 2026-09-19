"""Measure complete exact fixture generation and incremental rectangular images."""
from __future__ import annotations
import hashlib, json, platform, statistics, time
from fractions import Fraction as F
from pathlib import Path
from application_fixtures import application_case, generate, witness_case

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / ".validation" / "application" / "generation.json"

def fractions(value):
    if isinstance(value, dict):
        for v in value.values(): yield from fractions(v)
    elif isinstance(value, list):
        for v in value: yield from fractions(v)
    elif isinstance(value, (int, str)):
        try: yield F(value)
        except (ValueError, ZeroDivisionError): pass

def main():
    OUT.parent.mkdir(parents=True, exist_ok=True)
    complete = []
    for trial in range(3):
        dest = OUT.parent / f"generation-trial-{trial+1}"
        start = time.perf_counter(); generate(dest); complete.append(time.perf_counter()-start)
    cases = {}
    for n in (6,8,12):
        full, construct, image = [], [], []
        data = None
        for _ in range(3):
            start=time.perf_counter(); data=witness_case(n); full.append(time.perf_counter()-start)
            start=time.perf_counter()
            A=[[F(x) for x in row] for row in data["matrix"]]
            U=[[F(1),F(2*i-(n-1))] for i in range(n)]
            construct.append(time.perf_counter()-start)
            start=time.perf_counter()
            W=[[sum((A[i][j]*U[j][k] for j in range(n)),F(0)) for k in range(2)] for i in range(n)]
            image.append(time.perf_counter()-start)
            assert W == [[F(x) for x in row] for row in data["witness"]["W"]]
        qs=list(fractions(data)); fixture=ROOT/"examples"/"application"/f"n{n}_half_witness.json"
        cases[f"n{n}"]={"full_witness_generation_seconds":full,
          "matrix_witness_construction_seconds":construct,"incremental_image_seconds":image,
          "medians_seconds":{"full":statistics.median(full),"construction":statistics.median(construct),
                             "image":statistics.median(image)},
          "fixture_bytes":fixture.stat().st_size,"fixture_sha256":hashlib.sha256(fixture.read_bytes()).hexdigest(),
          "max_numerator_bits":max(abs(q.numerator).bit_length() for q in qs),
          "max_denominator_bits":max(q.denominator.bit_length() for q in qs)}
    sources={}
    for p in (ROOT/"tools"/"application_fixtures.py",Path(__file__)):
        sources[str(p.relative_to(ROOT))]=hashlib.sha256(p.read_bytes()).hexdigest()
    report={"schema":"weighted-path-generation-measurement-v1",
      "environment":{"python":platform.python_version(),"platform":platform.platform()},
      "command":"python tools/measure_fixture_generation.py","complete_generation_seconds":complete,
      "complete_generation_median_seconds":statistics.median(complete),"cases":cases,
      "source_hashes":sources,
      "limitations":["Producer timings are untrusted exact-Python costs, not Lean checking times.",
                     "Full witness generation includes exact inverse and diagonalization discovery."]}
    OUT.write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    print(f"PASS: report {OUT}")

if __name__ == "__main__": main()
