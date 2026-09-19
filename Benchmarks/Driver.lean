import SpectralGraph.Certificate.NormalizedInteger
import SpectralGraph.Graph.PackedEnumerationFast

/-!
Native evaluation workloads. These report performance, not trusted proofs.
Inputs are read at runtime so closed-term initialization is outside neither
the measured computation nor its input construction.
-/

open SpectralGraph SpectralGraph.Certificate SpectralGraph.Graph

def benchmarkMatrix (n : Nat) : DenseIntMatrix :=
  DenseIntMatrix.ofFn n fun i j ↦
    if i = j then ((i * 5 + 3) % 11 : Int) - 5
    else if i + 1 = j ∨ j + 1 = i then 2
    else if i + 3 = j ∨ j + 3 = i then -1 else 0

def main : IO Unit := do
  let kind := (← IO.getEnv "SPECTRAL_BENCH_KIND").getD "integer"
  let n := ((← IO.getEnv "SPECTRAL_BENCH_N").getD "8").toNat!
  let start ← IO.monoMsNow
  let result ← if kind == "integer" then do
      if n > 20 then throw (IO.userError "baseline integer benchmark supports orders at most 20")
      pure (reprStr (discoverIntegerInertiaV2 (benchmarkMatrix n)))
    else if kind == "normalized" then do
      if n > 80 then throw (IO.userError "normalized benchmark supports orders at most 80")
      pure (reprStr (discoverNormalizedIntegerInertia (benchmarkMatrix n)))
    else if kind == "fast-enumeration" then do
      if n > 8 then throw (IO.userError "fast enumeration benchmark supports orders at most 8")
      pure (toString (packedConnectedDegreeGraphsFast n 3).length)
    else if kind == "enumeration" then do
      if n > 8 then throw (IO.userError "reference enumeration benchmark supports orders at most 8")
      pure (toString (packedConnectedDegreeGraphs n 3).length)
    else throw (IO.userError "unknown benchmark kind")
  -- Force the result before reading the final time.
  IO.println s!"RESULT|{result}"
  let stop ← IO.monoMsNow
  IO.println s!"TIMING|{kind}|{n}|{stop - start}"
