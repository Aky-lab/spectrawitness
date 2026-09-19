import SpectralGraph.Certificate.NormalizedInteger

/-!
# Bounded coefficient-growth diagnostics

The workload is `3I - Adj(path_n)`, with expected inertia `(n,0,0)`.
Native timings and coefficient traces are diagnostics, not kernel proofs.
The trace follows positive diagonal pivots only; its validity flag checks
that this workload stays in that branch at every elimination step.
-/

namespace SpectralGraphBenchmarks.Growth
open SpectralGraph SpectralGraph.Certificate

def pathShift (n : Nat) : DenseIntMatrix :=
  DenseIntMatrix.ofFn n fun i j ↦
    if i = j then 3 else if i + 1 = j ∨ j + 1 = i then -1 else 0

def coefficientBits (A : DenseIntMatrix) : Nat :=
  A.entries.foldl (fun largest x ↦
    max largest (if x = 0 then 0 else x.natAbs.log2 + 1)) 0

structure GrowthStats where
  maxStoredBits : Nat
  maxBeforeReductionBits : Nat
  positivePivotSteps : Nat
  valid : Bool
  deriving Repr

/-- Independent instrumentation of the positive-pivot branch. A nonpositive
or missing pivot marks the trace invalid instead of silently claiming coverage. -/
def traceGrowth : Nat → DenseIntMatrix → Bool → GrowthStats
  | 0, A, _ => ⟨coefficientBits A, 0, 0, A.order == 0⟩
  | fuel + 1, A, normalized =>
      if A.order = 0 then ⟨coefficientBits A, 0, 0, true⟩
      else match A.firstDiagonalPivotFin? with
      | none => ⟨coefficientBits A, 0, 0, false⟩
      | some p =>
          if A.entry p p ≤ 0 then ⟨coefficientBits A, 0, 0, false⟩
          else
            let raw := A.signedDiagonalRemainder p
            let next := if normalized then raw.normalizeContent else raw
            let tail := traceGrowth fuel next normalized
            ⟨max (coefficientBits A) tail.maxStoredBits,
              max (coefficientBits raw) tail.maxBeforeReductionBits,
              tail.positivePivotSteps + 1, tail.valid⟩

def main : IO Unit := do
  let mode := (← IO.getEnv "SPECTRAL_GROWTH_MODE").getD "normalized"
  unless mode == "baseline" || mode == "normalized" do
    throw (IO.userError "mode must be baseline or normalized")
  let n := ((← IO.getEnv "SPECTRAL_GROWTH_N").getD "16").toNat!
  unless n == 16 || n == 20 || n == 24 do
    throw (IO.userError "bounded growth benchmark only permits orders 16, 20, 24")
  let A := pathShift n
  let normalized := mode == "normalized"
  let resultRef ← IO.mkRef (⟨0, 0, 0⟩ : Inertia)
  let start ← IO.monoNanosNow
  resultRef.set (if normalized then discoverNormalizedIntegerInertia A
    else discoverIntegerInertiaV2 A)
  let stop ← IO.monoNanosNow
  let result ← resultRef.get
  IO.println s!"RESULT|{result.pos}|{result.zero}|{result.neg}"
  IO.println s!"RUNTIME_NS|{stop - start}"
  unless result == (⟨n, 0, 0⟩ : Inertia) do
    throw (IO.userError "unexpected inertia for shifted path workload")
  let statsRef ← IO.mkRef (⟨0, 0, 0, false⟩ : GrowthStats)
  let diagStart ← IO.monoNanosNow
  statsRef.set (traceGrowth n A normalized)
  let diagStop ← IO.monoNanosNow
  let stats ← statsRef.get
  IO.println s!"GROWTH|{stats.maxStoredBits}|{stats.maxBeforeReductionBits}|{stats.positivePivotSteps}|{stats.valid}"
  IO.println s!"DIAGNOSTIC_NS|{diagStop - diagStart}"
  unless stats.valid && stats.positivePivotSteps == n do
    throw (IO.userError "positive-pivot diagnostic did not cover the complete elimination")

end SpectralGraphBenchmarks.Growth
