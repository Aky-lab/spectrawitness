import SpectralGraph.Certificate.ProductWitnessSubspace

/-!
# Bounded supplied-product witness benchmark

The workloads are diagonal rational matrices with standard-basis negative
columns.  The supplied image is exactly `A * U`; timings are diagnostics, not
proofs.  The closed examples below use kernel reduction (`decide`), while the
IO entrypoint measures repeated native checker execution after argument parsing.
Matrix entries are computed on demand inside the measured checks.
-/

namespace SpectralGraphBenchmarks.ProductWitness

open SpectralGraph.Certificate
open Matrix

def ambient (n k : Nat) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => if i = j then if i.val < k then -1 else 1 else 0

def witness (n k : Nat) : Matrix (Fin n) (Fin k) ℚ :=
  fun i j => if i.val = j.val then 1 else 0

def image (n k : Nat) : Matrix (Fin n) (Fin k) ℚ :=
  fun i j => if i.val = j.val then -1 else 0

def diagonal (k : Nat) : Fin k → ℚ := fun _ => -1

def baseline6 : Bool := checkNegativeSubspace (ambient 6 2) (witness 6 2) (diagonal 2)
def supplied6 : Bool :=
  checkNegativeSubspaceWithImage (ambient 6 2) (witness 6 2) (image 6 2) (diagonal 2)
def baseline8 : Bool := checkNegativeSubspace (ambient 8 3) (witness 8 3) (diagonal 3)
def supplied8 : Bool :=
  checkNegativeSubspaceWithImage (ambient 8 3) (witness 8 3) (image 8 3) (diagonal 3)

-- Empty closed cases keep kernel reduction bounded; the scalable cases are
-- measured natively below because matrix multiplication is intentionally the
-- subject of this benchmark.
example : checkNegativeSubspace (ambient 0 0) (witness 0 0) (diagonal 0) = true := by decide
example : checkNegativeSubspaceWithImage (ambient 0 0) (witness 0 0)
    (image 0 0) (diagonal 0) = true := by decide

def selected (case route : String) : Bool :=
  if case = "6x2" then
    if route = "baseline" then baseline6 else supplied6
  else if case = "8x3" then
    if route = "baseline" then baseline8 else supplied8
  else false

def main : IO Unit := do
  let caseName := (← IO.getEnv "SPECTRAL_PRODUCT_CASE").getD "8x3"
  let route := (← IO.getEnv "SPECTRAL_PRODUCT_ROUTE").getD "baseline"
  unless (caseName = "6x2" || caseName = "8x3") &&
      (route = "baseline" || route = "supplied") do
    throw (IO.userError "case must be 6x2 or 8x3; route must be baseline or supplied")
  let repeats := ((← IO.getEnv "SPECTRAL_PRODUCT_REPEATS").getD "10").toNat!
  let start ← IO.monoNanosNow
  let result ← loop caseName route repeats false
  let stop ← IO.monoNanosNow
  unless result do throw (IO.userError "workload was rejected")
  IO.println s!"RESULT|{caseName}|{route}|{result}"
  IO.println s!"RUNTIME_NS|{stop - start}|{repeats}"
where
  loop : String → String → Nat → Bool → IO Bool
  | _, _, 0, last => pure last
  | caseName, route, fuel + 1, _ =>
      let result := selected caseName route
      if result then loop caseName route fuel result else pure false

end SpectralGraphBenchmarks.ProductWitness
