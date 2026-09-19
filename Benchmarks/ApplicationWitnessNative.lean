import SpectralGraph.Certificate.ProductWitnessSubspace
import Lean

/-! A standalone runtime-input workload for the weighted-path application.

The executable reads the complete ambient matrix, witness, supplied image, and
diagonal from an application fixture before starting its checker timer.  The
non-inlined evaluator calls the public library checkers unchanged on those
runtime values; in particular, the old route retains the library's
left-associated `U.transpose * A * U` computation.
-/
namespace SpectralGraphBenchmarks.ApplicationWitness

open Lean Matrix SpectralGraph.Certificate

structure RuntimeInput where
  matrix : Array ℚ
  witness : Array ℚ
  image : Array ℚ
  diagonal : Array ℚ

/-! Closed canonical constructors remain available only for the separate
kernel-acceptance modules.  The native evaluator below does not call them. -/
def pathShift (n : Nat) (t c : ℚ) : Matrix (Fin n) (Fin n) ℚ := fun i j =>
  if i = j then (if i.val = 0 || i.val = n - 1 then 1 - t + c else 2 - t)
  else if (i.val + 1 = j.val) || (j.val + 1 = i.val) then -1
  else if (i.val = 0 && j.val = n - 1) || (j.val = 0 && i.val = n - 1) then -c
  else 0

def witness (n : Nat) : Matrix (Fin n) (Fin 2) ℚ := fun i j =>
  if j.val = 0 then 1 else (2 : ℚ) * i.val - (n - 1 : ℚ)

def image (n : Nat) (t c : ℚ) : Matrix (Fin n) (Fin 2) ℚ := fun i j =>
  if j.val = 0 then -t
  else
    let x : ℚ := (2 : ℚ) * i.val - (n - 1 : ℚ)
    if i.val = 0 then -2 - t * x - (2 * (n - 1) : ℚ) * c
    else if i.val = n - 1 then 2 - t * x + (2 * (n - 1) : ℚ) * c
    else -t * x

def diagonal (n : Nat) (t : ℚ) (d : ℚ) : Fin 2 → ℚ := fun j =>
  if j.val = 0 then -(n : ℚ) * t else d

private def fail {α : Type} (message : String) : Except String α := .error message

private def parseRatString (text : String) : Except String ℚ := do
  match text.splitOn "/" with
  | [numerator] =>
      let some value := numerator.toInt? | fail s!"invalid integer: {text}"
      pure (value : ℚ)
  | [numerator, denominator] =>
      let some num := numerator.toInt? | fail s!"invalid numerator: {text}"
      let some den := denominator.toInt? | fail s!"invalid denominator: {text}"
      if den = 0 then fail s!"zero denominator: {text}" else pure ((num : ℚ) / (den : ℚ))
  | _ => fail s!"invalid rational: {text}"

private def parseRat (json : Json) : Except String ℚ :=
  match json.getInt? with
  | .ok value => pure (value : ℚ)
  | .error _ => json.getStr? >>= parseRatString

private def parseMatrix (name : String) (rows columns : Nat) (json : Json) : Except String (Array ℚ) := do
  let sourceRows ← json.getArr?
  unless sourceRows.size = rows do fail s!"{name}: expected {rows} rows"
  let mut values := #[]
  for rowJson in sourceRows do
    let row ← rowJson.getArr?
    unless row.size = columns do fail s!"{name}: expected {columns} columns"
    for valueJson in row do values := values.push (← parseRat valueJson)
  unless values.size = rows * columns do fail s!"{name}: wrong flattened size"
  pure values

private def parseInput (expectedN : Nat) (json : Json) : Except String RuntimeInput := do
  let n ← (← json.getObjVal? "n").getNat?
  unless n = expectedN do fail s!"fixture n={n}, expected n={expectedN}"
  let witnessObject ← json.getObjVal? "witness"
  let k ← (← witnessObject.getObjVal? "k").getNat?
  unless k = 2 do fail s!"fixture k={k}, expected k=2"
  let matrix ← parseMatrix "matrix" n n (← json.getObjVal? "matrix")
  let witness ← parseMatrix "witness.U" n k (← witnessObject.getObjVal? "U")
  let image ← parseMatrix "witness.W" n k (← witnessObject.getObjVal? "W")
  let gram ← parseMatrix "witness.gram" k k (← witnessObject.getObjVal? "gram")
  unless gram[1]! = 0 && gram[2]! = 0 do fail "witness.gram: off-diagonal entry is nonzero"
  pure { matrix, witness, image, diagonal := #[gram[0]!, gram[3]!] }

private def matrixOfArray {rows columns : Nat} (values : Array ℚ) :
    Matrix (Fin rows) (Fin columns) ℚ :=
  fun i j => values[i.val * columns + j.val]!

private def diagonalOfArray (values : Array ℚ) : Fin 2 → ℚ :=
  fun j => values[j.val]!

/-- Non-inlined so generated-code inspection can verify a call on runtime
arguments in each iteration. -/
@[noinline] def evaluate {n : Nat} (route : String) (input : RuntimeInput) : Bool :=
  let A : Matrix (Fin n) (Fin n) ℚ := matrixOfArray input.matrix
  let U : Matrix (Fin n) (Fin 2) ℚ := matrixOfArray input.witness
  let W : Matrix (Fin n) (Fin 2) ℚ := matrixOfArray input.image
  let d : Fin 2 → ℚ := diagonalOfArray input.diagonal
  if route = "old" then checkNegativeSubspace A U d
  else checkNegativeSubspaceWithImage A U W d

/-! Keep the repeat wrapper distinct from the evaluator: the measured batch
includes both this loop and every runtime evaluator call. -/
@[noinline] private def repeatEvaluate {n : Nat} (route : String) (input : RuntimeInput) : Nat → Bool
  | 0 => true
  | repeats + 1 => evaluate (n := n) route input && repeatEvaluate (n := n) route input repeats

/-! Force and validate a separate first evaluator call before the measured
batch.  Its duration is reported independently so it cannot be folded into a
per-repeat measurement. -/
private def runFirstCall {n : Nat} (route : String) (input : RuntimeInput) : IO Nat := do
  let start ← IO.monoNanosNow
  let result := evaluate (n := n) route input
  unless result do throw (IO.userError "first evaluator call was rejected")
  let stop ← IO.monoNanosNow
  pure (stop - start)

private def runCase {n : Nat} (route : String) (repeats : Nat) (input : RuntimeInput) : IO Nat := do
  let start ← IO.monoNanosNow
  let result := repeatEvaluate (n := n) route input repeats
  unless result do throw (IO.userError "repeated evaluator call was rejected")
  let stop ← IO.monoNanosNow
  pure (stop - start)

private def usage : String :=
  "usage: ApplicationWitnessNative <fixture-path> <n6|n8|n12> <old|supplied> <positive-repeats>"

private def liftExcept {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError message)

def main (args : List String) : IO UInt32 := do
  let [fixturePath, caseName, route, repeatText] := args
    | throw (IO.userError usage)
  unless route = "old" || route = "supplied" do
    throw (IO.userError "route must be exactly old or supplied")
  let some repeats := repeatText.toNat? | throw (IO.userError "repeats must be a positive decimal integer")
  unless repeats > 0 do throw (IO.userError "repeats must be positive")
  let parseStart ← IO.monoNanosNow
  let contents ← IO.FS.readFile fixturePath
  let json ← liftExcept (Json.parse contents)
  let expectedN ← match caseName with
    | "n6" => pure 6
    | "n8" => pure 8
    | "n12" => pure 12
    | _ => throw (IO.userError "case must be exactly n6, n8, or n12")
  let input ← liftExcept (parseInput expectedN json)
  let parseStop ← IO.monoNanosNow
  let firstCallNs ← match caseName with
    | "n6" => runFirstCall (n := 6) route input
    | "n8" => runFirstCall (n := 8) route input
    | "n12" => runFirstCall (n := 12) route input
    | _ => throw (IO.userError "unreachable case")
  let runtimeNs ← match caseName with
    | "n6" => runCase (n := 6) route repeats input
    | "n8" => runCase (n := 8) route repeats input
    | "n12" => runCase (n := 12) route repeats input
    | _ => throw (IO.userError "unreachable case")
  IO.println s!"RESULT|case={caseName}|route={route}|result=true|repeats={repeats}|first_call_ns={firstCallNs}|runtime_ns={runtimeNs}|parse_ns={parseStop - parseStart}"
  pure 0

end SpectralGraphBenchmarks.ApplicationWitness

def main (args : List String) : IO UInt32 := SpectralGraphBenchmarks.ApplicationWitness.main args
