import SpectralGraph
import Lean.Util.CollectAxioms

/-!
# Compiled-environment trust audit

This development command audits every declaration in the public library namespace,
including transitive dependencies. It generates no mathematical theorem and is
kept outside the library and kernel-computation regression modules.
-/

open Lean Elab Command

run_cmd do
  let environment ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut count := 0
  for (name, _) in environment.constants.toList do
    if (`SpectralGraph).isPrefixOf name then
      let dependencies ← collectAxioms name
      let unexpected := dependencies.filter fun dependency ↦ !allowed.contains dependency
      unless unexpected.isEmpty do
        throwError "Unexpected foundational dependencies for {name}: {unexpected}"
      count := count + 1
  if count == 0 then
    throwError "No library declarations found; refusing a vacuous audit"
  logInfo m!"Audited {count} public namespace declarations: only propext, Classical.choice, Quot.sound"
