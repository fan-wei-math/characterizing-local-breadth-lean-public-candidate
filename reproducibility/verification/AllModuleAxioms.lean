import BanachDensityHD.ExactStatements
import BanachDensityHD.ExactStatements.ConditionalRectangle
import BanachDensityHD.TreeCorrespondence.ClosureRoute
import BanachDensity1D.Oct31Bridges
import Lean
open Lean in
run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames.filter fun m =>
    (`BanachDensityHD).isPrefixOf m || (`BanachDensity1D).isPrefixOf m
  logInfo m!"ALL_PROJECT_MODULES_JSON {toJson (mods.map Name.toString) |>.compress}"
  let mut count : Nat := 0
  for (n, _) in env.constants.toList do
    let ours := match env.getModuleIdxFor? n with
      | some i =>
        let m := env.header.moduleNames[i.toNat]!
        (`BanachDensityHD).isPrefixOf m || (`BanachDensity1D).isPrefixOf m
      | none => false
    if ours then
      count := count + 1
      let ax ← Elab.Command.liftCoreM (collectAxioms n)
      let bad := ax.filter (fun a => !([``propext, ``Classical.choice, ``Quot.sound] : List Name).contains a)
      if !bad.isEmpty then logError m!"NONSTANDARD {n}: {bad}"
      logInfo m!"AXIOMS {n}: {ax}"
  if count < 3000 then logError m!"Unexpectedly small library sweep: {count}"
  logInfo m!"COMPLETE_LIBRARY_DECLARATIONS: {count}; standard axioms only if no errors."
