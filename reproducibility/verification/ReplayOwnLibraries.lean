import LeanChecker
open Lean
unsafe def replayOwnLibrary : IO Unit := do
  initSearchPath (← findSysroot)
  let requested : Array Name := #[
    `BanachDensityHD.AppendixA,
    `BanachDensityHD.AppendixAConstruction,
    `BanachDensityHD.Basic,
    `BanachDensityHD.Characterization,
    `BanachDensityHD.CharacterizationProofs,
    `BanachDensityHD.CharacterizationSuff,
    `BanachDensityHD.CharacterizationSuff2,
    `BanachDensityHD.Endpoint,
    `BanachDensityHD.ExactStatements.BlockForcing,
    `BanachDensityHD.ExactStatements.Commitments,
    `BanachDensityHD.ExactStatements.ConditionalRectangle,
    `BanachDensityHD.ExactStatements.CopyEnumeration,
    `BanachDensityHD.ExactStatements.CopyForest,
    `BanachDensityHD.ExactStatements.CopyNormalization,
    `BanachDensityHD.ExactStatements.CopyOccurrences,
    `BanachDensityHD.ExactStatements.CopySchedule,
    `BanachDensityHD.ExactStatements.OnPlayPotential,
    `BanachDensityHD.ExactStatements.OnPlayRectangle,
    `BanachDensityHD.ExactStatements.PaperExports,
    `BanachDensityHD.ExactStatements.PositiveThreshold,
    `BanachDensityHD.ExactStatements.ProfileInternal,
    `BanachDensityHD.ExactStatements.SewingPositive,
    `BanachDensityHD.ExactStatements.TreeMap,
    `BanachDensityHD.ExactStatements.VertexCharacterization,
    `BanachDensityHD.ExactStatements.VertexRealization,
    `BanachDensityHD.FiniteRank,
    `BanachDensityHD.Forest,
    `BanachDensityHD.Game,
    `BanachDensityHD.Histories,
    `BanachDensityHD.Nov1.CutoffTransport,
    `BanachDensityHD.Nov1.GeneratorTransport,
    `BanachDensityHD.Nov1.IntervalBounds,
    `BanachDensityHD.Nov1.IntervalFiltered,
    `BanachDensityHD.Nov1.LocalRectangle,
    `BanachDensityHD.Nov1.LogNormalization,
    `BanachDensityHD.Nov1.ModelBridge,
    `BanachDensityHD.Nov1.OrdinaryFiltered,
    `BanachDensityHD.Nov1.ProfileRealization,
    `BanachDensityHD.Nov1.ProfileRegion,
    `BanachDensityHD.Nov1.RayEquivalence,
    `BanachDensityHD.Nov1.RayRectangles,
    `BanachDensityHD.Nov1.ThresholdTransport,
    `BanachDensityHD.Oct31Bridges,
    `BanachDensityHD.OneD,
    `BanachDensityHD.Separation,
    `BanachDensityHD.Sewing,
    `BanachDensityHD.TreeCorrespondence.Basic,
    `BanachDensityHD.TreeCorrespondence.ClosureRoute,
    `BanachDensityHD.TreeCorrespondence.Decoration,
    `BanachDensityHD.TreeCorrespondence.Occurrence,
    `BanachDensityHD.TreeCorrespondence.OccurrencePruning,
    `BanachDensityHD.TreeCorrespondence.ProofRoute,
    `BanachDensityHD.TreeCorrespondence.Pruning,
    `BanachDensityHD.TreeCorrespondence.VertexObstruction,
    `BanachDensityHD.Trees,
    `BanachDensity1D.Basic,
    `BanachDensity1D.Capture,
    `BanachDensity1D.Chains,
    `BanachDensity1D.Construction,
    `BanachDensity1D.Density,
    `BanachDensity1D.Examples,
    `BanachDensity1D.Extension,
    `BanachDensity1D.Forest,
    `BanachDensity1D.Foundations,
    `BanachDensity1D.HistoryTopology,
    `BanachDensity1D.Nov1.Balanced,
    `BanachDensity1D.Nov1.FullRange,
    `BanachDensity1D.Nov1.Intervals,
    `BanachDensity1D.Nov1.Profile.Atoms,
    `BanachDensity1D.Nov1.Profile.BlockSums,
    `BanachDensity1D.Nov1.Profile.Blocks,
    `BanachDensity1D.Nov1.Profile.Construction,
    `BanachDensity1D.Nov1.Profile.Core,
    `BanachDensity1D.Nov1.Profile.Counting,
    `BanachDensity1D.Nov1.Profile.CutRefinement,
    `BanachDensity1D.Nov1.Profile.Cutoffs,
    `BanachDensity1D.Nov1.Profile.FilteredAdversary,
    `BanachDensity1D.Nov1.Profile.FilteredRace,
    `BanachDensity1D.Nov1.Profile.FilteredWindows,
    `BanachDensity1D.Nov1.Profile.IntegerLower,
    `BanachDensity1D.Nov1.Profile.LateBlocks,
    `BanachDensity1D.Nov1.Profile.LayerScores,
    `BanachDensity1D.Nov1.Profile.Layers,
    `BanachDensity1D.Nov1.Profile.Layout,
    `BanachDensity1D.Nov1.Profile.LowerConstruction,
    `BanachDensity1D.Nov1.Profile.MechanicalSurplus,
    `BanachDensity1D.Nov1.Profile.Packing,
    `BanachDensity1D.Nov1.Profile.PaddedSums,
    `BanachDensity1D.Nov1.Profile.Requirements,
    `BanachDensity1D.Nov1.Profile.Scales,
    `BanachDensity1D.Nov1.Profile.Schedule,
    `BanachDensity1D.Nov1.Profile.Selection,
    `BanachDensity1D.Nov1.Profile.StageSurplus,
    `BanachDensity1D.Nov1.Profile.Stages,
    `BanachDensity1D.Nov1.Profile.Stride,
    `BanachDensity1D.Nov1.Profile.Surplus,
    `BanachDensity1D.Nov1.Profile.TreeRequirements,
    `BanachDensity1D.Nov1.Profile.Trees,
    `BanachDensity1D.Nov1.Profile.UniformWitness,
    `BanachDensity1D.Nov1.Profile.UpperConstruction,
    `BanachDensity1D.Nov1.Profile.WitnessSurplus,
    `BanachDensity1D.Nov1.Profile.WordCounting,
    `BanachDensity1D.Nov1.Profile.WordStatistics,
    `BanachDensity1D.Nov1.Profile.Words,
    `BanachDensity1D.Nov1.Relabel,
    `BanachDensity1D.Nov1.Scores,
    `BanachDensity1D.Nov1.Upper,
    `BanachDensity1D.Nov1.Witness,
    `BanachDensity1D.Oct31Bridges,
    `BanachDensity1D.PriorZeroValue.Construction,
    `BanachDensity1D.PriorZeroValue.Correspondence,
    `BanachDensity1D.PriorZeroValue.Scores,
    `BanachDensity1D.PriorZeroValue.Trees,
    `BanachDensity1D.PriorZeroValue,
    `BanachDensity1D.ProtRoute,
    `BanachDensity1D.Theorems,
    `BanachDensity1D.Upper]
  withImportModules (requested.map fun m => { module := m }) {} fun source => do
    let mut own : Std.HashMap Name ConstantInfo := {}
    let mut unsafeNames : Array String := #[]
    let mut theoremCount := 0
    for (n, ci) in source.constants.toList do
      let ours := match source.getModuleIdxFor? n with
        | some i =>
          let m := source.header.moduleNames[i.toNat]!
          (`BanachDensityHD).isPrefixOf m || (`BanachDensity1D).isPrefixOf m
        | none => false
      if ours then
        own := own.insert n ci
        if ci.isUnsafe || ci.isPartial then unsafeNames := unsafeNames.push n.toString
        if ci matches .thmInfo _ then theoremCount := theoremCount + 1
    let present := source.header.moduleNames.filter fun m =>
      (`BanachDensityHD).isPrefixOf m || (`BanachDensity1D).isPrefixOf m
    for m in requested do
      unless present.contains m do throw <| IO.userError s!"MISSING_MODULE {m}"
    for n in unsafeNames do
      unless n.endsWith "._unsafe_rec" do
        throw <| IO.userError s!"UNEXPECTED_UNSAFE_OR_PARTIAL {n}"
    IO.println s!"COMPILER_ONLY_UNSAFE_RECURSION_ARTIFACTS {unsafeNames}"
    IO.println s!"PROJECT_REPLAY_PLAN {Json.compress <| Json.mkObj [
      ("requested_modules", toJson (requested.map Name.toString)),
      ("present_project_modules", toJson (present.map Name.toString)),
      ("project_constant_count", toJson own.size),
      ("project_theorem_count", toJson theoremCount),
      ("unsafe_or_partial", toJson unsafeNames)]}"
    withImportModules #[{module := `Mathlib}] {} fun base => do
      for (n, _) in own.toList do
        if (base.find? n).isSome then
          throw <| IO.userError s!"PROJECT_NAME_ALREADY_IN_BASE {n}"
      IO.println "BASE_CONTAINS_NO_PROJECT_DECLARATIONS"
      let checked ← base.toKernelEnv.replay own
      for (n, ci) in own.toList do
        if !ci.isUnsafe && !ci.isPartial then
          unless (checked.find? n).isSome do
            throw <| IO.userError s!"MISSING_AFTER_REPLAY {n}"
      IO.println s!"COMPLETE_OWN_LIBRARY_KERNEL_REPLAY_OK {own.size - unsafeNames.size} logical constants; {theoremCount} theorems; {unsafeNames.size} compiler-only unsafe recursion artifacts skipped by the installed replay API"
#eval replayOwnLibrary
