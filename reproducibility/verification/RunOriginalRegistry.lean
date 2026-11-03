import BanachDensity1D.Oct31Bridges
import BanachDensityHD.ExactStatements.BlockForcing
import BanachDensityHD.ExactStatements
import Lean
set_option pp.universes false
set_option pp.proofs false
set_option pp.fullNames true

open Lean in
run_cmd do
  let env ← getEnv
  let names : List Name := [
    `BanachDensity1D.PriorZero.prop_prior_zero_value,
    `BanachDensity1D.ProfileAux.Staged.bK_lower,
    `BanachDensity1D.claim_bn_tree_path_bound,
    `BanachDensity1D.claim_cn_eventual_interval_bound,
    `BanachDensity1D.cor_finite_rank_b,
    `BanachDensity1D.cor_full_range,
    `BanachDensity1D.cor_intro_one_dimensional_rank,
    `BanachDensity1D.cor_protected_set,
    `BanachDensity1D.cor_regular_board_density,
    `BanachDensity1D.cor_safety_interior,
    `BanachDensity1D.def_history_protected_set,
    `BanachDensity1D.def_raw_pairing_score,
    `BanachDensity1D.def_safe_unsafe_history,
    `BanachDensity1D.lem_boards,
    `BanachDensity1D.lem_capture_fixed_copy,
    `BanachDensity1D.lem_copies_chain,
    `BanachDensity1D.lem_finest_history_topology,
    `BanachDensity1D.lem_finite_rank_witness,
    `BanachDensity1D.lem_fixed_copy_density,
    `BanachDensity1D.lem_forest_invariant,
    `BanachDensity1D.lem_memory,
    `BanachDensity1D.lem_uniform_board,
    `BanachDensity1D.lem_upper_race,
    `BanachDensity1D.lem_validity,
    `BanachDensity1D.rem_safety_local_score,
    `BanachDensity1D.thm_fixed_epsilon,
    `BanachDensity1D.thm_intro_one_dimensional,
    `BanachDensity1D.thm_lower,
    `BanachDensity1D.thm_main_oneD,
    `BanachDensity1D.thm_oneD_lower_conclusion,
    `BanachDensity1D.thm_topological_bn,
    `BanachDensity1D.thm_topological_bn_restated,
    `BanachDensity1D.thm_topological_main,
    `BanachDensity1D.thm_upper,
    `BanachDensityHD.BlackStrat,
    `BanachDensityHD.CellForced,
    `BanachDensityHD.DecoratedGood,
    `BanachDensityHD.ExactStatements.CopyOccurrenceTree.Protected,
    `BanachDensityHD.ExactStatements.DyadicCopyProtected,
    `BanachDensityHD.ExactStatements.OnPlay.Properties,
    `BanachDensityHD.ExactStatements.OnPlay.of_bookkeeping,
    `BanachDensityHD.ExactStatements.OnPlay.quotas_of_properties,
    `BanachDensityHD.ExactStatements.PlayScaleConditions,
    `BanachDensityHD.ExactStatements.adjacent_copy_ancestry,
    `BanachDensityHD.ExactStatements.all_dyadic_iff_reciprocal,
    `BanachDensityHD.ExactStatements.capture_specified_copy,
    `BanachDensityHD.ExactStatements.commitments_including_final_reply,
    `BanachDensityHD.ExactStatements.conditional_rectangle_on_play,
    `BanachDensityHD.ExactStatements.copyOccurrenceTree_iff,
    `BanachDensityHD.ExactStatements.dyadicQuota,
    `BanachDensityHD.ExactStatements.dyadic_fixed_copy_density_positive,
    `BanachDensityHD.ExactStatements.dyadic_treeFam,
    `BanachDensityHD.ExactStatements.exact_profile_occurrences_positive,
    `BanachDensityHD.ExactStatements.exists_copy_enumeration,
    `BanachDensityHD.ExactStatements.fixed_quota_nec_positive,
    `BanachDensityHD.ExactStatements.fixed_quota_suff_positive,
    `BanachDensityHD.ExactStatements.protected_normalization,
    `BanachDensityHD.ExactStatements.sewing_positive,
    `BanachDensityHD.ExactStatements.staged_bK_exact,
    `BanachDensityHD.ExactStatements.staged_bK_upper,
    `BanachDensityHD.FiniteCBRank,
    `BanachDensityHD.ForestAux.capture_gen,
    `BanachDensityHD.FreshResponder,
    `BanachDensityHD.GeomFeasible,
    `BanachDensityHD.HistoriesAux.lem_history_topology_gen,
    `BanachDensityHD.HistoriesAux.lem_obstruction_closure_gen,
    `BanachDensityHD.InBasic,
    `BanachDensityHD.IsQGoodDecoration,
    `BanachDensityHD.Nov1.local_rectangle_strategy_positive_dimension,
    `BanachDensityHD.Oct31.finite_rank_near_half_all,
    `BanachDensityHD.Oct31.separation_gap_one_sixteenth,
    `BanachDensityHD.PointRank,
    `BanachDensityHD.RegionTree.activationStep,
    `BanachDensityHD.SeparatesWith,
    `BanachDensityHD.StopGame,
    `BanachDensityHD.StopGame.Feasible,
    `BanachDensityHD.StopGame.Wins,
    `BanachDensityHD.StopGame.greedy_stop_bound,
    `BanachDensityHD.TreeCorrespondence.OccurrenceTree.Protected,
    `BanachDensityHD.TreeCorrespondence.PaperDecoration.finite_protection,
    `BanachDensityHD.TreeCorrespondence.PaperObstruction.Address.terminal_root,
    `BanachDensityHD.TreeCorrespondence.PaperObstruction.Address.vertexTree,
    `BanachDensityHD.TreeCorrespondence.all_vertex_obstructions_iff,
    `BanachDensityHD.TreeCorrespondence.exact_vertex_obstruction_characterization,
    `BanachDensityHD.TreeCorrespondence.paperProtectedTree_iff,
    `BanachDensityHD.TreeCorrespondence.paper_topological_characterization,
    `BanachDensityHD.banach,
    `BanachDensityHD.banach_eq_deltaH_one,
    `BanachDensityHD.cbDerived,
    `BanachDensityHD.claim_cf_potential_existence,
    `BanachDensityHD.claim_cf_potential_existence_uniform,
    `BanachDensityHD.claim_discardsmall,
    `BanachDensityHD.claim_horizontal_test,
    `BanachDensityHD.claim_quotassuffice,
    `BanachDensityHD.dH,
    `BanachDensityHD.deltaH,
    `BanachDensityHD.deltaH_tendsto,
    `BanachDensityHD.dyadicTree,
    `BanachDensityHD.end_main,
    `BanachDensityHD.end_strip,
    `BanachDensityHD.evidenceTopology,
    `BanachDensityHD.family7_witnesses,
    `BanachDensityHD.finalPiece,
    `BanachDensityHD.finiteCBRank_pointRank,
    `BanachDensityHD.guess,
    `BanachDensityHD.hTest,
    `BanachDensityHD.historyTopology,
    `BanachDensityHD.lem_block,
    `BanachDensityHD.lem_hd_capture,
    `BanachDensityHD.lem_hd_help,
    `BanachDensityHD.lem_local_rectangle_strategy,
    `BanachDensityHD.lem_pairing_game,
    `BanachDensityHD.lem_validity_commitment,
    `BanachDensityHD.opensets,
    `BanachDensityHD.packetGame,
    `BanachDensityHD.prop_profile_realization,
    `BanachDensityHD.prop_tradeoff,
    `BanachDensityHD.rem_orientation,
    `BanachDensityHD.remainder,
    `BanachDensityHD.scanParent,
    `BanachDensityHD.simRun,
    `BanachDensityHD.simStep,
    `BanachDensityHD.stripFamily_langClass,
    `BanachDensityHD.stripRun,
    `BanachDensityHD.testInf,
    `BanachDensityHD.thm_intro_higher_nonsimultaneous,
    `BanachDensityHD.thm_main_not_simul,
    `BanachDensityHD.thm_overview_1]
  for n in names do
    match env.find? n with
    | none => logError m!"MISSING_MAPPING {n}"
    | some ci =>
      let ty ← Elab.Command.liftTermElabM (Meta.ppExpr ci.type)
      let ax ← Elab.Command.liftCoreM (collectAxioms n)
      let deps := ((ci.value? true).map (fun v => v.getUsedConstants.toList)).getD []
      let j := Json.mkObj [("name", toJson n.toString), ("type", toJson ty.pretty),
        ("axioms", toJson (ax.toList.map Name.toString)),
        ("direct_proof_dependencies", toJson (deps.map Name.toString))]
      logInfo m!"REGISTRY_JSON {j.compress}"
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
