import BanachDensityHD.Examples

/-!
# Index: LaTeX results and their Lean declarations

Historical module index; numbering below belongs to the original source version.
Use the release theorem/definition registries for the current 65 numbered assertions.
The one-dimensional declarations are included in the `BanachDensity1D` library.

| Result | Lean declaration |
|---|---|
| Question 1.1 | not formalized (no formal content: the guiding question) |
| Definition 1.2 | not formalized (out of scope: lower asymptotic density, previously published) |
| Definition 1.3 | `banach` (extended-real valued, literal), with `banach_tendsto`, `banach_eq_deltaH_one` |
| Theorem 1.4 | not formalized (out of scope: previously published) |
| Theorem 1.5 | not formalized (out of scope: previously published) |
| Theorem 1.6 | not formalized (out of scope: previously published) |
| Theorem 1.7 | not formalized (out of scope: previously published) |
| Definition 1.8 | `GoodG`, `filterFn` |
| Definition 1.9 | `filtered` |
| Theorem 1.10 | not formalized (out of scope: previously published) |
| Theorem 1.11 | not formalized here (one-dimensional; verified in the 1D library as BanachDensity1D.thm_intro_one_dimensional) |
| Corollary 1.12 | not formalized here (one-dimensional; verified in the 1D library as BanachDensity1D.cor_intro_one_dimensional_rank) |
| Theorem 1.13 | `thm_intro_higher_nonsimultaneous` (uniform formulation), with `SeparatesWith` |
| Definition 1.14 | `Achievable` (unlabelled in the source), with `dH`, `deltaH`, `testInf`, `deltaH_tendsto` |
| Definition 2.1 | `PointRank`, `FiniteCBRank`, with `evidenceTopology`, `cbDerived` (finite-evidence topology); `finiteCBRank_pointRank`: finite rank of the family gives every language a point rank |
| Theorem 2.2 | not formalized here (one-dimensional; verified in the 1D library) |
| Definition 3.1 | not formalized here (one-dimensional; verified in the 1D library) |
| Claim 3.2 | not formalized here (one-dimensional; verified in the 1D library) |
| Definition 3.3 | `def_aot` (ported from the 1D library’s dimension-free definition, with `LTree`, `LTree.Admissible`, `LTree.paths`; used by Corollary 8.8) |
| Claim 3.4 | not formalized here (one-dimensional; verified in the 1D library) |
| Theorem 3.5 | not formalized here (one-dimensional; verified in the 1D library) |
| Theorem 3.6 | not formalized here (one-dimensional; verified in the 1D library) |
| Lemma 4.1 | not formalized here (one-dimensional; verified in the 1D library) |
| Corollary 4.2 | not formalized here (one-dimensional; verified in the 1D library) |
| Theorem 5.1 | not formalized here (one-dimensional; verified in the 1D library) |
| Lemma 5.2 | not formalized here (one-dimensional; verified in the 1D library) |
| Theorem 6.1 | not formalized here (one-dimensional; verified in the 1D library) |
| Definition 6.2 | not formalized here (one-dimensional; verified in the 1D library) |
| Definition 6.3 | `opensets` (ported from the 1D library’s dimension-free definition, with `InBasic`, `historyTopology`; used by Theorem 8.7 and Corollaries 8.8–8.9) |
| Lemma 6.4 | HD form: `HistoriesAux.lem_history_topology_gen` (generalized from ℤ to an arbitrary type, in particular ℤ^d; the one-dimensional statement was verified in the 1D library) |
| Lemma 6.5 | not formalized here (one-dimensional; verified in the 1D library) |
| Lemma 6.6 | HD form: `HistoriesAux.lem_obstruction_closure_gen` (generalized from ℤ to a countable type, in particular ℤ^d; used by Theorem 8.7 and Corollary 8.8; the one-dimensional statement was verified in the 1D library) |
| Corollary 6.7 | not formalized here (one-dimensional; verified in the 1D library) |
| Theorem 6.8 | not formalized here (one-dimensional; verified in the 1D library) |
| Theorem 6.9 | not formalized here (one-dimensional; verified in the 1D library) |
| Corollary 6.10 | not formalized here (one-dimensional; verified in the 1D library) |
| Remark 1 | not formalized here (one-dimensional; verified in the 1D library) |
| Definition 6.11 | not formalized here (one-dimensional; verified in the 1D library) |
| Remark 2 | not formalized (one-dimensional, no formal content; not formalized in the 1D run either) |
| Lemma 6.12 | not formalized here (one-dimensional; verified in the 1D library) |
| Lemma 6.13 | not formalized here (one-dimensional; verified in the 1D library) |
| Lemma 6.14 | not formalized here (one-dimensional; verified in the 1D library) |
| Lemma 6.15 | not formalized here (one-dimensional; verified in the 1D library) |
| Lemma 6.16 | HD form: `ForestAux.capture_gen` (generalized to the HD forest, the core of Lemma 8.10 for the strict and the nonstrict scan; the one-dimensional statement was verified in the 1D library) |
| Lemma 6.17 | not formalized here (one-dimensional; verified in the 1D library) |
| Lemma 6.18 | `lem_pairing_game` (ported from the verified BanachDensity1D.lem_pairing_game, generalized from finite sets of integers to finite sets of any type) |
| Corollary 6.19 | not formalized here (one-dimensional; verified in the 1D library) |
| Lemma 6.20 | not formalized here (one-dimensional; verified in the 1D library) |
| Lemma 6.21 | not formalized here (one-dimensional; verified in the 1D library) |
| Lemma 6.22 | not formalized here (one-dimensional; verified in the 1D library) |
| Theorem 6.23 | not formalized here (one-dimensional; verified in the 1D library) |
| Theorem 7.1 | `thm_general` |
| Theorem 7.2 | `thm_main_not_simul` (uniform formulation), with `family7_witnesses`, `family7d`, `K0d` |
| Remark 3 | `rem_orientation`, with `stripFamily`, `stripFamily_langClass` |
| Lemma 7.3 | `lem_validity_commitment` |
| Lemma 7.4 | `lem_block`, with `CellForced` |
| Lemma 7.5 | `prop_tradeoff` |
| Claim 7.6 | `claim_horizontal_test` (unlabelled claim in the proof of Lemma 7.5), with `hTest` |
| Theorem 8.1 | `thm_fixed_quota_suff`, `thm_fixed_quota_nec` |
| Theorem 8.2 | `thm_main_broad` (Definition 8.14 as written); `thm_main` is the same theorem for the monotone relation , linked by `copyTree_broad_iff_monotone`; its monotone-to-broad direction is proved through `TreesAux.collapse` (collapsing duplicated levels of a chain in one step), of which `GeomFeasible.insert_dup` is the one-level case, proved separately |
| Theorem 8.3 | `thm_overview` (= `thm_overview_1` and `end_main`) |
| Remark 4 | not formalized (no formal content: comparison with earlier work) |
| Definition 8.4 | `GeomFeasible`, with `StopGame`, `packetGame`, `StopGame.Wins`, `StopGame.Feasible` (unlabelled in the source) |
| Remark 5 | `StopGame.greedy_stop_bound` (one helper for this remark and the parallel paragraph of §8.3.1) |
| Definition 8.5 | `IsProtectedTree`, with `DTree` |
| Definition 8.6 | `IsQGoodDecoration`, with `DecoratedGood` |
| Theorem 8.7 | `thm_topological_protected_tree` |
| Corollary 8.8 | `cor_hd_obstruction` |
| Corollary 8.9 | `cor_topological_protected_set` |
| Lemma 8.10 | `lem_hd_capture`, with `scanParent`, `guess` (and `lem_hd_capture_copy` for accuracy copies) |
| Lemma 8.11 | `lem_sewing` |
| Lemma 8.12 | `lem_hd_help`, with `simStep`, `simRun` |
| Lemma 8.13 | `lem_hd_commitments` |
| Definition 8.14 | `IsBroadCopyProtectedTree` (as written); the alternative monotone formulation is `IsCopyProtectedTree` with `CompatibleCopy` (monotone relation) |
| Lemma 9.1 | `lem_local_rectangle_strategy`, with `claimGame` |
| Theorem 9.2 | `thm_finite_rank_near_half` |
| Theorem 10.1 | `end_main` |
| Lemma 10.2 | `end_strip`, with `stripRun`, `BlackStrat`, `FreshResponder` |
| Definition A.1 | `RegionTree.activationStep` |
| Lemma A.2 | `lem_new_abstract`, with `RegionTree.PotentialProps`, `RegionTree.run` |
| Claim A.3 | `claim_discardsmall`, with `dyadicTree`, `remainder`, `finalPiece` |
| Claim A.4 | `claim_quotassuffice` |
| Proposition A.5 | `prop_cf_conditional`, with `ScaleConditions` |
| Claim A.6 | `claim_cf_potential_existence` |

Supporting declarations without a number of their own: `lem_hd_capture_copy` (capture for accuracy
copies, §8.5), `family7_witnesses` (the explicit witnesses of Theorem 7.2), `thm_overview_1`
(Theorem 8.3(1), for every `τ > 0`, identical in statement to Theorem 9.2), `IsBroadCopyProtectedTree`,
`copyTree_broad_iff_monotone` (the broad/monotone bridge, proved via `TreesAux.collapse`) and `GeomFeasible.insert_dup`
(the one-level case of `TreesAux.collapse`, not used by the bridge), `cn_finite_range`, `cor_bn_open_iff`, `cor_bn_open_iff_pointwise`
(the one-dimensional sentence of §8.3.1).




-/
