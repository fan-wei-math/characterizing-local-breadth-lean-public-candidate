import BanachDensity1D.Examples

/-!
# Index: LaTeX results and their Lean declarations

Kleinberg–Wei, *Determination of lower Banach density in the KM model*, Part *Dimension one*
(Sections 2–6) with Definition 1.3 (d = 1), Theorem 1.11 and Corollary 1.12. Numbers are those
of the compiled source (`.aux`). Results of the introduction outside the one-dimensional scope
are listed as out of scope.

| Result | Lean declaration |
|---|---|
| Definition 1.2 | not formalized (out of scope: lower asymptotic density, previously published) |
| Definition 1.3 | `def_banach_intro` (dimension one), with `outputDensity` for δ_B(O, K) := δ_B(O ∩ K, K) |
| Theorem 1.4 | not formalized (out of scope: previously published, asymptotic density) |
| Theorem 1.5 | not formalized (out of scope: previously published) |
| Theorem 1.6 | not formalized (out of scope: previously published; its 1/2 bound is re-derived as Corollary 4.2) |
| Theorem 1.7 | not formalized (out of scope: higher dimensions, previously published) |
| Definition 1.8 | not formalized (out of scope: higher dimensions) |
| Definition 1.9 | not formalized (out of scope: higher dimensions) |
| Theorem 1.10 | not formalized (out of scope: higher dimensions, previously published) |
| Theorem 1.11 | `thm_intro_one_dimensional` |
| Corollary 1.12 | `cor_intro_one_dimensional_rank` |
| Theorem 1.13 | not formalized (out of scope: higher dimensions) |
| Definition 1.14 | not formalized (out of scope: higher dimensions; achievable density profiles, tex l.1441, unlabelled in the source) |
| Definition 2.1 | `CBrank`, with `evidenceTopology`, `cbDerived`, `FiniteCBRank` |
| Theorem 2.2 | `thm_main_oneD` |
| Definition 3.1 | `def_raw_pairing_score` |
| Claim 3.2 | `claim_cn_eventual_interval_bound` |
| Definition 3.3 | `def_aot`, with `LTree`, `LTree.Admissible`, `LTree.paths` |
| Claim 3.4 | `claim_bn_tree_path_bound` |
| Theorem 3.5 | `thm_lower` |
| Theorem 3.6 | `thm_topological_bn`, with `bnTop` |
| Lemma 4.1 | `lem_finite_rank_witness` |
| Corollary 4.2 | `cor_finite_rank_b` |
| Theorem 5.1 | `thm_upper` |
| Lemma 5.2 | `lem_upper_race` |
| Theorem 6.1 | `thm_fixed_epsilon` |
| Definition 6.2 | `def_safe_unsafe_history`, with `Safe` |
| Definition 6.3 | `opensets`, with `InBasic`, `historyTopology` |
| Lemma 6.4 | `lem_history_topology` |
| Lemma 6.5 | `lem_finest_history_topology`, with `ContinuationProperty` |
| Lemma 6.6 | `lem_obstruction_closure` |
| Corollary 6.7 | `cor_safety_interior` |
| Theorem 6.8 | `thm_topological_bn_restated` (restatement of Theorem 3.6) |
| Theorem 6.9 | `thm_topological_main`, with `bTop` |
| Corollary 6.10 | `cor_protected_set` |
| Remark 1 | `rem_safety_local_score` |
| Definition 6.11 | `def_history_protected_set` |
| Remark 2 | not formalized (no formal content: comparison with earlier work) |
| Lemma 6.12 | `lem_boards`, with `cutBoard` |
| Lemma 6.13 | `lem_forest_invariant` |
| Lemma 6.14 | `lem_uniform_board` |
| Lemma 6.15 | `lem_memory` |
| Lemma 6.16 | `lem_capture` |
| Lemma 6.17 | `lem_validity` |
| Lemma 6.18 | `lem_pairing_game` |
| Corollary 6.19 | `cor_regular_board_density`, with `Exceptional` |
| Lemma 6.20 | `lem_copies_chain` |
| Lemma 6.21 | `lem_capture_fixed_copy` |
| Lemma 6.22 | `lem_fixed_copy_density` |
| Theorem 6.23 | `thm_oneD_lower_conclusion` |
-/
