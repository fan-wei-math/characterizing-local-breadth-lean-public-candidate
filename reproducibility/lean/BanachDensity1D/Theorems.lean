import BanachDensity1D.Density
import BanachDensity1D.Upper
import BanachDensity1D.Extension
import BanachDensity1D.Foundations

/-!
# The main theorems of Part *Dimension one*

Kleinberg–Wei: Theorem 1.11, Corollary 1.12, Theorem 2.2, Theorem 3.5, Section 4
(Lemma 4.1, Corollary 4.2), Section 5 (Theorem 5.1, Lemma 5.2), Theorem 6.1, Theorem 6.9 and
Theorem 6.23.

Wording kept from the paper:
* Theorems 2.2 (achievability) and 3.5 and 6.9 (achievability) say "every output is available,
  and all but finitely many outputs belong to `K`" (`AllAvailable`, `AlmostAllIn`);
* Theorem 6.1 says only "all but finitely many outputs belong to `K`" (`AlmostAllIn`);
* Theorems 1.11, 6.23 and Corollary 1.12 say "eventually valid" (`EventuallyValid`: from some
  round on, every output is in `K` and available);
* the optimality statements (Theorems 2.2, 5.1, 6.9, 1.11, Corollary 1.12) assume the generator
  is eventually valid on every full enumeration of every language in `X` (`EventuallyValidOn`).

Every generator, in every statement, is a generator of the model (`Generator.Admissible`): at
every round, on every input sequence, its output is available (not an input so far, not an
earlier output). This is the author's model (Section 1.1); it is part of what "generator" means,
not a clause of individual theorems, so the printed wording of each theorem is kept as is.

The file is ordered by dependency (a theorem is stated before the theorems whose proofs use it),
not by the paper's numbering. Theorem 5.1 (`thm_upper`) is in `Upper.lean`.
-/

namespace BanachDensity1D

open Set Filter

/-- The topological value of Theorem 6.9: `lim_{n → ∞} sup_{𝒰 ∋ (K) open} inf_{H ∈ 𝒰} c_n(H)`. -/
noncomputable def bTop (X : Set (Set ℤ)) (K : Set ℤ) : ℝ :=
  limUnder atTop fun n : ℕ => bnTop X K n

namespace TheoremsAux

/-- An admissible generator with finitely many rounds outside `K` is eventually valid. -/
lemma eventuallyValid_of_almostAllIn {G : Generator} (hG : G.Admissible) {w : ℕ → ℤ} {K : Set ℤ}
    (h : G.AlmostAllIn w K) : G.EventuallyValid w K := by
  obtain ⟨M, hM⟩ := h.bddAbove
  refine ⟨M + 1, fun t ht => ⟨?_, hG w t⟩⟩
  by_contra hout
  have := hM hout
  omega

/-- An eventually valid generator has only finitely many rounds with an output outside `K`. -/
lemma almostAllIn_of_eventuallyValid {G : Generator} {w : ℕ → ℤ} {K : Set ℤ}
    (h : G.EventuallyValid w K) : G.AlmostAllIn w K := by
  obtain ⟨t₀, ht⟩ := h
  refine (Set.finite_lt_nat t₀).subset fun t ht' => ?_
  by_contra hlt
  exact ht' (ht t (not_lt.1 hlt)).1

/-- The topological value of Theorem 6.9 is `b(K)`: `b_n(K) = b_n^top(K)` for `n ≥ 1`
(Theorem 3.6), so the two sequences have the same limit. -/
lemma bTop_eq_bK {X : Set (Set ℤ)} (hX : LangClass X) {K : Set ℤ} (hK : K ∈ X) :
    bTop X K = bK X K := by
  have h := (ChainsAux.bK_tendsto (X := X) (hX.infinite K hK)).1
  have h' : Tendsto (bnTop X K) atTop (nhds (bK X K)) :=
    h.congr' (Filter.eventually_atTop.2 ⟨1, fun n hn => thm_topological_bn hX hK hn⟩)
  exact h'.limUnder_eq

end TheoremsAux

/-- **Theorem 6.23** (`thm:oneD-lower-conclusion`). For every nonempty countable class `X` of
infinite subsets of `ℤ`, there is one generator that is eventually valid on every full
enumeration and whose output set `O` satisfies `δ_B(O, K) ≥ b(K)` for every target `K ∈ X`. -/
theorem thm_oneD_lower_conclusion {X : Set (Set ℤ)} (hX : LangClass X) :
    ∃ G : Generator, G.Admissible ∧ G.EventuallyValidOn X ∧
      ∀ K ∈ X, ∀ w, IsFullEnumeration w K → bK X K ≤ outputDensity (G.outputSet w) K := by
  obtain ⟨R, copy, hR⟩ := FoundationsAux.exists_copySystem hX
  obtain ⟨C, hC⟩ := ConstructionAux.exists_valid_choices X R
  have hGa := ConstructionAux.algGen_admissible hX (fun v _ => hR.lab_mem v) hC
  refine ⟨algGen R C, hGa, fun K hK w hw => ?_, fun K hK w hw => ?_⟩
  · obtain ⟨z, hz, -⟩ := hR.surj K hK 1 le_rfl
    subst hz
    exact TheoremsAux.eventuallyValid_of_almostAllIn hGa (CaptureAux.validity_copy hX hR hC hw)
  · have hlim : Tendsto (fun m : ℕ => bK X K - (1 / 2 : ℝ) ^ m) atTop (nhds (bK X K)) := by
      simpa using (tendsto_const_nhds (x := bK X K)).sub
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
    refine le_of_tendsto hlim (Filter.eventually_atTop.2 ⟨1, fun m hm => ?_⟩)
    exact (le_max_left _ _).trans (lem_fixed_copy_density hX hR hC hK hm hw)

/-- **Theorem 6.1** (`thm:fixed-epsilon`). For every `ε > 0` there is one generator `𝒜_ε` such
that on every string enumeration of every `K ∈ X`: all but finitely many outputs belong to `K`,
and the output set satisfies `δ_B(O, K) ≥ (b(K) - ε)_+`. -/
theorem thm_fixed_epsilon {X : Set (Set ℤ)} (hX : LangClass X) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : Generator, G.Admissible ∧ ∀ K ∈ X, ∀ w, IsFullEnumeration w K →
      G.AlmostAllIn w K ∧ max (bK X K - ε) 0 ≤ outputDensity (G.outputSet w) K := by
  obtain ⟨R, hR⟩ := FoundationsAux.exists_fixedEpsSystem hX hε
  obtain ⟨C, hC⟩ := ConstructionAux.exists_valid_choices X R
  refine ⟨algGen R C, ConstructionAux.algGen_admissible hX hR.lab_mem hC, fun K hK w hw => ?_⟩
  obtain ⟨z, hz, rfl⟩ := hR.lab_surj K hK
  refine ⟨lem_validity hX hε hR hC hz hw, ?_⟩
  rw [← hR.q_def z hz]
  exact DensityAux.fixed_density hX hR hC hz hw

/-- **Theorem 3.5** (`thm:lower`). For every nonempty countable class `X` of infinite subsets of
`ℤ`, there is one generator such that, on every complete text of every `K ∈ X`: every output is
available, all but finitely many outputs belong to `K`, and its output set `O` satisfies
`δ_B(O, K) ≥ b(K)`. -/
theorem thm_lower {X : Set (Set ℤ)} (hX : LangClass X) :
    ∃ G : Generator, G.Admissible ∧ ∀ K ∈ X, ∀ w, IsFullEnumeration w K →
      G.AllAvailable w ∧ G.AlmostAllIn w K ∧ bK X K ≤ outputDensity (G.outputSet w) K := by
  obtain ⟨G, hGa, hGv, hGd⟩ := thm_oneD_lower_conclusion hX
  exact ⟨G, hGa, fun K hK w hw => ⟨hGa w,
    TheoremsAux.almostAllIn_of_eventuallyValid (hGv K hK w hw), hGd K hK w hw⟩⟩

/-- **Theorem 2.2** (`thm:main-oneD`, exact structural characterization). Let `X` be a nonempty
countable collection of infinite subsets of `ℤ`.
1. *Achievability.* There is a single generator such that, for every `K ∈ X` and every full
   enumeration of `K`, every output is available, all but finitely many outputs belong to `K`,
   and its output set `O` satisfies `δ_B(O, K) ≥ b(K)`.
2. *Optimality.* Let `𝒜` be any generator that is eventually valid on every full enumeration of
   every language in `X`. Then for every `K ∈ X` there is a full enumeration of `K` on which the
   output set `O` of `𝒜` satisfies `δ_B(O, K) ≤ b(K)`. -/
theorem thm_main_oneD {X : Set (Set ℤ)} (hX : LangClass X) :
    (∃ G : Generator, G.Admissible ∧ ∀ K ∈ X, ∀ w, IsFullEnumeration w K →
      G.AllAvailable w ∧ G.AlmostAllIn w K ∧ bK X K ≤ outputDensity (G.outputSet w) K) ∧
    (∀ G : Generator, G.Admissible → G.EventuallyValidOn X →
      ∀ K ∈ X, ∃ w, IsFullEnumeration w K ∧ outputDensity (G.outputSet w) K ≤ bK X K) := by
  exact ⟨thm_lower hX, fun G hGa hG K hK => thm_upper hX G hGa hG hK⟩

namespace TheoremsAux

/-- Every open set of the finite-evidence topology containing `x` contains a basic set
`U_{x,F}` with `F ⊆ x` finite (the basic sets `U_{L,F}` containing `x` are closed under finite
intersection, refined by `U_{x, F₁ ∪ F₂}`). -/
theorem evidence_nhds_basis {X : Set (Set ℤ)} (U : Set X) (hU : (evidenceTopology X).IsOpen U) :
    ∀ x ∈ U, ∃ F : Set ℤ, F.Finite ∧ F ⊆ x.1 ∧ evidenceSet X x.1 F ⊆ U := by
  change TopologicalSpace.GenerateOpen _ U at hU
  induction hU with
  | basic s hs =>
    obtain ⟨L, -, F, hF, -, rfl⟩ := hs
    intro x hx
    exact ⟨F, hF, hx.1, fun M hM => ⟨hM.1, hM.2.trans hx.2⟩⟩
  | univ =>
    intro x _
    exact ⟨∅, finite_empty, empty_subset _, subset_univ _⟩
  | inter s t _ _ ihs iht =>
    intro x hx
    obtain ⟨F₁, hF₁, hF₁x, h₁⟩ := ihs x hx.1
    obtain ⟨F₂, hF₂, hF₂x, h₂⟩ := iht x hx.2
    refine ⟨F₁ ∪ F₂, hF₁.union hF₂, union_subset hF₁x hF₂x, fun M hM => ⟨?_, ?_⟩⟩
    · exact h₁ ⟨subset_union_left.trans hM.1, hM.2⟩
    · exact h₂ ⟨subset_union_right.trans hM.1, hM.2⟩
  | sUnion S _ ih =>
    rintro x ⟨s, hs, hx⟩
    obtain ⟨F, hF, hFx, hsub⟩ := ih s hs x hx
    exact ⟨F, hF, hFx, hsub.trans (subset_sUnion_of_mem hs)⟩

/-- A language of `X` outside `X^{(r)}` has some rank `r' < r`. -/
theorem exists_rank_of_not_mem {X : Set (Set ℤ)} {M : Set ℤ} (hM : M ∈ X) :
    ∀ {r : ℕ}, (⟨M, hM⟩ : X) ∉ cbDerived X r → ∃ r' < r, CBrank X M r'
  | 0, h => absurd (mem_univ _) h
  | r + 1, h => by
    by_cases hr : (⟨M, hM⟩ : X) ∈ cbDerived X r
    · exact ⟨r, Nat.lt_succ_self r, hM, hr, h⟩
    · obtain ⟨r', hr', hrank⟩ := exists_rank_of_not_mem hM hr
      exact ⟨r', by omega, hrank⟩

end TheoremsAux

/-- **Lemma 4.1** (`lem:finite-rank-witness`). If `L` has finite rank `r`, there is a finite
`F ⊆ L` such that every `M ∈ X` with `F ⊆ M ⊊ L` has rank strictly less than `r`. In particular,
if `r = 0`, no `M ∈ X` satisfies `F ⊆ M ⊊ L`. -/
theorem lem_finite_rank_witness {X : Set (Set ℤ)} {L : Set ℤ} {r : ℕ} (hL : CBrank X L r) :
    ∃ F : Set ℤ, F.Finite ∧ F ⊆ L ∧
      (∀ M ∈ X, F ⊆ M → M ⊂ L → ∃ r' < r, CBrank X M r') ∧
      (r = 0 → ∀ M ∈ X, ¬ (F ⊆ M ∧ M ⊂ L)) := by
  obtain ⟨hLX, hr, hr1⟩ := hL
  have hiso : ∃ U : Set X, (evidenceTopology X).IsOpen U ∧
      U ∩ cbDerived X r = {(⟨L, hLX⟩ : X)} := by
    by_contra hc
    exact hr1 ⟨hr, hc⟩
  obtain ⟨U, hU, hUeq⟩ := hiso
  have hxU : (⟨L, hLX⟩ : X) ∈ U ∩ cbDerived X r := by rw [hUeq]; rfl
  obtain ⟨F, hF, hFL, hsub⟩ := TheoremsAux.evidence_nhds_basis U hU _ hxU.1
  have key : ∀ M ∈ X, F ⊆ M → M ⊂ L → ∃ r' < r, CBrank X M r' := by
    intro M hM hFM hML
    apply TheoremsAux.exists_rank_of_not_mem hM
    intro hMr
    have hmem : (⟨M, hM⟩ : X) ∈ U ∩ cbDerived X r := ⟨hsub ⟨hFM, hML.1⟩, hMr⟩
    rw [hUeq, mem_singleton_iff] at hmem
    exact hML.ne (congrArg Subtype.val hmem)
  refine ⟨F, hF, hFL, key, ?_⟩
  rintro rfl M hM ⟨hFM, hML⟩
  obtain ⟨r', hr', -⟩ := key M hM hFM hML
  exact Nat.not_lt_zero _ hr'

namespace TheoremsAux

/-! Facts for Corollary 4.2 (the facts on `c_n` they use are in `ChainsAux`). -/

/-- `⌊m/2⌋ ≥ (m - 1)/2`. -/
theorem half_floor_ge (m : ℕ) : ((m : ℝ) - 1) / 2 ≤ ((m / 2 : ℕ) : ℝ) := by
  have h : m ≤ 2 * (m / 2) + 1 := by omega
  have h' : (m : ℝ) ≤ 2 * ((m / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h
  linarith

/-- Layers of a strictly descending list with `s` entries:
`∑ ⌊|E ∩ J| / 2⌋ ≥ |head ∩ J| / 2 - s/2` for finite `J`. -/
theorem layers_sum_ge (J : Set ℤ) (hJ : J.Finite) :
    ∀ (L : Set ℤ) (t : List (Set ℤ)), (L :: t).IsChain (fun L M => M ⊂ L) →
      ((L ∩ J).ncard : ℝ) / 2 - ((L :: t).length : ℝ) / 2 ≤
        ((layers (L :: t)).map fun E => (((E ∩ J).ncard / 2 : ℕ) : ℝ)).sum
  | L, [], _ => by
    simp only [layers, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      List.length_singleton, Nat.cast_one]
    have h := half_floor_ge (L ∩ J).ncard
    linarith
  | L, M :: t, h => by
    have hML : M ⊂ L := (List.isChain_cons_cons.mp h).1
    have ht : (M :: t).IsChain (fun L M => M ⊂ L) := (List.isChain_cons_cons.mp h).2
    have ih := layers_sum_ge J hJ M t ht
    simp only [layers, List.map_cons, List.sum_cons] at ih ⊢
    have hfin : (L ∩ J).Finite := hJ.subset inter_subset_right
    have hsub : M ∩ J ⊆ L ∩ J := inter_subset_inter_left _ hML.1
    have hsplit : ((L \ M) ∩ J).ncard + (M ∩ J).ncard = (L ∩ J).ncard := by
      rw [show (L \ M) ∩ J = (L ∩ J) \ (M ∩ J) by ext x; simp; tauto]
      exact ncard_sdiff_add_ncard_of_subset hsub hfin
    have h1 := half_floor_ge ((L \ M) ∩ J).ncard
    have h2 : (((L \ M) ∩ J).ncard : ℝ) + (M ∩ J).ncard = (L ∩ J).ncard := by
      exact_mod_cast hsplit
    have hlen : ((L :: M :: t).length : ℝ) = ((M :: t).length : ℝ) + 1 := by
      simp only [List.length_cons]; push_cast; ring
    rw [hlen]
    linarith

/-- For a strictly descending list `H` with `s` entries and a finite nonempty `J` contained in
its first entry, `p(H, J) ≥ 1/2 - s/(2|J|)`. -/
theorem raw_score_ge {L : Set ℤ} {t : List (Set ℤ)}
    (h : (L :: t).IsChain (fun L M => M ⊂ L)) {J : Set ℤ} (hJL : J ⊆ L) (hJ : J.Finite)
    (hpos : 0 < J.ncard) :
    1 / 2 - ((L :: t).length : ℝ) / (2 * J.ncard) ≤ def_raw_pairing_score (L :: t) J := by
  unfold def_raw_pairing_score
  have hs := layers_sum_ge J hJ L t h
  rw [inter_eq_right.mpr hJL] at hs
  have hp : (0 : ℝ) < J.ncard := by exact_mod_cast hpos
  rw [one_div_mul_eq_div, le_div_iff₀ hp]
  have : (1 / 2 - ((L :: t).length : ℝ) / (2 * J.ncard)) * J.ncard =
      (J.ncard : ℝ) / 2 - ((L :: t).length : ℝ) / 2 := by
    field_simp
  linarith

/-- Following rank-decreasing children (Lemma 4.1) from a vertex whose label has rank `s` gives
a root-to-leaf path with at most `s + 1` entries. -/
theorem exists_short_path {X : Set (Set ℤ)} :
    ∀ (T : LTree) (s : ℕ), T.Admissible X → CBrank X T.label s →
      ∃ P ∈ T.paths, P.length ≤ s + 1
  | .leaf L, s, _, _ => ⟨[L], rfl, by simp⟩
  | .node L c, s, hT, hs => by
    obtain ⟨F, hF, hFL, hlt, -⟩ := lem_finite_rank_witness (X := X) (L := L) hs
    obtain ⟨i, hi⟩ := hT.2 F hF hFL
    obtain ⟨hX, hss, hadm⟩ := hT.1 i
    obtain ⟨s', hs', hrank⟩ := hlt _ hX hi hss
    obtain ⟨Q, hQ, hlen⟩ := exists_short_path (c i) s' hadm hrank
    exact ⟨L :: Q, ⟨i, Q, hQ, rfl⟩, by simp only [List.length_cons]; omega⟩

/-- The bound of Corollary 4.2: if `K` has rank `r` and `n ≥ 1`, then
`b_n(K) ≥ 1/2 - (r+1)/(2n)`. -/
theorem bn_ge_of_rank {X : Set (Set ℤ)} (hX : LangClass X) {K : Set ℤ} {r : ℕ}
    (hK : CBrank X K r) {n : ℕ} (hn : 1 ≤ n) :
    (1 : ℝ) / 2 - (r + 1) / (2 * n) ≤ bn X K n := by
  have hKinf : K.Infinite := hX.infinite K hK.1
  unfold bn
  have : Nonempty {T : LTree // def_aot X K T} := ⟨⟨LTree.leaf K, rfl, trivial⟩⟩
  refine le_ciInf fun T => ?_
  obtain ⟨hlab, hadm⟩ := T.2
  have hrk : CBrank X T.1.label r := by rw [hlab]; exact hK
  have hKT : T.1.label.Infinite := by rw [hlab]; exact hKinf
  obtain ⟨P, hP, hlen⟩ := exists_short_path T.1 r hadm hrk
  refine le_trans ?_ (le_ciSup (ChainsAux.pathSup_bdd hadm hKT n) ⟨P, hP⟩)
  show _ ≤ cn P n
  obtain ⟨⟨t, rfl⟩, hc, -⟩ := ChainsAux.paths_spec X T.1 hadm P hP
  have hA' : (start (T.1.label :: t)).Infinite := by simpa [start] using hKT
  refine ge_of_tendsto' (ChainsAux.cn_tendsto (List.cons_ne_nil _ _) hc hA' n).1 fun R => ?_
  have : Nonempty (farIntervals (T.1.label :: t) n R) :=
    (ChainsAux.farIntervals_nonempty hA' n R).to_subtype
  refine le_ciInf fun J => ?_
  obtain ⟨⟨a, b, hJ⟩, hnJ, -⟩ := J.2
  have hJL : (J : Set ℤ) ⊆ T.1.label := by
    rw [hJ]; exact inter_subset_left
  have hJfin : (J : Set ℤ).Finite := by
    rw [hJ]; exact (finite_Icc a b).subset inter_subset_right
  have hpos : 0 < (J : Set ℤ).ncard := by omega
  refine le_trans ?_ (raw_score_ge hc hJL hJfin hpos)
  have hlen' : (((T.1.label :: t).length : ℕ) : ℝ) ≤ (r : ℝ) + 1 := by exact_mod_cast hlen
  have hnJ' : (n : ℝ) ≤ (J : Set ℤ).ncard := by exact_mod_cast hnJ
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hJ' : (0 : ℝ) < (J : Set ℤ).ncard := by exact_mod_cast hpos
  have e1 : (((T.1.label :: t).length : ℕ) : ℝ) / (2 * (J : Set ℤ).ncard) ≤
      ((r : ℝ) + 1) / (2 * (J : Set ℤ).ncard) := by gcongr
  have e2 : ((r : ℝ) + 1) / (2 * (J : Set ℤ).ncard) ≤ ((r : ℝ) + 1) / (2 * n) := by gcongr
  linarith

/-- If `K` has finite rank, `b(K) = 1/2` (the limit of the bounds of Corollary 4.2). -/
theorem bK_eq_half_of_rank {X : Set (Set ℤ)} (hX : LangClass X) {K : Set ℤ} {r : ℕ}
    (hK : CBrank X K r) : bK X K = 1 / 2 := by
  obtain ⟨hKX, -, -⟩ := id hK
  obtain ⟨ht, -, hle⟩ := ChainsAux.bK_tendsto (X := X) (hX.infinite K hKX)
  refine le_antisymm hle ?_
  have h0 : Tendsto (fun n : ℕ => ((r : ℝ) + 1) / (2 * n)) atTop (nhds 0) := by
    have := tendsto_const_div_atTop_nhds_zero_nat (((r : ℝ) + 1) / 2)
    refine this.congr fun n => ?_
    rw [div_div]
  have hg : Tendsto (fun n : ℕ => (1 : ℝ) / 2 - ((r : ℝ) + 1) / (2 * n)) atTop (nhds (1 / 2)) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ) / 2)).sub h0
  exact le_of_tendsto_of_tendsto hg ht
    (Filter.eventually_atTop.2 ⟨1, fun n hn => bn_ge_of_rank hX hK hn⟩)

/-- Under finite Cantor–Bendixson rank every language has a (finite) rank. -/
theorem rank_of_finiteCBRank {X : Set (Set ℤ)} (hfin : FiniteCBRank X) {L : Set ℤ} (hL : L ∈ X) :
    ∃ r, CBrank X L r := by
  obtain ⟨r, hr⟩ := hfin
  obtain ⟨r', -, h⟩ := exists_rank_of_not_mem hL (r := r) (by rw [hr]; simp)
  exact ⟨r', h⟩

end TheoremsAux

/-- **Corollary 4.2** (`cor:finite-rank-b`). If `K` has finite rank `r`, then
`b_n(K) ≥ 1/2 - (r+1)/(2n)` for every positive integer `n`, and consequently `b(K) = 1/2`.
In particular, if `X` has finite Cantor–Bendixson rank, the generator of the structural theorem
(Theorem 2.2: every output available, all but finitely many outputs in the target) achieves lower
Banach density `1/2` on every target language. -/
theorem cor_finite_rank_b {X : Set (Set ℤ)} (hX : LangClass X) {K : Set ℤ} {r : ℕ}
    (hK : CBrank X K r) :
    (∀ n : ℕ, 1 ≤ n → (1 : ℝ) / 2 - (r + 1) / (2 * n) ≤ bn X K n) ∧ bK X K = 1 / 2 ∧
    (FiniteCBRank X → ∃ G : Generator, G.Admissible ∧ ∀ K' ∈ X, ∀ w, IsFullEnumeration w K' →
      G.AllAvailable w ∧ G.AlmostAllIn w K' ∧ 1 / 2 ≤ outputDensity (G.outputSet w) K') := by
  refine ⟨fun n hn => TheoremsAux.bn_ge_of_rank hX hK hn, TheoremsAux.bK_eq_half_of_rank hX hK,
    fun hfin => ?_⟩
  obtain ⟨G, hGa, hG⟩ := thm_lower hX
  refine ⟨G, hGa, fun K' hK' w hw => ?_⟩
  obtain ⟨r', hr'⟩ := TheoremsAux.rank_of_finiteCBRank hfin hK'
  have h := hG K' hK' w hw
  rw [TheoremsAux.bK_eq_half_of_rank hX hr'] at h
  exact h

/-- **Lemma 5.2** (`lem:upper-race`). Let `A` be a finite set none of whose points has been used.
In a race of `k` rounds the adversary inputs `a j ∈ A` and the algorithm outputs `o j`; every
point is available when it is played (`a j` is not an earlier input or output, `o j` is not an
input up to round `j` nor an earlier output), and the race ends when no point of `A` is
available (every point of `A` was input or output). Then the algorithm has generated at most
`⌊|A|/2⌋` points of `A`. The hypothesis `hend` mirrors the paper's "when the race ends"; the
Lean proof does not use it. This is a standalone restatement of the paper's lemma: the proof of
Theorem 5.1 (`thm_upper`) uses the race in the form `UpperAux.race`, not `lem_upper_race`. -/
theorem lem_upper_race (A : Finset ℤ) (k : ℕ) (a o : ℕ → ℤ) (ha : ∀ j < k, a j ∈ A)
    (ha_new : ∀ j < k, ∀ i < j, a j ≠ a i ∧ a j ≠ o i)
    (ho_new : ∀ j < k, (∀ i ≤ j, o j ≠ a i) ∧ ∀ i < j, o j ≠ o i)
    (hend : ∀ x ∈ A, ∃ j < k, a j = x ∨ o j = x) :
    ((Finset.range k).filter fun j => o j ∈ A).card ≤ A.card / 2 := by
  classical
  set S := (Finset.range k).filter fun j => o j ∈ A with hSdef
  have hI : ((Finset.range k).image a).card = k := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rcases lt_trichotomy i j with h | h | h
    · exact absurd hij.symm (ha_new j hj i h).1
    · exact h
    · exact absurd hij (ha_new i hi j h).1
  have hO : (S.image o).card = S.card := by
    apply Finset.card_image_of_injOn
    intro i hi j hj hij
    simp only [hSdef, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi hj
    rcases lt_trichotomy i j with h | h | h
    · exact absurd hij.symm ((ho_new j hj.1).2 i h)
    · exact h
    · exact absurd hij ((ho_new i hi.1).2 j h)
  have hdisj : Disjoint ((Finset.range k).image a) (S.image o) := by
    rw [Finset.disjoint_left]
    intro x hxa hxo
    simp only [Finset.mem_image, Finset.mem_range, hSdef, Finset.mem_filter] at hxa hxo
    obtain ⟨i, hi, rfl⟩ := hxa
    obtain ⟨j, ⟨hj, -⟩, hji⟩ := hxo
    rcases le_or_gt i j with h | h
    · exact (ho_new j hj).1 i h hji
    · exact (ha_new i hi j h).2 hji.symm
  have hsub : (Finset.range k).image a ∪ S.image o ⊆ A := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, hSdef,
      Finset.mem_filter] at hx
    rcases hx with ⟨i, hi, rfl⟩ | ⟨j, ⟨-, hj⟩, rfl⟩
    · exact ha i hi
    · exact hj
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hI, hO] at hcard
  have hSk : S.card ≤ k := (Finset.card_filter_le _ _).trans (by simp)
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  omega

/-- **Theorem 6.9** (`thm:topological-main`, topological characterization of the optimal
guarantee). For every nonempty countable class `X` of infinite subsets of `ℤ`:
1. *Achievability.* There is one generator such that, on every complete text of every `K ∈ X`,
   every output is available, all but finitely many outputs belong to `K`, and
   `δ_B(O, K) ≥ lim_n sup_{𝒰 ∋ (K) open} inf_{H ∈ 𝒰} c_n(H)`.
2. *Optimality.* Let `𝒜` be any generator eventually valid on every complete text of every
   language in `X`. Then for every `K ∈ X` there is an adversarial enumeration of `K` on which
   `δ_B(O, K) ≤ lim_n sup_{𝒰 ∋ (K) open} inf_{H ∈ 𝒰} c_n(H)`. -/
theorem thm_topological_main {X : Set (Set ℤ)} (hX : LangClass X) :
    (∃ G : Generator, G.Admissible ∧ ∀ K ∈ X, ∀ w, IsFullEnumeration w K →
      G.AllAvailable w ∧ G.AlmostAllIn w K ∧ bTop X K ≤ outputDensity (G.outputSet w) K) ∧
    (∀ G : Generator, G.Admissible → G.EventuallyValidOn X →
      ∀ K ∈ X, ∃ w, IsFullEnumeration w K ∧ outputDensity (G.outputSet w) K ≤ bTop X K) := by
  refine ⟨?_, fun G hGa hG K hK => ?_⟩
  · obtain ⟨G, hGa, hG⟩ := thm_lower hX
    exact ⟨G, hGa, fun K hK w hw => by
      rw [TheoremsAux.bTop_eq_bK hX hK]; exact hG K hK w hw⟩
  · rw [TheoremsAux.bTop_eq_bK hX hK]
    exact thm_upper hX G hGa hG hK

/-- **Theorem 1.11** (`thm:intro-one-dimensional`, one-dimensional characterization). Let `X`
be a nonempty countable family of infinite subsets of `ℤ`. For every `K ∈ X` and `n ≥ 1`,
`b_n^comb(K) = b_n^top(K)`; write `b_n(K)` for the common value and `b(K) = lim_n b_n(K)`.
1. (Upper bound) For every generator eventually valid on `X` and every `K ∈ X` there is an
   adversarial enumeration of `K` with `δ_B(O, K) ≤ b(K)`.
2. (Lower bound) There is a single eventually valid generator such that for every `K ∈ X` and
   every adversarial enumeration of `K`, its output set satisfies `δ_B(O, K) ≥ b(K)`.

The premise `1 ≤ n` of the first conjunct mirrors the paper's statement ("every `n ≥ 1`"); the
Lean proof does not need it (it is only passed on to `thm_topological_bn`, which does not use
it). -/
theorem thm_intro_one_dimensional {X : Set (Set ℤ)} (hX : LangClass X) :
    (∀ K ∈ X, ∀ n : ℕ, 1 ≤ n → bn X K n = bnTop X K n) ∧
    (∀ G : Generator, G.Admissible → G.EventuallyValidOn X →
      ∀ K ∈ X, ∃ w, IsFullEnumeration w K ∧ outputDensity (G.outputSet w) K ≤ bK X K) ∧
    (∃ G : Generator, G.Admissible ∧ G.EventuallyValidOn X ∧
      ∀ K ∈ X, ∀ w, IsFullEnumeration w K → bK X K ≤ outputDensity (G.outputSet w) K) := by
  exact ⟨fun K hK n hn => thm_topological_bn hX hK hn,
    fun G hGa hG K hK => thm_upper hX G hGa hG hK, thm_oneD_lower_conclusion hX⟩

/-- **Corollary 1.12** (`cor:intro-one-dimensional-rank`). If every language in `X` has finite
Cantor–Bendixson point rank, then a single eventually valid generator achieves the optimal lower
Banach density `1/2` for every target: it achieves `δ_B(O, K) ≥ 1/2` on every full enumeration
of every `K ∈ X`, and no eventually valid generator does better (for every such generator and
every `K` some enumeration gives `δ_B(O, K) ≤ 1/2`). -/
theorem cor_intro_one_dimensional_rank {X : Set (Set ℤ)} (hX : LangClass X)
    (hrank : ∀ L ∈ X, ∃ r, CBrank X L r) :
    (∃ G : Generator, G.Admissible ∧ G.EventuallyValidOn X ∧
      ∀ K ∈ X, ∀ w, IsFullEnumeration w K → 1 / 2 ≤ outputDensity (G.outputSet w) K) ∧
    (∀ G : Generator, G.Admissible → G.EventuallyValidOn X →
      ∀ K ∈ X, ∃ w, IsFullEnumeration w K ∧ outputDensity (G.outputSet w) K ≤ 1 / 2) := by
  have hb : ∀ K ∈ X, bK X K = 1 / 2 := fun K hK => by
    obtain ⟨r, hr⟩ := hrank K hK
    exact (cor_finite_rank_b hX hr).2.1
  refine ⟨?_, fun G hGa hG K hK => ?_⟩
  · obtain ⟨G, hGa, hGv, hGd⟩ := thm_oneD_lower_conclusion hX
    exact ⟨G, hGa, hGv, fun K hK w hw => by rw [← hb K hK]; exact hGd K hK w hw⟩
  · rw [← hb K hK]
    exact thm_upper hX G hGa hG hK

end BanachDensity1D
