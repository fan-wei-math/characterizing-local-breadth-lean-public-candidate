import BanachDensityHD.CharacterizationSuff2

/-!
# Section 8: the characterization of the generation frontier

Kleinberg–Wei, *Characterizing Local Breadth in Language Generation*.
Historical source numbering is retained; current mappings are in the release registry.

-/

namespace BanachDensityHD

open Set Filter
open scoped Classical

/-! ## Proof development (helpers for §8) -/


/-- **Lemma 8.11** (`lem:sewing`): one partition `Pb` of `ℤ^d` into rectangular boards, chosen
before `g` and independent of every language, with the two sewing bounds (finitely many boards
meet a rectangle). -/
theorem lem_sewing (d : ℕ) (hd : 2 ≤ d) :
    ∃ Pb : Set (Rect d),
      (∀ C ∈ Pb, ∀ C' ∈ Pb, C ≠ C' → Disjoint C.pts C'.pts) ∧ (∀ x : Pt d, ∃ C ∈ Pb, x ∈ C.pts) ∧
      ∀ R : Rect d, {C ∈ Pb | (C.pts ∩ R.pts).Nonempty}.Finite ∧
        (∑ᶠ C ∈ {C ∈ Pb | (C.pts ∩ R.pts).Nonempty}, Real.log (2 + (C.pts ∩ R.pts).ncard)) ≤
          (12 * d ^ 2 + 4 * d) * Real.log (2 + R.vol) ∧
        ∀ g : ℝ → ℝ, (∀ x, 1 ≤ x → 1 ≤ g x) → MonotoneOn g (Ici 1) →
          (∑ᶠ C ∈ {C ∈ Pb | (C.pts ∩ R.pts).Nonempty}, hLog g (C.pts ∩ R.pts).ncard) ≤
            (12 * d ^ 2 + 4 * d) * hLog g R.vol := by
  open SewingAux in
  refine ⟨Pb d, ?_, ?_, fun R => ⟨?_, ?_, fun g hg1 hgm => ?_⟩⟩
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hne
    rw [Set.disjoint_left]
    intro x hxa hxb
    exact hne (congrArg board (idx_unique hxa hxb))
  · intro x
    obtain ⟨a, ha⟩ := exists_board x
    exact ⟨board a, ⟨a, rfl⟩, ha⟩
  · rw [metBoards_eq]; exact (met_finite R).image _
  · rw [finsum_eq R (fun C => Real.log (2 + (C.pts ∩ R.pts).ncard))]
    exact log_sum_le hd R
  · rw [finsum_eq R (fun C => hLog g (C.pts ∩ R.pts).ncard)]
    exact h_sum_le hd R g hg1 hgm

/-- **Theorem 8.1(1)** (`thm:fixed-quota`, sufficiency). -/
theorem thm_fixed_quota_suff {d : ℕ} (hd : 2 ≤ d) {X : Set (Set (Pt d))} (hX : LangClass X)
    {g : ℝ → ℝ} (hg1 : ∀ x, 1 ≤ x → 1 ≤ g x) (hgm : MonotoneOn g (Ici 1))
    (q : Set (Pt d) → ℝ) (hq : ∀ K ∈ X, q K ∈ Icc (0 : ℝ) 1)
    (htree : ∀ K ∈ X, ∃ T, IsProtectedTree X (hLog g) q K T) :
    ∃ G ∈ ValidGen X, ∀ K ∈ X, Guarantees (dH (hLog g)) G K (q K) := by
  exact SuffAux.fixed_quota_suff_of_sewing hd hX hg1 hgm q hq htree (lem_sewing d hd)

/-- **Theorem 8.1(2)** (`thm:fixed-quota`, necessity). -/
theorem thm_fixed_quota_nec {d : ℕ} (hd : 2 ≤ d) {X : Set (Set (Pt d))} (hX : LangClass X)
    {g : ℝ → ℝ} (hg1 : ∀ x, 1 ≤ x → 1 ≤ g x) (hgm : MonotoneOn g (Ici 1))
    (α : Set (Pt d) → ℝ) (hα : ∀ K ∈ X, α K ∈ Icc (0 : ℝ) 1)
    (hach : Achievable (hLog g) X α) :
    ∀ ε : ℝ, 0 < ε → ∀ K ∈ X, ∃ T, IsProtectedTree X (hLog g) (fun L => max (α L - ε) 0) K T := by
  intro ε _ K hK
  obtain ⟨G, hG, hGK⟩ := hach
  have hq : ∀ L, (fun L => max (α L - ε) 0) L = 0 ∨ (fun L => max (α L - ε) 0) L < α L := by
    intro L
    by_cases h : α L - ε ≤ 0
    · left; exact max_eq_right h
    · right
      push Not at h
      simp only [max_eq_left h.le]
      linarith
  obtain ⟨U, s, a, hU⟩ := CharAux.nec_deco hX hg1 _ α hq G hG hGK hK
  exact CharAux.tree_of_deco hX.countable hK hU

/-- **Theorem 8.2** (`thm:main`, exact simultaneous profile characterization) stated for the
**monotone** copy relation (an alternative to the broad relation),
via `IsCopyProtectedTree`. The theorem as written in the manuscript, with the broad relation of
Definition 8.14, is `thm_main_broad`; the two are linked by `copyTree_broad_iff_monotone`, whose
equivalence is proved in Trees.lean. -/
theorem thm_main {d : ℕ} (hd : 2 ≤ d) {X : Set (Set (Pt d))} (hX : LangClass X)
    {g : ℝ → ℝ} (hg1 : ∀ x, 1 ≤ x → 1 ≤ g x) (hgm : MonotoneOn g (Ici 1))
    (α : Set (Pt d) → ℝ) (hα : ∀ K ∈ X, α K ∈ Icc (0 : ℝ) 1) :
    Achievable (hLog g) X α ↔
      ∀ K ∈ X, ∀ k : ℕ, 1 ≤ k → ∃ T, IsCopyProtectedTree X (hLog g) α K k T := by
  constructor
  · rintro ⟨G, hG, hGK⟩ K hK k hk
    exact CharAux.copy_tree_of_gen hX hg1 α G hG hGK hK k hk
  · exact fun htree => SuffAux.main_suff_of_sewing hd hX hg1 hgm α hα htree (lem_sewing d hd)

/-- **Theorem 8.2** (`thm:main`) with Definition 8.14 as written in the manuscript (the broad copy
relation, `IsBroadCopyProtectedTree`). Same hypotheses as `thm_main`, which states the theorem for
the monotone relation ; the two are linked by
`copyTree_broad_iff_monotone`. -/
theorem thm_main_broad {d : ℕ} (hd : 2 ≤ d) {X : Set (Set (Pt d))} (hX : LangClass X)
    {g : ℝ → ℝ} (hg1 : ∀ x, 1 ≤ x → 1 ≤ g x) (hgm : MonotoneOn g (Ici 1))
    (α : Set (Pt d) → ℝ) (hα : ∀ K ∈ X, α K ∈ Icc (0 : ℝ) 1) :
    Achievable (hLog g) X α ↔
      ∀ K ∈ X, ∀ k : ℕ, 1 ≤ k → ∃ T, IsBroadCopyProtectedTree X (hLog g) α K k T := by
  -- derived from `thm_main` through the bridge `copyTree_broad_iff_monotone` (Trees.lean)
  simp_rw [copyTree_broad_iff_monotone]
  exact thm_main hd hX hg1 hgm α hα



/-- **Theorem 8.7** (`thm:topological-protected-tree`). -/
theorem thm_topological_protected_tree {d : ℕ} (hd : 2 ≤ d) {X : Set (Set (Pt d))}
    (hX : LangClass X) {g : ℝ → ℝ} (hg1 : ∀ x, 1 ≤ x → 1 ≤ g x) (hgm : MonotoneOn g (Ici 1)) (q : Set (Pt d) → ℝ) {K : Set (Pt d)} (hK : K ∈ X) :
    (∃ T, IsProtectedTree X (hLog g) q K T) ↔
      ∃ (U : Set (History X)) (s a : List (Set (Pt d)) → ℝ), IsQGoodDecoration X (hLog g) q K hK U s a :=
  ⟨fun ⟨_, hT⟩ => CharAux.deco_of_tree hK hT,
    fun ⟨_, _, _, hU⟩ => CharAux.tree_of_deco hX.countable hK hU⟩

/-- **Corollary 8.8** (`cor:hd-obstruction`): a protected tree exists iff some global geometric
assignment `Θ = (s, a)` (cutoffs `≥ 1`, radii `≥ 0` strictly increasing along one-step extensions)
makes every admissible obstruction tree rooted at `K` have a `Θ`-good terminal history. -/
theorem cor_hd_obstruction {d : ℕ} (hd : 2 ≤ d) {X : Set (Set (Pt d))}
    (hX : LangClass X) {g : ℝ → ℝ} (hg1 : ∀ x, 1 ≤ x → 1 ≤ g x) (hgm : MonotoneOn g (Ici 1)) (q : Set (Pt d) → ℝ) {K : Set (Pt d)} (hK : K ∈ X) :
    (∃ T, IsProtectedTree X (hLog g) q K T) ↔
      ∃ s a : List (Set (Pt d)) → ℝ,
        (∀ H, IsChain X H → H.headD ∅ = K → 1 ≤ s H ∧ 0 ≤ a H) ∧
        (∀ H M, IsChain X (H ++ [M]) → H ≠ [] → H.headD ∅ = K → a H < a (H ++ [M])) ∧
        ∀ T : LTree (Pt d), def_aot X K T →
          ∃ P ∈ T.paths, ∃ hP : P ≠ [], DecoratedGood (hLog g) q s a P hP :=
  ⟨fun ⟨_, hT⟩ => CharAux.assignment_of_tree hK hT,
    fun ⟨s, a, h1, h2, h3⟩ => CharAux.tree_of_assignment hX.countable hK s a h1 h2 h3⟩


/-- **Corollary 8.9** (`cor:topological-protected-set`): in an open neighbourhood with a `q`-good
decoration, every history `H` has a finite `P_H ⊆ end(H)` such that every proper refinement
`M ∈ X` with `P_H ⊆ M ⊊ end(H)` gives `H⌢M ∈ 𝓤`. -/
theorem cor_topological_protected_set {d : ℕ} (hd : 2 ≤ d) {X : Set (Set (Pt d))}
    (hX : LangClass X) {g : ℝ → ℝ} (hg1 : ∀ x, 1 ≤ x → 1 ≤ g x) (hgm : MonotoneOn g (Ici 1)) (q : Set (Pt d) → ℝ) {K : Set (Pt d)} (hK : K ∈ X)
    {U : Set (History X)} {s a : List (Set (Pt d)) → ℝ}
    (hU : IsQGoodDecoration X (hLog g) q K hK U s a) :
    ∀ H ∈ U, ∃ P : Set (Pt d), P.Finite ∧ P ⊆ H.last ∧
      ∀ M ∈ X, P ⊆ M → M ⊂ H.last → ∀ Γ : History X, History.IsSnoc H Γ M → Γ ∈ U := by
  intro H hH
  obtain ⟨F, hF, hFL, hext⟩ := (HistoriesAux.isOpen_iff U).1 hU.2.1 H hH
  exact ⟨F, hF, hFL, fun M _ hPM _ Γ hΓ => hext Γ M hΓ hPM⟩


/-- **Lemma 8.13** (`lem:hd-commitments`): finite validity and density commitments. For a generator
of the model guaranteeing `α_L` at `L`, and a quota `q` with `q = 0` or `0 ≤ q < α_L`: from any
finite prefix in `L`, a finite extension in `L` and a cutoff `s ≥ 1` commit the generator, for
every further continuation in `L` (repetitions allowed), to valid outputs and to the quota `q` on
every occupied trace `L ∩ R` with `ρ_L(R) ≥ s`. -/
theorem lem_hd_commitments {d : ℕ} (hd : 2 ≤ d) {X : Set (Set (Pt d))} (hX : LangClass X)
    {g : ℝ → ℝ} (hg1 : ∀ x, 1 ≤ x → 1 ≤ g x) (hgm : MonotoneOn g (Ici 1)) (G : Generator (Pt d)) (hG : G ∈ ValidGen X) {L : Set (Pt d)} (hL : L ∈ X)
    {αL q : ℝ} (hach : Guarantees (dH (hLog g)) G L αL) (hq : q = 0 ∨ (0 ≤ q ∧ q < αL))
    (xs : List (Pt d)) (hxL : ∀ x ∈ xs, x ∈ L) :
    ∃ ext : List (Pt d), ∃ s : ℝ, 1 ≤ s ∧ (∀ x ∈ ext, x ∈ L) ∧
      ∀ cont : List (Pt d), (∀ x ∈ cont, x ∈ L) →
        (∀ j < cont.length, G ((xs ++ ext ++ cont).take ((xs ++ ext).length + j + 1)) ∈ L) ∧
        ∀ R : Rect d, s * (hLog g) R.vol ≤ mass L R →
          (L ∩ R.pts ⊆ {x | x ∈ xs ++ ext ++ cont} ∪ outsOf G (xs ++ ext ++ cont)) →
          q * (mass L R : ℝ) ≤ ((outsOf G (xs ++ ext ++ cont) ∩ L ∩ R.pts).ncard : ℝ) :=
  CharAux.hd_commitments hX hg1 G hG hL hach (hq.imp_right And.right) xs hxL



end BanachDensityHD
