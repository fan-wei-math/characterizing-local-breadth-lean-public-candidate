import BanachDensityHD

/-!
# Oct 31 manuscript bridges

New alignment declarations only. The historical import graph and all historical
statements and proofs remain unchanged. The scalar cofinality results below do not
purport to formalize an entire relabelling of protected trees or copy forests.
-/

namespace BanachDensityHD.Oct31

open Set Filter

/-- Oct31 Definition 1.3: retain only valid target points in the numerator. -/
noncomputable def relativeBanach {d : ℕ} (A B : Set (Pt d)) : EReal :=
  banach (A ∩ B) B

/-- Oct31 Definition 1.4: intersecting the output with its target changes no level test. -/
theorem deltaH_inter_target {d : ℕ} (h : ℕ → ℝ) (A B : Set (Pt d)) :
    deltaH h (A ∩ B) B = deltaH h A B := by
  classical
  have he : testInf h (A ∩ B) B = testInf h A B := by
    funext s
    have hi : (A ∩ B) ∩ B = A ∩ B := by
      ext x
      simp only [Set.mem_inter_iff]
      tauto
    have hs : {r : ℝ | ∃ R : Rect d, s * h R.vol ≤ mass B R ∧
        r = (((A ∩ B) ∩ B ∩ R.pts).ncard : ℝ) / mass B R} =
        {r : ℝ | ∃ R : Rect d, s * h R.vol ≤ mass B R ∧
        r = ((A ∩ B ∩ R.pts).ncard : ℝ) / mass B R} := by
      rw [hi]
    exact congrArg (fun S : Set ℝ => if S.Nonempty then sInf S else 1) hs
  exact congrArg (fun f : ℝ → ℝ => limUnder atTop f) he

/-- Oct31 Definitions 1.3–1.4: ordinary relative density is the constant-threshold
filtered density for every output set, provided the target is infinite. No
finite-invalid-output assumption on A is needed for the valid-target numerator. -/
theorem relativeBanach_eq_dH_one {d : ℕ} (A B : Set (Pt d)) (hB : B.Infinite) :
    relativeBanach A B = dH (fun _ => 1) A B := by
  have hf : ((A ∩ B) \ B).Finite := Set.finite_empty.subset (by
    intro x hx
    exact hx.2 hx.1.2)
  simpa [relativeBanach, dH, deltaH_inter_target] using
    banach_eq_deltaH_one (A ∩ B) B hB hf

/-- Oct31 text after Definition 1.4: every h-vacuous target has density one,
for every output set. Positivity is needed only on positive rectangle volumes. -/
theorem deltaH_of_vacuous {d : ℕ} (h : ℕ → ℝ)
    (hpos : ∀ n, 1 ≤ n → 0 < h n) (O K : Set (Pt d))
    (hv : ¬ Nonvacuous h K) : deltaH h O K = 1 := by
  classical
  have hb : BddAbove (range fun R : Rect d => (mass K R : ℝ) / h R.vol) := by
    simpa only [Nonvacuous, not_not] using hv
  obtain ⟨c, hc⟩ := hb
  have he : ∀ᶠ s : ℝ in atTop, testInf h O K s = 1 := by
    filter_upwards [eventually_ge_atTop (c + 1)] with s hs
    unfold testInf
    rw [ite_eq_right]
    rintro ⟨r, R, hr, _⟩
    have hp := hpos R.vol (BasicAux.rect_vol_pos R)
    have hbound := hc (mem_range_self R)
    have hm : (mass K R : ℝ) ≤ c * h R.vol := (div_le_iff₀ hp).mp hbound
    nlinarith
  have ht : Tendsto (testInf h O K) atTop (nhds (1 : ℝ)) :=
    tendsto_const_nhds.congr' (he.mono fun _ hs => hs.symm)
  exact tendsto_nhds_unique (deltaH_tendsto h hpos O K).1 ht

/-- Oct31 Theorem 8.2 including vacuous targets: one generator handles every
finite-point-rank target, without a common rank bound or a nonvacuity guard. -/
theorem finite_rank_near_half_all {d : ℕ} (hd : 2 ≤ d)
    {X : Set (Set (Pt d))} (hX : LangClass X) {τ ε : ℝ}
    (hτ : 0 < τ) (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    ∃ G ∈ ValidGen X, ∀ K ∈ X, (∃ r, PointRank X K r) →
      Guarantees (dH (hTau τ)) G K (1 / 2 - ε) := by
  obtain ⟨G, hG, hGK⟩ := thm_finite_rank_near_half hd hX hτ hε0 hε
  refine ⟨G, hG, fun K hK hr => ?_⟩
  by_cases hv : Nonvacuous (hTau τ) K
  · exact hGK K hK hv hr
  · intro w _
    have hp : ∀ n, 1 ≤ n → 0 < hTau τ n := by
      intro n hn
      apply Real.rpow_pos_of_pos
      apply Real.log_pos
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    rw [dH, deltaH_of_vacuous (hTau τ) hp (G.outputSet w) K hv]
    exact EReal.coe_le_coe_iff.mpr (by linarith)

/-- Oct31 Theorem 6.1: expose the fixed gap 1/16, uniformly in the threshold,
from the already verified exact-optima/trade-off theorem. -/
theorem separation_gap_one_sixteenth (d : ℕ) (hd : 2 ≤ d) :
    ∃ X : Set (Set (Pt d)), LangClass X ∧
      (∀ L ∈ X, ∀ x ∈ L, ∀ i, 0 ≤ x i) ∧
      ∀ h : ℕ → ℝ, IsThreshold h → ∀ G ∈ ValidGen X,
        ∃ L ∈ X, bG (dH h) G L ≤ bOpt (dH h) X L - ((1 / 16 : ℝ) : EReal) := by
  obtain ⟨X, K, G₀, G₁, hX, hnonneg, hK, _, _, hs⟩ := thm_main_not_simul d hd
  refine ⟨X, hX, hnonneg, fun h hh G hG => ?_⟩
  obtain ⟨_, _, htrade, hopt0, hopt1⟩ := hs h hh
  by_contra hcon
  push Not at hcon
  have e1 : (1 / 4 : EReal) - ((1 / 16 : ℝ) : EReal) = ((3 / 16 : ℝ) : EReal) := by
    rw [← SeparationAux.ereal_quarter, ← EReal.coe_sub]; congr 1; norm_num
  have e2 : (1 / 2 : EReal) - ((1 / 16 : ℝ) : EReal) = ((7 / 16 : ℝ) : EReal) := by
    rw [← SeparationAux.ereal_half, ← EReal.coe_sub]; congr 1; norm_num
  have g0 : Guarantees (dH h) G K (3 / 16) := by
    intro w hw
    have h := hcon K hK
    rw [hopt0, e1] at h
    exact h.le.trans (SeparationAux.bG_le hw)
  have g1 : ∀ L ∈ X, L ≠ K → Guarantees (dH h) G L (7 / 16) := by
    intro L hL hne w hw
    have h := hcon L hL
    rw [hopt1 L hL hne, e2] at h
    exact h.le.trans (SeparationAux.bG_le hw)
  have hbad := htrade G hG _ _ g0 g1
  norm_num at hbad

/-- Oct31 §7.5: all positive dyadic-accuracy scalar quotas recover exactly the
limiting profile bound. This is the limiting step, not a copy-tree equivalence. -/
theorem le_iff_all_dyadic_quotas (a x : ℝ) (hx : 0 ≤ x) :
    a ≤ x ↔ ∀ k : ℕ, 1 ≤ k → max (a - (1 / 2 : ℝ) ^ k) 0 ≤ x := by
  constructor
  · intro h k _
    apply max_le _ hx
    have hp : 0 ≤ (1 / 2 : ℝ) ^ k := by positivity
    linarith
  · intro h
    have ht : Tendsto (fun k : ℕ => a - (1 / 2 : ℝ) ^ k) atTop (nhds a) := by
      simpa using tendsto_const_nhds.sub
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1))
    apply le_of_tendsto ht
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
    exact (le_max_left _ _).trans (h k hk)

/-- Oct31 §7.5 versus the verified reciprocal schedule: scalar approximation by
all reciprocal quotas is equivalent to approximation by all dyadic quotas. -/
theorem reciprocal_iff_dyadic_quotas (a x : ℝ) (hx : 0 ≤ x) :
    (∀ k : ℕ, 1 ≤ k → max (a - 1 / (k : ℝ)) 0 ≤ x) ↔
      ∀ k : ℕ, 1 ≤ k → max (a - (1 / 2 : ℝ) ^ k) 0 ≤ x := by
  rw [← le_iff_all_dyadic_quotas a x hx]
  constructor
  · intro h
    by_contra hn
    push Not at hn
    obtain ⟨n, he⟩ := exists_nat_one_div_lt (sub_pos.mpr hn)
    have hq := (le_max_left _ _).trans (h (n + 1) (by omega))
    push_cast at hq
    linarith
  · intro h k _
    apply max_le _ hx
    have hp : 0 ≤ 1 / (k : ℝ) := by positivity
    linarith

end BanachDensityHD.Oct31
