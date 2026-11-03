import BanachDensityHD.AppendixA

/-! The abstract potential theorem localized to prescribed legal play.
Quantitative hypotheses are required only at actual states before and during rounds.
Locality is used there and at one legal hypothetical Black probe from them.
No equivalence with arbitrary bookkeeping Reachable states is assumed.
-/
namespace BanachDensityHD.ExactStatements.OnPlay
open Set Filter RegionTree AppendixAAux
open scoped Classical
noncomputable section
variable {d : ℕ} (T : RegionTree d) (Pot : T.V → T.State → ℝ)

inductive PlayState : T.State → Prop
  | before (bs : List (Pt d)) (h : T.LegalBlack Pot bs) (k : ℕ) (hk : k ≤ bs.length) :
      PlayState (T.run Pot (bs.take k))
  | black (bs : List (Pt d)) (h : T.LegalBlack Pot bs) (k : ℕ) (hk : k < bs.length) :
      PlayState (T.blackClaim (T.run Pot (bs.take k)) bs[k])
  | activated (bs : List (Pt d)) (h : T.LegalBlack Pot bs) (k : ℕ) (hk : k < bs.length) :
      PlayState (T.activationStep Pot (T.blackClaim (T.run Pot (bs.take k)) bs[k]))

inductive ProbeState : T.State → Prop
  | actual {st : T.State} : PlayState T Pot st → ProbeState st
  | black {st : T.State} (h : PlayState T Pot st) {x : Pt d}
      (hx : x ∈ T.E T.root) (hu : T.Unused st x) : ProbeState (T.blackClaim st x)

structure Properties (σ : ℝ) : Prop where
  sigma : 0 < σ ∧ σ ≤ 1 / 16
  nonneg : ∀ st, PlayState T Pot st → ∀ v, 0 ≤ Pot v st
  loc_black : ∀ st, ProbeState T Pot st → ∀ v x, x ∉ T.eff st v → Pot v (T.blackClaim st x) = Pot v st
  loc_white : ∀ st, ProbeState T Pot st → ∀ v y, y ∉ T.eff st v → Pot v (T.whiteClaim st y) = Pot v st
  loc_act : ∀ st, ProbeState T Pot st → ∀ u v, ¬ T.StrictAnc v u → Pot v (T.activate st u) = Pot v st
  p1_init : ∀ v, Pot v T.init ≤ 1 / 16
  p1_detect : ∀ st, PlayState T Pot st → ∀ v, (∀ x ∈ T.E T.root, x ∈ st.black ∨ x ∈ st.white) →
    (∃ Q ∈ T.reqs v, 0 < T.outstanding st v Q) → 1 ≤ Pot v st
  p2 : ∀ st, PlayState T Pot st → ∀ v, (∀ u, T.Anc v u → Pot u st ≤ 1 / 4) →
    ∀ x ∈ T.eff st v, T.Unused st x →
      0 ≤ T.score Pot st v x ∧ T.score Pot st v x ≤ σ * Pot v st
  p2_white : ∀ st, PlayState T Pot st → ∀ u y, y ∈ T.E T.root → T.Unused st y → Pot u (T.whiteClaim st y) ≤ Pot u st
  p3 : ∀ st, PlayState T Pot st → ∀ v, (∀ u, T.Anc v u → Pot u st ≤ 1 / 4) →
    ∀ y ∈ T.eff st v, T.Unused st y →
      (1 + 8 * σ) * T.score Pot st v y ≤ Pot v st - Pot v (T.whiteClaim st y) ∧
      ∀ x ∈ T.eff st v, T.Unused st x → x ≠ y →
        T.score Pot (T.whiteClaim st y) v x ≤ (1 + 2 * σ) * T.score Pot st v x
  p4 : ∀ st, PlayState T Pot st → ∀ u x, u ∉ st.active → 1 / 12 ≤ Pot u st → x ∈ T.eff st u →
    T.Unused st x → ∀ v, T.StrictAnc v u →
      Pot v (T.activate (T.blackClaim st x) u) ≤ Pot v st ∧
      T.reserve Pot (T.activate (T.blackClaim st x) u) v ≤ T.reserve Pot st v


variable {T Pot}
variable {σ : ℝ}
theorem score_bounds (hP : Properties T Pot σ) {st : T.State} (hR : T.Reachable st) (hS : PlayState T Pot st)
    (hB : ∀ v, Pot v st ≤ 1 / 4) {v : T.V} {x : Pt d} (hx : x ∈ T.eff st v) (hu : T.Unused st x) :
    0 ≤ T.score Pot st v x ∧ T.score Pot st v x ≤ σ * Pot v st :=
  hP.p2 st hS v (fun u _ => hB u) x hx hu

theorem maxScore_bounds (hP : Properties T Pot σ) {st : T.State} (hR : T.Reachable st) (hS : PlayState T Pot st)
    (hB : ∀ v, Pot v st ≤ 1 / 4) (v : T.V) :
    0 ≤ T.maxScore Pot st v ∧ T.maxScore Pot st v ≤ σ * Pot v st :=
  ⟨maxScore_nonneg Pot fun x hx hu => (score_bounds hP hR hS hB hx hu).1,
    maxScore_le Pot (mul_nonneg hP.sigma.1.le (hP.nonneg st hS v))
      fun x hx hu => (score_bounds hP hR hS hB hx hu).2⟩

/-- A Black claim outside `E_w^*` does not increase the reserve at `w`. -/
theorem reserve_black_le (hT : T.WellFormed) (hP : Properties T Pot σ) {s : T.State}
    (hR : T.Reachable s) (hS : PlayState T Pot s) (hB : ∀ v, Pot v s ≤ 1 / 4) {w : T.V} {x : Pt d} (hx : x ∉ T.eff s w) :
    T.reserve Pot (T.blackClaim s x) w ≤ T.reserve Pot s w := by
  unfold RegionTree.reserve
  rw [hP.loc_black s (ProbeState.actual hS) w x hx]
  refine add_le_add le_rfl (maxScore_mono Pot (maxScore_bounds hP hR hS hB w).1 fun z hz hu => ?_)
  have hz' : z ∈ T.eff s w := hz
  have hus : T.Unused s z := ⟨fun h => hu.1 (Finset.mem_insert_of_mem h), hu.2⟩
  refine ⟨hz', hus, le_of_eq ?_⟩
  rw [score_of_mem Pot hz, score_of_mem Pot hz', blackClaim_comm,
    hP.loc_black _ (ProbeState.black hS (eff_sub_root hT s w hz') hus) w x hx,
    hP.loc_black s (ProbeState.actual hS) w x hx]

/-- A White claim outside `E_w^*` does not increase the reserve at `w`. -/
theorem reserve_white_le (hT : T.WellFormed) (hP : Properties T Pot σ) {s : T.State}
    (hR : T.Reachable s) (hS : PlayState T Pot s) (hB : ∀ v, Pot v s ≤ 1 / 4) {w : T.V} {y : Pt d} (hy : y ∉ T.eff s w) :
    T.reserve Pot (T.whiteClaim s y) w ≤ T.reserve Pot s w := by
  unfold RegionTree.reserve
  rw [hP.loc_white s (ProbeState.actual hS) w y hy]
  refine add_le_add le_rfl (maxScore_mono Pot (maxScore_bounds hP hR hS hB w).1 fun z hz hu => ?_)
  have hz' : z ∈ T.eff s w := hz
  have hus : T.Unused s z := ⟨hu.1, fun h => hu.2 (Finset.mem_insert_of_mem h)⟩
  refine ⟨hz', hus, le_of_eq ?_⟩
  rw [score_of_mem Pot hz, score_of_mem Pot hz', blackClaim_whiteClaim,
    hP.loc_white _ (ProbeState.black hS (eff_sub_root hT s w hz') hus) w y hy,
    hP.loc_white s (ProbeState.actual hS) w y hy]

/-- Activating `u` does not increase the reserve at a vertex that is not a strict ancestor of `u`. -/
theorem reserve_act_le (hT : T.WellFormed) (hP : Properties T Pot σ) {s : T.State}
    (hR : T.Reachable s) (hS : PlayState T Pot s) (hB : ∀ v, Pot v s ≤ 1 / 4) {w u : T.V} (hwu : ¬ T.StrictAnc w u) :
    T.reserve Pot (T.activate s u) w ≤ T.reserve Pot s w := by
  unfold RegionTree.reserve
  rw [hP.loc_act s (ProbeState.actual hS) u w hwu]
  refine add_le_add le_rfl (maxScore_mono Pot (maxScore_bounds hP hR hS hB w).1 fun z hz hu => ?_)
  have hz' : z ∈ T.eff s w := by rwa [eff_activate_of_not hwu] at hz
  have hus : T.Unused s z := hu
  refine ⟨hz', hus, le_of_eq ?_⟩
  rw [score_of_mem Pot hz, score_of_mem Pot hz', blackClaim_activate,
    hP.loc_act _ (ProbeState.black hS (eff_sub_root hT s w hz') hus) u w hwu,
    hP.loc_act s (ProbeState.actual hS) u w hwu]

/-- White's step of a round: from the state after Black's claim and the activation step, White's
reply at the responsible vertex `r` restores the round invariant. -/
theorem white_step (hT : T.WellFormed) (hP : Properties T Pot σ) {s : T.State} {r : T.V}
    (hR : T.Reachable s) (hS : PlayState T Pot s) (hB : ∀ v, Pot v s ≤ 1 / 4) (hin : ∀ v, v ∉ s.active → Pot v s < 1 / 8)
    (hr : r ∈ s.active) (hres : ∀ w ∈ s.active, w ≠ r → T.reserve Pot s w ≤ 1 / 4)
    (hcr : ∀ v Q, s.credit v Q ≤ (s.white ∩ Q).card) :
    RoundInv (Pot := Pot) ((T.reply Pot s r).elim s (T.whiteClaim s ·)) := by
  rcases hrep : T.reply Pot s r with _ | y
  · -- White passes
    show RoundInv (Pot := Pot) s
    refine ⟨hR, hB, fun v hv => ?_, hin, hcr⟩
    by_cases hvr : v = r
    · subst hvr
      unfold RegionTree.reserve
      rw [maxScore_eq_zero Pot (reply_none Pot hrep), add_zero]
      exact hB v
    · exact hres v hv hvr
  · obtain ⟨hy, hyu, hymax⟩ := reply_some Pot hrep
    have hyE : y ∈ T.E T.root := eff_sub_root hT s r hy
    have hRW : T.Reachable (T.whiteClaim s y) := RegionTree.Reachable.white hR hyE hyu
    have hPW : ∀ v, Pot v (T.whiteClaim s y) ≤ Pot v s := fun v => hP.p2_white s hS v y hyE hyu
    show RoundInv (Pot := Pot) (T.whiteClaim s y)
    refine ⟨hRW, fun v => (hPW v).trans (hB v), fun v hv => ?_,
      fun v hv => (hPW v).trans_lt (hin v hv), fun v Q => ?_⟩
    · have hv' : v ∈ s.active := hv
      by_cases hvr : v = r
      · subst hvr
        obtain ⟨h3a, h3b⟩ := hP.p3 s hS v (fun u _ => hB u) y hy hyu
        have hsy := (score_bounds hP hR hS hB hy hyu).1
        have hσ := hP.sigma.1
        have hM : T.maxScore Pot (T.whiteClaim s y) v ≤ (1 + 2 * σ) * T.score Pot s v y := by
          refine maxScore_le Pot (by positivity) fun x hx hxu => ?_
          have hx' : x ∈ T.eff s v := hx
          have hxu' : T.Unused s x := ⟨hxu.1, fun h => hxu.2 (Finset.mem_insert_of_mem h)⟩
          have hxy : x ≠ y := fun h => hxu.2 (h ▸ Finset.mem_insert_self _ _)
          exact (h3b x hx' hxu' hxy).trans
            (mul_le_mul_of_nonneg_left (hymax x hx' hxu') (by linarith))
        unfold RegionTree.reserve
        have := hB v
        nlinarith
      · exact (reserve_white_le hT hP hR hS hB (not_mem_eff_of_active hT hr hv' hvr hy)).trans
          (hres v hv' hvr)
    · show (if Q ∈ T.reqs v ∧ y ∈ Q ∧ y ∈ T.eff s v then s.credit v Q + 1 else s.credit v Q) ≤
        (insert y s.white ∩ Q).card
      split_ifs with hc
      · rw [Finset.insert_inter_of_mem hc.2.1, Finset.card_insert_of_notMem
          (fun h => hyu.2 (Finset.mem_inter.1 h).1)]
        exact Nat.succ_le_succ (hcr v Q)
      · exact (hcr v Q).trans (Finset.card_le_card
          (Finset.inter_subset_inter (Finset.subset_insert _ _) le_rfl))

/-- One round of the potential strategy preserves the invariant (proof of Lemma A.2). -/
theorem round_inv (hT : T.WellFormed) (hP : Properties T Pot σ) {st : T.State}
    (hI : RoundInv (Pot := Pot) st) {x : Pt d} (hxE : x ∈ T.E T.root) (hxu : T.Unused st x)
    (hS : PlayState T Pot st) (hSB : PlayState T Pot (T.blackClaim st x))
    (hSA : PlayState T Pot (T.activationStep Pot (T.blackClaim st x))) :
    RoundInv (Pot := Pot) (T.round Pot st x).1 := by
  obtain ⟨hR, hB, hres, hin, hcr⟩ := hI
  have hσ := hP.sigma
  set stB := T.blackClaim st x with hstB
  have hRB : T.Reachable stB := RegionTree.Reachable.black hR hxE hxu
  -- after Black's claim every potential is at most `1/4`
  have hPB : ∀ v, Pot v stB ≤ 1 / 4 := by
    intro v
    by_cases hxv : x ∈ T.eff st v
    · have h1 : Pot v stB ≤ T.reserve Pot st v := by
        have := le_maxScore Pot hxv hxu
        rw [score_of_mem Pot hxv] at this
        unfold RegionTree.reserve; linarith
      by_cases hva : v ∈ st.active
      · exact h1.trans (hres v hva)
      · have h2 := (maxScore_bounds hP hR hS hB v).2
        have h3 := hin v hva
        have h4 := hP.nonneg st hS v
        unfold RegionTree.reserve at h1
        nlinarith
    · rw [hP.loc_black st (ProbeState.actual hS) v x hxv]; exact hB v
  have hroot : T.root ∈ st.active := reachable_root_active hR
  show RoundInv (Pot := Pot) ((T.reply Pot (T.activationStep Pot stB)
      (T.responsible (T.activationStep Pot stB) x)).elim (T.activationStep Pot stB)
      (T.whiteClaim (T.activationStep Pot stB) ·))
  rcases activationStep_cases Pot stB with ⟨hlow, hact⟩ | ⟨u, hu, hu8, hdeep, hact⟩
  · -- no activation
    rw [hact]
    have hrootB : T.root ∈ stB.active := hroot
    obtain ⟨hr1, -, -⟩ := responsible_spec (T := T) hrootB hxE
    have hxr : x ∈ T.eff st (T.responsible stB x) := responsible_eff hT hrootB hxE
    refine white_step hT hP hRB hSB hPB hlow hr1 (fun w hw hwr => ?_) hcr
    exact (reserve_black_le hT hP hR hS hB (not_mem_eff_of_active hT hr1 hw hwr hxr)).trans
      (hres w hw)
  · -- activation of the deepest crossing vertex `u`
    rw [hact]
    have hu' : u ∉ st.active := hu
    have hxu_eff : x ∈ T.eff st u := by
      by_contra hn
      have : Pot u stB = Pot u st := hP.loc_black st (ProbeState.actual hS) u x hn
      have := hin u hu'
      linarith
    have hsc := score_bounds hP hR hS hB hxu_eff hxu
    rw [score_of_mem Pot hxu_eff] at hsc
    have hPu12 : 1 / 12 ≤ Pot u st := by
      have := hP.nonneg st hS u
      nlinarith
    have hp4 := hP.p4 st hS u x hu' hPu12 hxu_eff hxu
    set st₁ := T.activate stB u with hst₁
    have hR₁ : T.Reachable st₁ := RegionTree.Reachable.act hRB
    have hxuE : x ∈ T.E u := (mem_eff.1 hxu_eff).1
    -- vertices that are not strict ancestors of `u` keep their post-Black potentials
    have hP₁ : ∀ v, Pot v st₁ ≤ 1 / 4 := by
      intro v
      by_cases hv : T.StrictAnc v u
      · exact (hp4 v hv).1.trans (hB v)
      · rw [hP.loc_act stB (ProbeState.actual hSB) u v hv]; exact hPB v
    have hin₁ : ∀ v, v ∉ st₁.active → Pot v st₁ < 1 / 8 := by
      intro v hv
      have hv' : v ∉ insert u st.active := hv
      have hvu : v ≠ u := fun h => hv' (h ▸ Finset.mem_insert_self _ _)
      have hva : v ∉ st.active := fun h => hv' (Finset.mem_insert_of_mem h)
      by_cases hsa : T.StrictAnc v u
      · exact (hp4 v hsa).1.trans_lt (hin v hva)
      · rw [hP.loc_act stB (ProbeState.actual hSB) u v hsa]
        by_contra hge
        rw [not_lt] at hge
        have hxv : x ∈ T.eff st v := by
          by_contra hn
          have : Pot v stB = Pot v st := hP.loc_black st (ProbeState.actual hS) v x hn
          have := hin v hva
          linarith
        rcases comparable hT v u (mem_eff.1 hxv).1 hxuE with h | h
        · exact hsa ⟨h, hvu⟩
        · have h1 := strictAnc_depth hT ⟨h, fun h' => hvu h'.symm⟩
          have h2 := hdeep v hva hge
          omega
    have hroot₁ : T.root ∈ st₁.active := Finset.mem_insert_of_mem hroot
    obtain ⟨hr1, hr2, hr3⟩ := responsible_spec (T := T) hroot₁ hxE
    -- the responsible vertex is `u`
    have hru : T.responsible st₁ x = u := by
      by_contra hne
      have hra : T.responsible st₁ x ∈ st.active := by
        rcases Finset.mem_insert.1 hr1 with h | h
        · exact absurd h hne
        · exact h
      rcases comparable hT u (T.responsible st₁ x) hxuE hr2 with h | h
      · exact (mem_eff.1 hxu_eff).2 _ hra ⟨h, fun h' => hne h'.symm⟩ hr2
      · have h1 := strictAnc_depth hT ⟨h, hne⟩
        have h2 := hr3 u (Finset.mem_insert_self _ _) hxuE
        omega
    rw [hru]
    refine white_step hT hP hR₁ (by simpa [hst₁, hact] using hSA) hP₁ hin₁ (Finset.mem_insert_self _ _) (fun w hw hwu => ?_) hcr
    have hw' : w ∈ st.active := by
      rcases Finset.mem_insert.1 hw with h | h
      · exact absurd h hwu
      · exact h
    by_cases hsa : T.StrictAnc w u
    · exact (hp4 w hsa).2.trans (hres w hw')
    · refine (reserve_act_le hT hP hRB hSB hPB hsa).trans
        ((reserve_black_le hT hP hR hS hB fun hxw => ?_).trans (hres w hw'))
      rcases comparable hT w u (mem_eff.1 hxw).1 hxuE with h | h
      · exact hsa ⟨h, hwu⟩
      · exact (mem_eff.1 hxu_eff).2 w hw' ⟨h, fun h' => hwu h'.symm⟩ (mem_eff.1 hxw).1

theorem init_inv (hP : Properties T Pot σ) :
    RoundInv (Pot := Pot) T.init := by
  have hR : T.Reachable T.init := RegionTree.Reachable.init
  have hS : PlayState T Pot T.init := by
    have hi := PlayState.before (T := T) (Pot := Pot) [] (by intro k hk; simp at hk) 0 (by simp)
    simpa [RegionTree.run] using hi
  have hB : ∀ v, Pot v T.init ≤ 1 / 4 := fun v => (hP.p1_init v).trans (by norm_num)
  refine ⟨hR, hB, fun v _ => ?_, fun v _ => (hP.p1_init v).trans_lt (by norm_num),
    fun v Q => Nat.zero_le _⟩
  have h1 := (maxScore_bounds hP hR hS hB v).2
  have h2 := hP.p1_init v
  have h3 := hP.nonneg _ hS v
  have hσ := hP.sigma
  unfold RegionTree.reserve
  nlinarith

theorem run_take_succ (bs : List (Pt d)) (k : ℕ) (hk : k < bs.length) :
    T.run Pot (bs.take (k + 1)) = (T.round Pot (T.run Pot (bs.take k)) (bs.get ⟨k, hk⟩)).1 := by
  unfold RegionTree.run
  rw [List.take_succ, List.foldl_append, List.getElem?_eq_getElem hk]
  rfl

theorem run_inv (hT : T.WellFormed) (hP : Properties T Pot σ) (bs : List (Pt d))
    (hbs : T.LegalBlack Pot bs) : ∀ k ≤ bs.length, RoundInv (Pot := Pot) (T.run Pot (bs.take k)) := by
  intro k
  induction k with
  | zero => intro _; exact init_inv hP
  | succ k ih =>
    intro hk
    rw [run_take_succ bs k hk]
    exact round_inv hT hP (ih (by omega)) (hbs k hk).1 (hbs k hk).2
      (PlayState.before bs hbs k (by omega)) (PlayState.black bs hbs k hk)
      (PlayState.activated bs hbs k hk)

theorem quotas_of_properties {d : ℕ} (T : RegionTree d) (hT : T.WellFormed) (Pot : T.V → T.State → ℝ)
    (σ : ℝ) (hP : Properties T Pot σ) (bs : List (Pt d)) (hbs : T.LegalBlack Pot bs)
    (hcomplete : ∀ x ∈ T.E T.root, x ∈ (T.run Pot bs).black ∨ x ∈ (T.run Pot bs).white) :
    ∀ v, ∀ Q ∈ T.reqs v, T.quota v Q ≤ ((T.run Pot bs).white ∩ Q).card := by
  have hI := run_inv hT hP bs hbs bs.length le_rfl
  rw [List.take_length] at hI
  obtain ⟨hR, hB, -, -, hcr⟩ := hI
  intro v Q hQ
  by_contra hlt
  rw [not_le] at hlt
  have hc : ((T.run Pot bs).credit v Q : ℝ) ≤ (((T.run Pot bs).white ∩ Q).card : ℝ) :=
    Nat.cast_le.2 (hcr v Q)
  have hpos : 0 < T.outstanding (T.run Pot bs) v Q := by
    unfold RegionTree.outstanding; linarith
  have := hP.p1_detect _ (by simpa using PlayState.before (T := T) (Pot := Pot) bs hbs bs.length le_rfl) v hcomplete ⟨Q, hQ, hpos⟩
  linarith [hB v]


/-- The stronger historical bookkeeping-domain properties imply the localized
ones. This is an implication, not an assertion of a false domain equivalence. -/
theorem of_bookkeeping (hT : T.WellFormed) (hP : T.PotentialProps Pot σ) :
    Properties T Pot σ := by
  have hplay : ∀ st, PlayState T Pot st → T.Reachable st := by
    intro st hs
    cases hs with
    | before bs h k hk => exact (AppendixAAux.run_inv hT hP bs h k hk).1
    | black bs h k hk =>
      exact RegionTree.Reachable.black
        (AppendixAAux.run_inv hT hP bs h k (by omega)).1 (h k hk).1 (h k hk).2
    | activated bs h k hk =>
      have hr := RegionTree.Reachable.black
        (AppendixAAux.run_inv hT hP bs h k (by omega)).1 (h k hk).1 (h k hk).2
      rcases activationStep_cases Pot (T.blackClaim (T.run Pot (bs.take k)) bs[k]) with
        ⟨_, he⟩ | ⟨u, _, _, _, he⟩
      · rw [he]; exact hr
      · rw [he]; exact RegionTree.Reachable.act hr
  have hprobe : ∀ st, ProbeState T Pot st → T.Reachable st := by
    intro st hs
    cases hs with
    | actual h => exact hplay _ h
    | black h hx hu => exact RegionTree.Reachable.black (hplay _ h) hx hu
  exact ⟨hP.sigma, fun st hs => hP.nonneg st (hplay st hs),
    fun st hs => hP.loc_black st (hprobe st hs),
    fun st hs => hP.loc_white st (hprobe st hs),
    fun st hs => hP.loc_act st (hprobe st hs), hP.p1_init,
    fun st hs => hP.p1_detect st (hplay st hs),
    fun st hs => hP.p2 st (hplay st hs),
    fun st hs v y _ _ => hP.p2_white st (hplay st hs) v y,
    fun st hs => hP.p3 st (hplay st hs),
    fun st hs => hP.p4 st (hplay st hs)⟩

end
end BanachDensityHD.ExactStatements.OnPlay
