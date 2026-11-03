import BanachDensityHD.AppendixA

/-!
# Appendix A, Claim A.6: the explicit potentials (construction)

This module follows `AppendixA.lean` (it uses
the Lemma A.2 helpers of `BanachDensityHD.AppendixAAux`: ancestry, `mem_eff`, scores). It holds the
explicit potentials of Claim A.6 (tex l.7313–7682), the helper
`claim_cf_potential_existence_uniform` (uniform `σ = ε/128`) and the derivation of 
`claim_cf_potential_existence` from it.
-/

namespace BanachDensityHD

open Set Filter
open scoped Classical

noncomputable section

namespace AppendixAAux
open RegionTree

variable {d : ℕ} {T : RegionTree d}

/-! ### The explicit potential on an abstract tree with levels (eq. cf-potential) -/

/-- The allowance function `g_k(P) = (12P)^{1/h_k}` (eq. cf-correction-function). -/
def gA (h : ℕ → ℕ) (k : ℕ) (P : ℝ) : ℝ := (12 * P) ^ ((1 : ℝ) / h k)

/-- `n_Q`: the unused points of `Q ∩ E_v^*`. -/
def nQ (st : T.State) (v : T.V) (Q : Finset (Pt d)) : ℕ :=
  ((Q ∩ T.eff st v).filter fun x => T.Unused st x).card

/-- `m_{Qu} = |Q ∩ E_u|`. -/
def mQ (T : RegionTree d) (Q : Finset (Pt d)) (u : T.V) : ℕ := (Q ∩ T.E u).card

/-- `𝒟_v`: the proper descendants `w` of `v` such that no vertex on the path from `v` to `w`,
`v` excluded, is active. -/
def Dset (st : T.State) (v : T.V) : Finset T.V :=
  Finset.univ.filter fun w => T.StrictAnc v w ∧ ∀ z, T.StrictAnc v z → T.Anc z w → z ∉ st.active

section Potential
variable (ℓ : T.V → ℕ) (lam : ℕ → ℝ) (μ : ℝ) (h : ℕ → ℕ)

/-- The exponent of the weight `p_Q` at `v`, given the descendant potentials `P`. -/
def expo (P : T.V → ℝ) (st : T.State) (v : T.V) (Q : Finset (Pt d)) : ℝ :=
  lam (ℓ v) * (2 * T.outstanding st v Q - (1 - μ) * (nQ st v Q : ℝ) +
    ∑ u ∈ Dset st v, (mQ T Q u : ℝ) * gA h (ℓ u) (P u))

/-- One step of the recursion: `P_v = ∑_Q exp(expo)`. -/
def potF (P : T.V → ℝ) (st : T.State) (v : T.V) : ℝ :=
  ∑ Q ∈ T.reqs v, Real.exp (expo ℓ lam μ h P st v Q)

/-- The recursion, iterated `n` times from `0`. -/
def potIter : ℕ → T.V → T.State → ℝ
  | 0 => fun _ _ => 0
  | n + 1 => fun v st => potF ℓ lam μ h (fun u => potIter n u st) st v

/-- The potential is a finite iteration of `potIter`, with `ℓ v + 1` steps. For an arbitrary
level function this is the total definition below; `pot_eq` identifies it with the upward
recursion of eq. cf-potential when levels decrease along strict descendants. -/
def pot (v : T.V) (st : T.State) : ℝ := potIter ℓ lam μ h (ℓ v + 1) v st

end Potential

/-! #### Structural lemmas -/

theorem mem_Dset {st : T.State} {v w : T.V} :
    w ∈ Dset st v ↔ T.StrictAnc v w ∧ ∀ z, T.StrictAnc v z → T.Anc z w → z ∉ st.active := by
  unfold Dset; simp

theorem Dset_congr {s t : T.State} (h : s.active = t.active) (v : T.V) : Dset s v = Dset t v := by
  unfold Dset; rw [h]

theorem Dset_inactive {st : T.State} {v w : T.V} (hw : w ∈ Dset st v) : w ∉ st.active :=
  (mem_Dset.1 hw).2 w (mem_Dset.1 hw).1 (RegionTree.Anc.refl _)

theorem strictAnc_trans (hT : T.WellFormed) {a b c : T.V} (h1 : T.StrictAnc a b)
    (h2 : T.StrictAnc b c) : T.StrictAnc a c :=
  ⟨anc_trans h1.1 h2.1, fun h => by
    subst h
    have := strictAnc_depth hT h1
    have := strictAnc_depth hT h2
    omega⟩

/-- A point not counted at `v` is not counted at any monitored descendant. -/
theorem not_eff_of_Dset (hT : T.WellFormed) {st : T.State} {v w : T.V} (hw : w ∈ Dset st v)
    {x : Pt d} (hx : x ∉ T.eff st v) : x ∉ T.eff st w := by
  intro hxw
  have hxw' := mem_eff.1 hxw
  have hxv : x ∈ T.E v := E_anti hT (mem_Dset.1 hw).1.1 hxw'.1
  rw [mem_eff] at hx
  push_neg at hx
  obtain ⟨a, ha, hva, hxa⟩ := hx hxv
  rcases comparable hT a w hxa hxw'.1 with h | h
  · exact (mem_Dset.1 hw).2 a hva h ha
  · have hne : w ≠ a := fun h' => Dset_inactive hw (h' ▸ ha)
    exact hxw'.2 a ha ⟨h, hne⟩ hxa

theorem Dset_activate_of_not {st : T.State} {u v : T.V} (h : ¬ T.StrictAnc v u) :
    Dset (T.activate st u) v = Dset st v := by
  ext w
  rw [mem_Dset, mem_Dset]
  refine and_congr_right fun _ => forall_congr' fun z => forall_congr' fun hvz =>
    forall_congr' fun _ => ?_
  constructor
  · exact fun hz hz' => hz (Finset.mem_insert_of_mem hz')
  · intro hz hz'
    rcases Finset.mem_insert.1 hz' with rfl | hz'
    · exact h hvz
    · exact hz hz'

/-- `n_Q` before a claim at `x` equals `n_Q` after it plus the indicator that `x` was an unused
point of `Q ∩ E_v^*` (for any claim that uses `x` and keeps the active set). -/
theorem nQ_claim {s t : T.State} (hact : t.active = s.active) {x : Pt d}
    (hun : ∀ z, T.Unused t z ↔ T.Unused s z ∧ z ≠ x) (v : T.V) (Q : Finset (Pt d)) :
    (nQ s v Q : ℝ) = nQ t v Q + if x ∈ Q ∧ x ∈ T.eff s v ∧ T.Unused s x then 1 else 0 := by
  unfold nQ
  rw [eff_congr hact]
  split_ifs with hc
  · have : ((Q ∩ T.eff s v).filter fun z => T.Unused s z) =
        insert x ((Q ∩ T.eff s v).filter fun z => T.Unused t z) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_inter, hun]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hzx : z = x
        · exact Or.inl hzx
        · exact Or.inr ⟨h1, h2, hzx⟩
      · rintro (rfl | ⟨h1, h2, -⟩)
        · exact ⟨⟨hc.1, hc.2.1⟩, hc.2.2⟩
        · exact ⟨h1, h2⟩
    rw [this, Finset.card_insert_of_notMem (by simp [hun])]
    push_cast; ring
  · have : ((Q ∩ T.eff s v).filter fun z => T.Unused s z) =
        ((Q ∩ T.eff s v).filter fun z => T.Unused t z) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_inter, hun]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, h2, ?_⟩
        rintro rfl
        exact hc ⟨h1.1, h1.2, h2⟩
      · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
    rw [this]; simp

theorem unused_black (s : T.State) (x z : Pt d) :
    T.Unused (T.blackClaim s x) z ↔ T.Unused s z ∧ z ≠ x := by
  unfold RegionTree.Unused
  change z ∉ insert x s.black ∧ z ∉ s.white ↔ _
  rw [Finset.mem_insert]; tauto

theorem unused_white (s : T.State) (x z : Pt d) :
    T.Unused (T.whiteClaim s x) z ↔ T.Unused s z ∧ z ≠ x := by
  unfold RegionTree.Unused
  change z ∉ s.black ∧ z ∉ insert x s.white ↔ _
  rw [Finset.mem_insert]; tauto

theorem outstanding_white (s : T.State) (y : Pt d) (v : T.V) (Q : Finset (Pt d))
    (hQ : Q ∈ T.reqs v) :
    T.outstanding (T.whiteClaim s y) v Q =
      T.outstanding s v Q - if y ∈ Q ∧ y ∈ T.eff s v then 1 else 0 := by
  unfold RegionTree.outstanding
  change T.quota v Q - ((if Q ∈ T.reqs v ∧ y ∈ Q ∧ y ∈ T.eff s v then s.credit v Q + 1
    else s.credit v Q : ℕ) : ℝ) = _
  by_cases hc : y ∈ Q ∧ y ∈ T.eff s v
  · rw [if_pos ⟨hQ, hc⟩, if_pos hc]; push_cast; ring
  · rw [if_neg (fun h => hc h.2), if_neg hc]; ring

section Potential
variable (ℓ : T.V → ℕ) (lam : ℕ → ℝ) (μ : ℝ) (h : ℕ → ℕ)

/-- The recursion stabilizes: from `ℓ v + 1` iterations on, the value at `v` is `pot v`. -/
theorem potIter_stable (hℓ : ∀ a b : T.V, T.StrictAnc a b → ℓ b < ℓ a) (st : T.State) :
    ∀ v n, ℓ v + 1 ≤ n → potIter ℓ lam μ h n v st = pot ℓ lam μ h v st := by
  intro v
  induction hn : ℓ v using Nat.strong_induction_on generalizing v with
  | _ k ih =>
    intro n hkn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    unfold pot
    rw [hn]
    show potF ℓ lam μ h (fun u => potIter ℓ lam μ h m u st) st v =
      potF ℓ lam μ h (fun u => potIter ℓ lam μ h k u st) st v
    unfold potF expo
    refine Finset.sum_congr rfl fun Q _ => ?_
    congr 3
    refine Finset.sum_congr rfl fun u hu => ?_
    have hlt : ℓ u < k := hn ▸ hℓ v u (mem_Dset.1 hu).1
    dsimp only
    rw [ih (ℓ u) hlt u rfl m (by omega), ih (ℓ u) hlt u rfl k (by omega)]

/-- The defining equation of the potential (eq. cf-potential). -/
theorem pot_eq (hℓ : ∀ a b : T.V, T.StrictAnc a b → ℓ b < ℓ a) (v : T.V) (st : T.State) :
    pot ℓ lam μ h v st = potF ℓ lam μ h (fun u => pot ℓ lam μ h u st) st v := by
  show potF ℓ lam μ h (fun u => potIter ℓ lam μ h (ℓ v) u st) st v = _
  unfold potF expo
  refine Finset.sum_congr rfl fun Q _ => ?_
  congr 3
  refine Finset.sum_congr rfl fun u hu => ?_
  dsimp only
  rw [potIter_stable ℓ lam μ h hℓ st u (ℓ v) (hℓ v u (mem_Dset.1 hu).1)]

theorem pot_nonneg (hℓ : ∀ a b : T.V, T.StrictAnc a b → ℓ b < ℓ a) (v : T.V) (st : T.State) :
    0 ≤ pot ℓ lam μ h v st := by
  rw [pot_eq ℓ lam μ h hℓ]
  exact Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le

/-- The exponent after a Black claim at `x`. -/
theorem expo_black (P P' : T.V → ℝ) (s : T.State) (x : Pt d) (v : T.V) (Q : Finset (Pt d)) :
    expo ℓ lam μ h P' (T.blackClaim s x) v Q - expo ℓ lam μ h P s v Q =
      lam (ℓ v) * ((1 - μ) * (if x ∈ Q ∧ x ∈ T.eff s v ∧ T.Unused s x then 1 else 0) +
        ∑ u ∈ Dset s v, (mQ T Q u : ℝ) * (gA h (ℓ u) (P' u) - gA h (ℓ u) (P u))) := by
  unfold expo
  have hD : Dset (T.blackClaim s x) v = Dset s v := Dset_congr rfl v
  rw [nQ_claim (s := s) (t := T.blackClaim s x) rfl (unused_black s x) v Q, hD]
  have : T.outstanding (T.blackClaim s x) v Q = T.outstanding s v Q := rfl
  rw [this]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- The exponent after a White claim at `y`, for a requirement `Q ∈ 𝒜_v`. -/
theorem expo_white (P P' : T.V → ℝ) (s : T.State) (y : Pt d) (v : T.V) (Q : Finset (Pt d))
    (hQ : Q ∈ T.reqs v) :
    expo ℓ lam μ h P s v Q - expo ℓ lam μ h P' (T.whiteClaim s y) v Q =
      lam (ℓ v) * (2 * (if y ∈ Q ∧ y ∈ T.eff s v then 1 else 0) -
        (1 - μ) * (if y ∈ Q ∧ y ∈ T.eff s v ∧ T.Unused s y then 1 else 0) +
        ∑ u ∈ Dset s v, (mQ T Q u : ℝ) * (gA h (ℓ u) (P u) - gA h (ℓ u) (P' u))) := by
  unfold expo
  have hD : Dset (T.whiteClaim s y) v = Dset s v := Dset_congr rfl v
  rw [nQ_claim (s := s) (t := T.whiteClaim s y) rfl (unused_white s y) v Q, hD,
    outstanding_white s y v Q hQ]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

end Potential

/-! #### The allowance function -/

theorem gA_nonneg (h : ℕ → ℕ) (k : ℕ) {P : ℝ} (hP : 0 ≤ P) : 0 ≤ gA h k P :=
  Real.rpow_nonneg (by positivity) _

theorem gA_mono (h : ℕ → ℕ) (k : ℕ) {P P' : ℝ} (hP : 0 ≤ P) (hPP : P ≤ P') :
    gA h k P ≤ gA h k P' :=
  Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)

theorem gA_ge_one (h : ℕ → ℕ) (k : ℕ) {P : ℝ} (hP : 1 / 12 ≤ P) : 1 ≤ gA h k P :=
  Real.one_le_rpow (by linarith) (by positivity)

section Qualitative
variable (ℓ : T.V → ℕ) (lam : ℕ → ℝ) (μ : ℝ) (h : ℕ → ℕ)
  (hT : T.WellFormed) (hℓ : ∀ a b : T.V, T.StrictAnc a b → ℓ b < ℓ a)

include hT hℓ

/-- Locality: a Black claim outside `E_v^*` leaves `P_v` unchanged. -/
theorem pot_black_loc : ∀ (v : T.V) (s : T.State) (x : Pt d), x ∉ T.eff s v →
    pot ℓ lam μ h v (T.blackClaim s x) = pot ℓ lam μ h v s := by
  intro v
  induction hn : ℓ v using Nat.strong_induction_on generalizing v with
  | _ k ih =>
    intro s x hx
    rw [pot_eq ℓ lam μ h hℓ v (T.blackClaim s x), pot_eq ℓ lam μ h hℓ v s]
    unfold potF
    refine Finset.sum_congr rfl fun Q _ => ?_
    congr 1
    have := expo_black ℓ lam μ h (fun u => pot ℓ lam μ h u s)
      (fun u => pot ℓ lam μ h u (T.blackClaim s x)) s x v Q
    have hsum : ∑ u ∈ Dset s v, (mQ T Q u : ℝ) * (gA h (ℓ u) (pot ℓ lam μ h u (T.blackClaim s x)) -
        gA h (ℓ u) (pot ℓ lam μ h u s)) = 0 := Finset.sum_eq_zero fun u hu => by
      rw [ih (ℓ u) (hn ▸ hℓ v u (mem_Dset.1 hu).1) u rfl s x (not_eff_of_Dset hT hu hx)]; ring
    rw [if_neg (fun h => hx h.2.1), hsum] at this
    simp only [mul_zero, add_zero, sub_eq_zero] at this
    exact this

/-- Locality: a White claim outside `E_v^*` leaves `P_v` unchanged. -/
theorem pot_white_loc : ∀ (v : T.V) (s : T.State) (y : Pt d), y ∉ T.eff s v →
    pot ℓ lam μ h v (T.whiteClaim s y) = pot ℓ lam μ h v s := by
  intro v
  induction hn : ℓ v using Nat.strong_induction_on generalizing v with
  | _ k ih =>
    intro s y hy
    rw [pot_eq ℓ lam μ h hℓ v (T.whiteClaim s y), pot_eq ℓ lam μ h hℓ v s]
    unfold potF
    refine Finset.sum_congr rfl fun Q hQ => ?_
    congr 1
    have := expo_white ℓ lam μ h (fun u => pot ℓ lam μ h u s)
      (fun u => pot ℓ lam μ h u (T.whiteClaim s y)) s y v Q hQ
    have hsum : ∑ u ∈ Dset s v, (mQ T Q u : ℝ) * (gA h (ℓ u) (pot ℓ lam μ h u s) -
        gA h (ℓ u) (pot ℓ lam μ h u (T.whiteClaim s y))) = 0 := Finset.sum_eq_zero fun u hu => by
      rw [ih (ℓ u) (hn ▸ hℓ v u (mem_Dset.1 hu).1) u rfl s y (not_eff_of_Dset hT hu hy)]; ring
    rw [if_neg (fun h => hy h.2), if_neg (fun h => hy h.2.1), hsum] at this
    simp only [mul_zero, sub_zero, add_zero, sub_eq_zero] at this
    exact this.symm

/-- Locality: activating `u` changes potentials only at strict ancestors of `u`. -/
theorem pot_act_loc : ∀ (v : T.V) (s : T.State) (u : T.V), ¬ T.StrictAnc v u →
    pot ℓ lam μ h v (T.activate s u) = pot ℓ lam μ h v s := by
  intro v
  induction hn : ℓ v using Nat.strong_induction_on generalizing v with
  | _ k ih =>
    intro s u hvu
    rw [pot_eq ℓ lam μ h hℓ v (T.activate s u), pot_eq ℓ lam μ h hℓ v s]
    unfold potF expo
    have hn' : ∀ Q, nQ (T.activate s u) v Q = nQ s v Q := by
      intro Q; unfold nQ; rw [eff_activate_of_not hvu]; rfl
    refine Finset.sum_congr rfl fun Q _ => ?_
    rw [hn' Q, Dset_activate_of_not hvu]
    have hsum : ∑ w ∈ Dset s v, (mQ T Q w : ℝ) * gA h (ℓ w) (pot ℓ lam μ h w (T.activate s u)) =
        ∑ w ∈ Dset s v, (mQ T Q w : ℝ) * gA h (ℓ w) (pot ℓ lam μ h w s) :=
      Finset.sum_congr rfl fun w hw => by
        have hwu : ¬ T.StrictAnc w u := fun hwu =>
          hvu (strictAnc_trans hT (mem_Dset.1 hw).1 hwu)
        rw [ih (ℓ w) (hn ▸ hℓ v w (mem_Dset.1 hw).1) w rfl s u hwu]
    rw [hsum]; rfl

variable (hlam : ∀ k, 0 ≤ lam k) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
include hlam hμ0 hμ1

omit hT hμ0 in
/-- A Black claim never decreases a potential (at any state, any point). -/
theorem pot_black_mono : ∀ (v : T.V) (s : T.State) (x : Pt d),
    pot ℓ lam μ h v s ≤ pot ℓ lam μ h v (T.blackClaim s x) := by
  intro v
  induction hn : ℓ v using Nat.strong_induction_on generalizing v with
  | _ k ih =>
    intro s x
    rw [pot_eq ℓ lam μ h hℓ v (T.blackClaim s x), pot_eq ℓ lam μ h hℓ v s]
    refine Finset.sum_le_sum fun Q _ => Real.exp_le_exp.2 ?_
    have := expo_black ℓ lam μ h (fun u => pot ℓ lam μ h u s)
      (fun u => pot ℓ lam μ h u (T.blackClaim s x)) s x v Q
    have h1 : 0 ≤ lam (ℓ v) * ((1 - μ) * (if x ∈ Q ∧ x ∈ T.eff s v ∧ T.Unused s x then 1 else 0) +
        ∑ u ∈ Dset s v, (mQ T Q u : ℝ) * (gA h (ℓ u) (pot ℓ lam μ h u (T.blackClaim s x)) -
          gA h (ℓ u) (pot ℓ lam μ h u s))) := by
      refine mul_nonneg (hlam _) (add_nonneg (mul_nonneg (by linarith) (by split_ifs <;> norm_num))
        (Finset.sum_nonneg fun u hu => mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.2 ?_)))
      exact gA_mono h _ (pot_nonneg ℓ lam μ h hℓ u s)
        (ih (ℓ u) (hn ▸ hℓ v u (mem_Dset.1 hu).1) u rfl s x)
    linarith

omit hT hμ1 in
/-- A White claim never increases a potential (at any state, any point). -/
theorem pot_white_mono : ∀ (v : T.V) (s : T.State) (y : Pt d),
    pot ℓ lam μ h v (T.whiteClaim s y) ≤ pot ℓ lam μ h v s := by
  intro v
  induction hn : ℓ v using Nat.strong_induction_on generalizing v with
  | _ k ih =>
    intro s y
    rw [pot_eq ℓ lam μ h hℓ v (T.whiteClaim s y), pot_eq ℓ lam μ h hℓ v s]
    refine Finset.sum_le_sum fun Q hQ => Real.exp_le_exp.2 ?_
    have := expo_white ℓ lam μ h (fun u => pot ℓ lam μ h u s)
      (fun u => pot ℓ lam μ h u (T.whiteClaim s y)) s y v Q hQ
    have hc : (0 : ℝ) ≤ 2 * (if y ∈ Q ∧ y ∈ T.eff s v then 1 else 0) -
        (1 - μ) * (if y ∈ Q ∧ y ∈ T.eff s v ∧ T.Unused s y then 1 else 0) := by
      by_cases h1 : y ∈ Q ∧ y ∈ T.eff s v
      · rw [if_pos h1]; split_ifs <;> linarith
      · rw [if_neg h1, if_neg fun h2 => h1 ⟨h2.1, h2.2.1⟩]; norm_num
    have h1 : 0 ≤ lam (ℓ v) * (2 * (if y ∈ Q ∧ y ∈ T.eff s v then 1 else 0) -
        (1 - μ) * (if y ∈ Q ∧ y ∈ T.eff s v ∧ T.Unused s y then 1 else 0) +
        ∑ u ∈ Dset s v, (mQ T Q u : ℝ) * (gA h (ℓ u) (pot ℓ lam μ h u s) -
          gA h (ℓ u) (pot ℓ lam μ h u (T.whiteClaim s y)))) := by
      refine mul_nonneg (hlam _) (add_nonneg hc
        (Finset.sum_nonneg fun u hu => mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.2 ?_)))
      exact gA_mono h _ (pot_nonneg ℓ lam μ h hℓ u _)
        (ih (ℓ u) (hn ▸ hℓ v u (mem_Dset.1 hu).1) u rfl s y)
    linarith

omit hlam hμ0 hμ1 in
/-- (P1), detection: once every board point is used, an unmet quota at `v` forces `P_v ≥ 1`. -/
theorem pot_detect (hlampos : ∀ k, 0 < lam k) (s : T.State) (v : T.V)
    (hall : ∀ x ∈ T.E T.root, x ∈ s.black ∨ x ∈ s.white) (Q : Finset (Pt d)) (hQ : Q ∈ T.reqs v)
    (hout : 0 < T.outstanding s v Q) : 1 ≤ pot ℓ lam μ h v s := by
  have hn : nQ s v Q = 0 := by
    unfold nQ
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro z hz hu
    have hzE : z ∈ T.E T.root := eff_sub_root hT s v (Finset.mem_inter.1 hz).2
    rcases hall z hzE with h1 | h1
    · exact hu.1 h1
    · exact hu.2 h1
  have hA : 0 ≤ ∑ u ∈ Dset s v, (mQ T Q u : ℝ) * gA h (ℓ u) (pot ℓ lam μ h u s) :=
    Finset.sum_nonneg fun u _ => mul_nonneg (Nat.cast_nonneg _)
      (gA_nonneg h _ (pot_nonneg ℓ lam μ h hℓ u s))
  have hE : 0 < expo ℓ lam μ h (fun u => pot ℓ lam μ h u s) s v Q := by
    unfold expo
    rw [hn]
    have := hlampos (ℓ v)
    push_cast
    nlinarith
  rw [pot_eq ℓ lam μ h hℓ v s]
  unfold potF
  calc (1 : ℝ) ≤ Real.exp (expo ℓ lam μ h (fun u => pot ℓ lam μ h u s) s v Q) :=
        Real.one_le_exp hE.le
    _ ≤ _ := Finset.single_le_sum (f := fun Q => Real.exp
          (expo ℓ lam μ h (fun u => pot ℓ lam μ h u s) s v Q)) (fun _ _ => (Real.exp_pos _).le) hQ

/-- (P4), potential part: if `u` with `P_u ≥ 1/12` is activated after a Black claim
at `x ∈ E_u^*`, no strict ancestor's potential increases. This potential comparison does
not require `u` to have been inactive. -/
theorem pot_p4 (s : T.State) (u : T.V) (x : Pt d)
    (hPu : 1 / 12 ≤ pot ℓ lam μ h u s) (hx : x ∈ T.eff s u) : ∀ v, T.StrictAnc v u →
      pot ℓ lam μ h v (T.activate (T.blackClaim s x) u) ≤ pot ℓ lam μ h v s := by
  set st' := T.activate (T.blackClaim s x) u with hst'
  have hxEu : x ∈ T.E u := (mem_eff.1 hx).1
  have hact' : st'.active = insert u s.active := rfl
  intro v
  induction hn : ℓ v using Nat.strong_induction_on generalizing v with
  | _ k ih =>
    intro hvu
    -- monitored descendants after the move: their potentials did not increase
    have hDsub : Dset st' v ⊆ Dset s v := by
      intro w hw
      rw [mem_Dset] at hw ⊢
      exact ⟨hw.1, fun z hz hzw hza => hw.2 z hz hzw (Finset.mem_insert_of_mem hza)⟩
    have hF2 : ∀ w ∈ Dset st' v, pot ℓ lam μ h w st' ≤ pot ℓ lam μ h w s := by
      intro w hw
      have hw' := mem_Dset.1 hw
      by_cases hwu : T.StrictAnc w u
      · exact ih (ℓ w) (hn ▸ hℓ v w hw'.1) w rfl hwu
      · rw [hst', pot_act_loc ℓ lam μ h hT hℓ w _ u hwu]
        refine le_of_eq (pot_black_loc ℓ lam μ h hT hℓ w s x fun hxw => ?_)
        rcases comparable hT w u (mem_eff.1 hxw).1 hxEu with h1 | h1
        · by_cases hwu' : w = u
          · subst hwu'; exact hw'.2 w hvu (RegionTree.Anc.refl _) (Finset.mem_insert_self _ _)
          · exact hwu ⟨h1, hwu'⟩
        · exact hw'.2 u hvu h1 (Finset.mem_insert_self _ _)
    -- points counted at `v` outside `E_u` stay counted
    have heff : ∀ z, z ∈ T.eff s v → z ∉ T.E u → z ∈ T.eff st' v := by
      intro z hz hzu
      refine mem_eff.2 ⟨(mem_eff.1 hz).1, fun a ha hva => ?_⟩
      rcases Finset.mem_insert.1 (hact' ▸ ha) with rfl | ha'
      · exact hzu
      · exact (mem_eff.1 hz).2 a ha' hva
    have hunused : ∀ z, T.Unused s z → z ∉ T.E u → T.Unused st' z := by
      intro z hz hzu
      refine ⟨fun h1 => ?_, hz.2⟩
      rcases Finset.mem_insert.1 h1 with rfl | h1
      · exact hzu hxEu
      · exact hz.1 h1
    rw [pot_eq ℓ lam μ h hℓ v st', pot_eq ℓ lam μ h hℓ v s]
    refine Finset.sum_le_sum fun Q _ => Real.exp_le_exp.2 ?_
    unfold expo
    have hout : T.outstanding st' v Q = T.outstanding s v Q := rfl
    rw [hout]
    refine mul_le_mul_of_nonneg_left ?_ (hlam _)
    have hA' : ∑ w ∈ Dset st' v, (mQ T Q w : ℝ) * gA h (ℓ w) (pot ℓ lam μ h w st') ≤
        ∑ w ∈ Dset st' v, (mQ T Q w : ℝ) * gA h (ℓ w) (pot ℓ lam μ h w s) :=
      Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_left
        (gA_mono h _ (pot_nonneg ℓ lam μ h hℓ w _) (hF2 w hw)) (Nat.cast_nonneg _)
    have hterm : ∀ w, 0 ≤ (mQ T Q w : ℝ) * gA h (ℓ w) (pot ℓ lam μ h w s) := fun w =>
      mul_nonneg (Nat.cast_nonneg _) (gA_nonneg h _ (pot_nonneg ℓ lam μ h hℓ w s))
    by_cases huD : u ∈ Dset s v
    · -- `u` was monitored: its allowance pays for the lost points
      have hsub : Dset st' v ⊆ (Dset s v).erase u := by
        intro w hw
        refine Finset.mem_erase.2 ⟨fun h1 => ?_, hDsub hw⟩
        subst h1
        exact Dset_inactive hw (Finset.mem_insert_self _ _)
      have hA2 : ∑ w ∈ Dset st' v, (mQ T Q w : ℝ) * gA h (ℓ w) (pot ℓ lam μ h w s) ≤
          ∑ w ∈ (Dset s v).erase u, (mQ T Q w : ℝ) * gA h (ℓ w) (pot ℓ lam μ h w s) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun w _ _ => hterm w
      have hA3 := Finset.sum_erase_add (Dset s v)
        (f := fun w => (mQ T Q w : ℝ) * gA h (ℓ w) (pot ℓ lam μ h w s)) huD
      have hg1 : (mQ T Q u : ℝ) ≤ (mQ T Q u : ℝ) * gA h (ℓ u) (pot ℓ lam μ h u s) :=
        le_mul_of_one_le_right (Nat.cast_nonneg _) (gA_ge_one h _ hPu)
      have hn1 : (nQ s v Q : ℝ) ≤ nQ st' v Q + mQ T Q u := by
        have : ((Q ∩ T.eff s v).filter fun z => T.Unused s z) ⊆
            ((Q ∩ T.eff st' v).filter fun z => T.Unused st' z) ∪ (Q ∩ T.E u) := by
          intro z hz
          obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
          obtain ⟨hzQ, hze⟩ := Finset.mem_inter.1 hz1
          by_cases hzu : z ∈ T.E u
          · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hzQ, hzu⟩)
          · exact Finset.mem_union_left _ (Finset.mem_filter.2
              ⟨Finset.mem_inter.2 ⟨hzQ, heff z hze hzu⟩, hunused z hz2 hzu⟩)
        unfold nQ mQ
        exact_mod_cast (Finset.card_le_card this).trans (Finset.card_union_le _ _)
      have hn2 : (nQ st' v Q : ℝ) ≤ nQ s v Q := by
        unfold nQ
        refine Nat.cast_le.2 (Finset.card_le_card fun z hz => ?_)
        obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
        obtain ⟨hzQ, hze⟩ := Finset.mem_inter.1 hz1
        refine Finset.mem_filter.2 ⟨Finset.mem_inter.2 ⟨hzQ, mem_eff.2 ⟨(mem_eff.1 hze).1,
          fun a ha hva => (mem_eff.1 hze).2 a (Finset.mem_insert_of_mem ha) hva⟩⟩,
          fun h1 => hz2.1 (Finset.mem_insert_of_mem h1), hz2.2⟩
      nlinarith
    · -- `u` was already separated from `v` by an active vertex: nothing counted at `v` is lost
      have hn1 : (nQ s v Q : ℝ) ≤ nQ st' v Q := by
        rw [mem_Dset] at huD
        push_neg at huD
        obtain ⟨z, hvz, hzu, hza⟩ := huD hvu
        unfold nQ
        refine Nat.cast_le.2 (Finset.card_le_card fun z' hz' => ?_)
        obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz'
        obtain ⟨hzQ, hze⟩ := Finset.mem_inter.1 hz1
        have hz'u : z' ∉ T.E u := fun h1 =>
          (mem_eff.1 hze).2 z hza hvz (E_anti hT hzu h1)
        exact Finset.mem_filter.2 ⟨Finset.mem_inter.2 ⟨hzQ, heff z' hze hz'u⟩,
          hunused z' hz2 hz'u⟩
      have hA2 : ∑ w ∈ Dset st' v, (mQ T Q w : ℝ) * gA h (ℓ w) (pot ℓ lam μ h w s) ≤
          ∑ w ∈ Dset s v, (mQ T Q w : ℝ) * gA h (ℓ w) (pot ℓ lam μ h w s) :=
        Finset.sum_le_sum_of_subset_of_nonneg hDsub fun w _ _ => hterm w
      nlinarith

omit hT hμ0 in
/-- Black scores are nonnegative at every state. -/
theorem pot_score_nonneg (s : T.State) (v : T.V) (z : Pt d) :
    0 ≤ T.score (pot ℓ lam μ h) s v z := by
  unfold RegionTree.score
  split_ifs
  · exact sub_nonneg.2 (pot_black_mono ℓ lam μ h hℓ hlam hμ1 v s z)
  · exact le_rfl

/-- (P4), reserve part. -/
theorem reserve_p4 (s : T.State) (u : T.V) (x : Pt d)
    (hPu : 1 / 12 ≤ pot ℓ lam μ h u s) (hx : x ∈ T.eff s u) (v : T.V)
    (hvu : T.StrictAnc v u) :
    T.reserve (pot ℓ lam μ h) (T.activate (T.blackClaim s x) u) v ≤
      T.reserve (pot ℓ lam μ h) s v := by
  set st' := T.activate (T.blackClaim s x) u with hst'
  have hP := pot_p4 ℓ lam μ h hT hℓ hlam hμ0 hμ1 s u x hPu hx v hvu
  have hM0 : 0 ≤ T.maxScore (pot ℓ lam μ h) s v :=
    maxScore_nonneg _ fun z _ _ => pot_score_nonneg ℓ lam μ h hℓ hlam hμ1 s v z
  unfold RegionTree.reserve
  have hc : T.maxScore (pot ℓ lam μ h) st' v ≤
      T.maxScore (pot ℓ lam μ h) s v + pot ℓ lam μ h v s - pot ℓ lam μ h v st' := by
    refine maxScore_le _ (by linarith) fun y hy hyu => ?_
    have hyEu : y ∉ T.E u := fun h1 => (mem_eff.1 hy).2 u (Finset.mem_insert_self _ _) hvu h1
    have hys : y ∈ T.eff s v := mem_eff.2 ⟨(mem_eff.1 hy).1,
      fun a ha hva => (mem_eff.1 hy).2 a (Finset.mem_insert_of_mem ha) hva⟩
    have hyus : T.Unused s y := ⟨fun h1 => hyu.1 (Finset.mem_insert_of_mem h1), hyu.2⟩
    have hyx : y ≠ x := fun h1 => hyu.1 (h1 ▸ Finset.mem_insert_self _ _)
    have hPu' : 1 / 12 ≤ pot ℓ lam μ h u (T.blackClaim s y) := by
      rw [pot_black_loc ℓ lam μ h hT hℓ u s y fun h1 => hyEu (mem_eff.1 h1).1]; exact hPu
    have h1 := pot_p4 ℓ lam μ h hT hℓ hlam hμ0 hμ1 (T.blackClaim s y) u x hPu' hx v hvu
    have h2 : T.blackClaim st' y = T.activate (T.blackClaim (T.blackClaim s y) x) u := by
      rw [hst', blackClaim_activate, blackClaim_comm]
    rw [score_of_mem _ hy, h2]
    have h3 := le_maxScore (pot ℓ lam μ h) hys hyus
    rw [score_of_mem _ hys] at h3
    linarith
  linarith

end Qualitative

/-! #### Real analysis of the allowance function and of the exponential weights -/

/-- Concavity of `g_k` in tangent form: `g(P') - g(P) ≤ (g(P)/(h_k P)) (P' - P)` for `P > 0`. -/
theorem gA_tangent (h : ℕ → ℕ) (k : ℕ) (hk : 1 ≤ h k) {P P' : ℝ} (hP : 0 < P) (hP' : 0 ≤ P') :
    gA h k P' - gA h k P ≤ gA h k P / (h k * P) * (P' - P) := by
  have hq0 : (0 : ℝ) ≤ 1 / (h k : ℝ) := by positivity
  have hhk : (1 : ℝ) ≤ h k := by exact_mod_cast hk
  have hq1 : 1 / (h k : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hhk
  have hX : 0 < 12 * P := by linarith
  unfold gA
  have hsplit : 12 * P' = (12 * P) * (1 + (P' / P - 1)) := by field_simp; ring
  rw [hsplit, Real.mul_rpow hX.le (by have := div_nonneg hP' hP.le; linarith)]
  have hb := rpow_one_add_le_one_add_mul_self (s := P' / P - 1)
    (by have := div_nonneg hP' hP.le; linarith) hq0 hq1
  have hXq : 0 ≤ (12 * P) ^ (1 / (h k : ℝ)) := Real.rpow_nonneg hX.le _
  have : (12 * P) ^ (1 / (h k : ℝ)) / (h k * P) * (P' - P) =
      (12 * P) ^ (1 / (h k : ℝ)) * (1 / (h k : ℝ) * (P' / P - 1)) := by
    field_simp
  rw [this]
  nlinarith

/-- For `P ≤ 1/4`, `g_k(P) ≤ 1 + 2/h_k`. -/
theorem gA_le (h : ℕ → ℕ) (k : ℕ) (hk : 2 ≤ h k) {P : ℝ} (hP : 0 ≤ P) (hP4 : P ≤ 1 / 4) :
    gA h k P ≤ 1 + 2 / h k := by
  have hhk : (2 : ℝ) ≤ h k := by exact_mod_cast hk
  have hq0 : (0 : ℝ) ≤ 1 / (h k : ℝ) := by positivity
  have hq1 : 1 / (h k : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  unfold gA
  calc (12 * P) ^ (1 / (h k : ℝ)) ≤ (1 + 2) ^ (1 / (h k : ℝ)) :=
        Real.rpow_le_rpow (by positivity) (by linarith) hq0
    _ ≤ 1 + 1 / (h k : ℝ) * 2 := rpow_one_add_le_one_add_mul_self (by norm_num) hq0 hq1
    _ = 1 + 2 / h k := by ring

/-- (eq. cf-g-white), Black part: `0 ≤ g(P^B) - g(P) ≤ 2ρ/h`. -/
theorem gA_black_incr (h : ℕ → ℕ) (k : ℕ) (hk : 2 ≤ h k) {P PB ρ : ℝ} (hP : 0 ≤ P)
    (hP4 : P ≤ 1 / 4) (hPB : P ≤ PB) (hPB' : PB - P ≤ ρ * P) (hρ : 0 ≤ ρ) :
    0 ≤ gA h k PB - gA h k P ∧ gA h k PB - gA h k P ≤ 2 * ρ / h k := by
  refine ⟨sub_nonneg.2 (gA_mono h k hP hPB), ?_⟩
  have hhk : (2 : ℝ) ≤ h k := by exact_mod_cast hk
  rcases hP.lt_or_eq with hP0 | hP0
  · have h1 := gA_tangent h k (by omega) hP0 (hP.trans hPB)
    have h2 := gA_le h k hk hP hP4
    have h3 : gA h k P / (h k * P) * (PB - P) ≤ gA h k P / (h k * P) * (ρ * P) :=
      mul_le_mul_of_nonneg_left hPB' (div_nonneg (gA_nonneg h k hP) (by positivity))
    have h4 : gA h k P / (h k * P) * (ρ * P) = gA h k P * ρ / h k := by field_simp
    have h5 : gA h k P * ρ / h k ≤ 2 * ρ / h k := by
      apply div_le_div_of_nonneg_right _ (by linarith)
      have : 2 / (h k : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hhk
      nlinarith
    linarith
  · subst hP0
    have : PB = 0 := by nlinarith
    subst this
    have : (0 : ℝ) ≤ 2 * ρ / h k := by positivity
    linarith

/-- (eq. cf-g-white), White part: `0 ≤ g(P) - g(P^W) ≤ 4ρ/h`. -/
theorem gA_white_decr (h : ℕ → ℕ) (k : ℕ) (hk : 2 ≤ h k) {P PW ρ : ℝ} (hP4 : P ≤ 1 / 4)
    (hPW : 0 ≤ PW) (hPWP : PW ≤ P) (hPW' : (1 - ρ) * P ≤ PW) (hρ : 0 ≤ ρ) (hρ2 : ρ ≤ 1 / 2) :
    0 ≤ gA h k P - gA h k PW ∧ gA h k P - gA h k PW ≤ 4 * ρ / h k := by
  refine ⟨sub_nonneg.2 (gA_mono h k hPW hPWP), ?_⟩
  have hhk : (2 : ℝ) ≤ h k := by exact_mod_cast hk
  rcases hPW.lt_or_eq with hW0 | hW0
  · have h1 := gA_tangent h k (by omega) hW0 (hPW.trans hPWP)
    have h2 := gA_le h k hk (hPW.trans hPWP) hP4
    have h2' : gA h k PW ≤ gA h k P := gA_mono h k hPW hPWP
    have hP0 : 0 < P := hW0.trans_le hPWP
    -- `P - PW ≤ ρ P ≤ 2ρ PW`
    have hd : P - PW ≤ 2 * ρ * PW := by nlinarith
    have h3 : gA h k PW / (h k * PW) * (P - PW) ≤ gA h k PW / (h k * PW) * (2 * ρ * PW) :=
      mul_le_mul_of_nonneg_left hd (div_nonneg (gA_nonneg h k hPW) (by positivity))
    have h4 : gA h k PW / (h k * PW) * (2 * ρ * PW) = 2 * ρ * gA h k PW / h k := by
      field_simp
    have h5 : 2 * ρ * gA h k PW / h k ≤ 4 * ρ / h k := by
      apply div_le_div_of_nonneg_right _ (by linarith)
      have : 2 / (h k : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hhk
      nlinarith
    linarith
  · subst hW0
    have : P ≤ 0 := by nlinarith
    have hP0 : P = 0 := le_antisymm this hPWP
    subst hP0
    have : (0 : ℝ) ≤ 4 * ρ / h k := by positivity
    simp only [sub_self]; exact this

/-- Concavity passes White's advantage from `P` to `g(P)`. -/
theorem gA_advantage (h : ℕ → ℕ) (k : ℕ) (hk : 1 ≤ h k) {P PB PW η : ℝ} (hP : 0 ≤ P)
    (hPB : P ≤ PB) (hPW : 0 ≤ PW) (hη : 0 ≤ η) (hadv : (1 + η) * (PB - P) ≤ P - PW) :
    (1 + η) * (gA h k PB - gA h k P) ≤ gA h k P - gA h k PW := by
  rcases hP.lt_or_eq with hP0 | hP0
  · set a := PB - P with ha
    have h1 := gA_tangent h k hk hP0 (hP.trans hPB)
    have h2 := gA_tangent h k hk hP0 (P' := P - (1 + η) * a) (by nlinarith)
    have h3 : gA h k PW ≤ gA h k (P - (1 + η) * a) := gA_mono h k hPW (by linarith)
    have hs : 0 ≤ gA h k P / (h k * P) := div_nonneg (gA_nonneg h k hP) (by positivity)
    have h4 : (1 + η) * (gA h k PB - gA h k P) ≤ (1 + η) * (gA h k P / (h k * P) * a) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    nlinarith
  · subst hP0
    have : PB - 0 ≤ 0 := by nlinarith
    have hPB0 : PB = 0 := by linarith
    subst hPB0
    have : gA h k PW ≤ gA h k 0 := gA_mono h k hPW (by nlinarith)
    simp only [sub_self, mul_zero]; linarith

/-- The growth bound for a descendant's allowance increment under a White claim:
`g(PW + sW) - g(PW) ≤ e (1+ρ)/(1-ρ) (g(P + s) - g(P))`, for any nonnegative multiplier
`e` satisfying `sW ≤ e*s`, including `e = 0`. Eq. cf-ind-score applies it with `e = exp β`. -/
theorem gA_score_ratio (h : ℕ → ℕ) (k : ℕ) (hk : 1 ≤ h k) {P PW s sW ρ e : ℝ} (hP : 0 ≤ P)
    (hPWP : PW ≤ P) (hPW' : (1 - ρ) * P ≤ PW) (hs : 0 ≤ s) (hsP : s ≤ ρ * P) (hsW : 0 ≤ sW)
    (hsWs : sW ≤ e * s) (he : 0 ≤ e) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    gA h k (PW + sW) - gA h k PW ≤ e * ((1 + ρ) / (1 - ρ)) * (gA h k (P + s) - gA h k P) := by
  rcases hP.lt_or_eq with hP0 | hP0
  · have hPW0 : 0 < PW := lt_of_lt_of_le (by nlinarith) hPW'
    have hps : 0 < P + s := by linarith
    -- upper bound of the numerator by the tangent at `PW`
    have h1 := gA_tangent h k hk hPW0 (P' := PW + sW) (by linarith)
    -- lower bound of the denominator by the tangent at `P + s`
    have h2 := gA_tangent h k hk hps (P' := P) hP
    -- `g(PW)/PW ≤ g(P+s)/(P+s) · (P+s)/PW`
    have hgm : gA h k PW ≤ gA h k (P + s) := gA_mono h k hPW0.le (by linarith)
    have hhk : (0 : ℝ) < h k := by exact_mod_cast (show 0 < h k by omega)
    set c := gA h k (P + s) / (h k * (P + s)) with hc
    have hc0 : 0 ≤ c := div_nonneg (gA_nonneg h k hps.le) (by positivity)
    have hslope : gA h k PW / (h k * PW) ≤ c * ((P + s) / PW) := by
      have : c * ((P + s) / PW) = gA h k (P + s) / (h k * PW) := by
        rw [hc]; field_simp
      rw [this]
      exact div_le_div_of_nonneg_right hgm (by positivity)
    have hratio : (P + s) / PW ≤ (1 + ρ) / (1 - ρ) := by
      rw [div_le_div_iff₀ hPW0 (by linarith)]
      nlinarith
    have hden : c * s ≤ gA h k (P + s) - gA h k P := by
      have : gA h k P - gA h k (P + s) ≤ c * (P - (P + s)) := h2
      nlinarith
    have hnum : gA h k (PW + sW) - gA h k PW ≤ c * ((1 + ρ) / (1 - ρ)) * sW := by
      have h3 : gA h k PW / (h k * PW) * (PW + sW - PW) ≤ c * ((P + s) / PW) * sW := by
        rw [show PW + sW - PW = sW by ring]
        exact mul_le_mul_of_nonneg_right hslope hsW
      have h4 : c * ((P + s) / PW) * sW ≤ c * ((1 + ρ) / (1 - ρ)) * sW :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hc0) hsW
      linarith
    have hr0 : 0 ≤ (1 + ρ) / (1 - ρ) := div_nonneg (by linarith) (by linarith)
    calc gA h k (PW + sW) - gA h k PW ≤ c * ((1 + ρ) / (1 - ρ)) * sW := hnum
      _ ≤ c * ((1 + ρ) / (1 - ρ)) * (e * s) :=
          mul_le_mul_of_nonneg_left hsWs (mul_nonneg hc0 hr0)
      _ = e * ((1 + ρ) / (1 - ρ)) * (c * s) := by ring
      _ ≤ e * ((1 + ρ) / (1 - ρ)) * (gA h k (P + s) - gA h k P) :=
          mul_le_mul_of_nonneg_left hden (mul_nonneg he hr0)
  · subst hP0
    have hs0 : s = 0 := by nlinarith
    subst hs0
    have hsW0 : sW = 0 := by nlinarith
    have hPW0 : PW = 0 := le_antisymm hPWP (by nlinarith)
    subst hsW0; subst hPW0
    simp

theorem exp_sub_one_le_two_mul {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) : Real.exp b - 1 ≤ 2 * b := by
  have := Real.abs_exp_sub_one_sub_id_le (x := b) (by rw [abs_of_nonneg hb]; exact hb1)
  have := (abs_le.1 this).2
  nlinarith

theorem one_sub_exp_neg_ge {w : ℝ} (hw : 0 ≤ w) (hw1 : w ≤ 1) : w - w ^ 2 ≤ 1 - Real.exp (-w) := by
  have := Real.abs_exp_sub_one_sub_id_le (x := -w) (by rw [abs_neg, abs_of_nonneg hw]; exact hw1)
  have := (abs_le.1 this).2
  nlinarith

theorem exp_sub_one_le_mul_exp {x : ℝ} : Real.exp x - 1 ≤ x * Real.exp x := by
  have h1 := Real.add_one_le_exp (-x)
  have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  have h3 := Real.exp_pos x
  nlinarith

/-! #### The move estimates (eq. cf-ind-black – eq. cf-ind-score) -/

/-- Abstract numerical conditions for the induction: the move bound `D_j ≤ ρ_j/8`,
`η'_j = η_j + 16ρ_j`, and the earlier-level inequalities for `η`, `η'` and `β`,
together with their sign bounds. No predecessor equality is imposed. The separate `σ` slack
bounds of eq. cf-slack-bounds are established by `cf_sigma`. -/
structure QParams (lam : ℕ → ℝ) (μ : ℝ) (h : ℕ → ℕ) (γ ρ η η' β : ℕ → ℝ) : Prop where
  lam_pos : ∀ k, 0 < lam k
  μ0 : 0 ≤ μ
  μ1 : μ ≤ 1
  h2 : ∀ k, 2 ≤ h k
  γ0 : ∀ k, 0 ≤ γ k
  ρ0 : ∀ k, 0 ≤ ρ k
  ρ1 : ∀ k, ρ k ≤ 1 / 4
  D : ∀ j, lam j * (1 + μ + 4 * ∑ k ∈ Finset.range j, γ k * ρ k / h k) ≤ ρ j / 8
  η_step : ∀ j, η' j = η j + 16 * ρ j
  η0 : ∀ j, 0 ≤ η j
  η'μ : ∀ j, η' j ≤ μ
  η_mono : ∀ k j, k < j → η' j ≤ η k
  β_step : ∀ k j, k < j → β k + 3 * ρ k ≤ β j - 4 * ρ j
  β0 : ∀ j, 4 * ρ j ≤ β j
  β1 : ∀ j, β j ≤ 1 / 2

theorem exp_half_le_two : Real.exp (1 / 2) ≤ 2 := by
  have h1 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h2 := Real.exp_one_lt_d9
  have h3 := Real.exp_pos (1 / 2)
  nlinarith

/-- The per-requirement inequalities behind (eq. cf-ind-black), (eq. cf-ind-white) and
(eq. cf-ind-advantage). -/
theorem weight_ineqs {E0 EB EW b w D ρ η η' : ℝ} (hb : EB = E0 + b) (hw : EW = E0 - w)
    (hb0 : 0 ≤ b) (hbD : b ≤ D) (hw0 : 0 ≤ w) (hwD : w ≤ D) (hD : D ≤ ρ / 8)
    (hadv : (1 + η') * b ≤ w) (hη : η' = η + 16 * ρ) (hη0 : 0 ≤ η) (hη1 : η' ≤ 1) :
    Real.exp EB - Real.exp E0 ≤ ρ * Real.exp E0 ∧ Real.exp E0 - Real.exp EW ≤ ρ * Real.exp E0 ∧
      (1 + η) * (Real.exp EB - Real.exp E0) ≤ Real.exp E0 - Real.exp EW := by
  have hE := Real.exp_pos E0
  have hρ0 : 0 ≤ ρ := by linarith
  have hb1 : b ≤ 1 := by linarith
  have hw1 : w ≤ 1 := by linarith
  have eB : Real.exp EB - Real.exp E0 = Real.exp E0 * (Real.exp b - 1) := by
    rw [hb, Real.exp_add]; ring
  have eW : Real.exp E0 - Real.exp EW = Real.exp E0 * (1 - Real.exp (-w)) := by
    rw [hw, show E0 - w = E0 + -w by ring, Real.exp_add]; ring
  have k1 := exp_sub_one_le_two_mul hb0 hb1
  have k2 : 1 - Real.exp (-w) ≤ w := by linarith [Real.add_one_le_exp (-w)]
  have k3 := one_sub_exp_neg_ge hw0 hw1
  have k4 : Real.exp b - 1 ≤ b + b ^ 2 := by
    have := Real.abs_exp_sub_one_sub_id_le (x := b) (by rw [abs_of_nonneg hb0]; exact hb1)
    linarith [(abs_le.1 this).2]
  refine ⟨?_, ?_, ?_⟩
  · rw [eB]
    have : Real.exp b - 1 ≤ ρ := by linarith
    nlinarith
  · rw [eW]
    have : 1 - Real.exp (-w) ≤ ρ := by linarith
    nlinarith
  · rw [eB, eW]
    -- `(1+η)(e^b - 1) ≤ (1+η)(1+D) b ≤ (1+η')(1-D) b ≤ (1-D) w ≤ 1 - e^{-w}`
    have h1 : (1 + η) * (Real.exp b - 1) ≤ (1 + η) * ((1 + D) * b) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith); nlinarith
    have h2 : (1 + η) * ((1 + D) * b) ≤ (1 - D) * ((1 + η') * b) := by
      have : (1 + η) * (1 + D) ≤ (1 - D) * (1 + η') := by
        rw [hη]; nlinarith
      nlinarith
    have h3 : (1 - D) * ((1 + η') * b) ≤ (1 - D) * w :=
      mul_le_mul_of_nonneg_left hadv (by linarith)
    have h4 : (1 - D) * w ≤ 1 - Real.exp (-w) := by nlinarith
    have := h1.trans (h2.trans (h3.trans h4))
    nlinarith

/-- The per-requirement inequality behind (eq. cf-ind-score). -/
theorem weight_score {E0 EB EWy EWyB b bt G β ρ D : ℝ} (hb : EB = E0 + b) (hbt : EWyB = EWy + bt)
    (hEW : EWy ≤ E0) (hb0 : 0 ≤ b) (hbD : b ≤ D) (hD : D ≤ ρ / 8) (hbt0 : 0 ≤ bt)
    (hbtG : bt ≤ G * b) (hG : G = Real.exp (β - 4 * ρ)) (hG2 : G ≤ 2) :
    Real.exp EWyB - Real.exp EWy ≤ Real.exp β * (Real.exp EB - Real.exp E0) := by
  have hE0 := Real.exp_pos E0
  have eB : Real.exp EB - Real.exp E0 = Real.exp E0 * (Real.exp b - 1) := by
    rw [hb, Real.exp_add]; ring
  have eW : Real.exp EWyB - Real.exp EWy = Real.exp EWy * (Real.exp bt - 1) := by
    rw [hbt, Real.exp_add]; ring
  rw [eB, eW]
  have hG0 : 0 < G := hG ▸ Real.exp_pos _
  have hGb0 : 0 ≤ G * b := mul_nonneg hG0.le hb0
  -- `e^{bt} - 1 ≤ e^{Gb} - 1 ≤ G b e^{Gb} ≤ e^β b ≤ e^β (e^b - 1)`
  have k1 : Real.exp bt - 1 ≤ Real.exp (G * b) - 1 := by
    have := Real.exp_le_exp.2 hbtG; linarith
  have k2 := exp_sub_one_le_mul_exp (x := G * b)
  have k3 : G * Real.exp (G * b) ≤ Real.exp β := by
    have hρ' : G * b ≤ 4 * ρ := by nlinarith
    calc G * Real.exp (G * b) = Real.exp (β - 4 * ρ + G * b) := by rw [Real.exp_add, ← hG]
      _ ≤ Real.exp β := Real.exp_le_exp.2 (by linarith)
  have k4 : b ≤ Real.exp b - 1 := by linarith [Real.add_one_le_exp b]
  have k5 : Real.exp bt - 1 ≤ Real.exp β * (Real.exp b - 1) := by
    calc Real.exp bt - 1 ≤ G * b * Real.exp (G * b) := k1.trans k2
      _ = G * Real.exp (G * b) * b := by ring
      _ ≤ Real.exp β * b := mul_le_mul_of_nonneg_right k3 hb0
      _ ≤ Real.exp β * (Real.exp b - 1) := mul_le_mul_of_nonneg_left k4 (Real.exp_pos _).le
  have k6 : 0 ≤ Real.exp bt - 1 := by linarith [Real.add_one_le_exp bt]
  have k7 : Real.exp EWy ≤ Real.exp E0 := Real.exp_le_exp.2 hEW
  calc Real.exp EWy * (Real.exp bt - 1) ≤ Real.exp E0 * (Real.exp bt - 1) :=
        mul_le_mul_of_nonneg_right k7 k6
    _ ≤ Real.exp E0 * (Real.exp β * (Real.exp b - 1)) :=
        mul_le_mul_of_nonneg_left k5 hE0.le
    _ = Real.exp β * (Real.exp E0 * (Real.exp b - 1)) := by ring


/-- The per-requirement algebra of the induction step, with the descendant sums abstracted:
(eq. cf-ind-black), (eq. cf-ind-white), (eq. cf-ind-advantage). -/
theorem per_req_main {E0 EB EW ind SB SW lamj μ S4 ρ η η' : ℝ}
    (hlam : 0 < lamj) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hind0 : 0 ≤ ind) (hind1 : ind ≤ 1)
    (hSB0 : 0 ≤ SB) (hSB : SB ≤ 2 * S4) (hSW0 : 0 ≤ SW) (hSW : SW ≤ 4 * S4)
    (hadvS : (1 + η') * SB ≤ SW) (hD : lamj * (1 + μ + 4 * S4) ≤ ρ / 8)
    (hη : η' = η + 16 * ρ) (hη0 : 0 ≤ η) (hη'μ : η' ≤ μ)
    (eB : EB - E0 = lamj * ((1 - μ) * ind + SB))
    (eW : E0 - EW = lamj * (2 * ind - (1 - μ) * ind + SW)) :
    Real.exp EB - Real.exp E0 ≤ ρ * Real.exp E0 ∧ Real.exp E0 - Real.exp EW ≤ ρ * Real.exp E0 ∧
      (1 + η) * (Real.exp EB - Real.exp E0) ≤ Real.exp E0 - Real.exp EW := by
  set b := lamj * ((1 - μ) * ind + SB) with hb
  set w := lamj * (2 * ind - (1 - μ) * ind + SW) with hw
  set D := lamj * (1 + μ + 4 * S4) with hDdef
  have hb0 : 0 ≤ b := mul_nonneg hlam.le (by nlinarith)
  have hw0 : 0 ≤ w := mul_nonneg hlam.le (by nlinarith)
  have hbD : b ≤ D := mul_le_mul_of_nonneg_left (by nlinarith) hlam.le
  have hwD : w ≤ D := mul_le_mul_of_nonneg_left (by nlinarith) hlam.le
  have hη'0 : 0 ≤ η' := by rw [hη]; nlinarith
  have k : (1 + η') * (1 - μ) ≤ 1 + μ := by nlinarith
  have k2 : (1 + η') * ((1 - μ) * ind) ≤ 2 * ind - (1 - μ) * ind := by
    have := mul_le_mul_of_nonneg_right k hind0
    nlinarith
  have hadv : (1 + η') * b ≤ w := by
    have : (1 + η') * ((1 - μ) * ind + SB) ≤ 2 * ind - (1 - μ) * ind + SW := by nlinarith
    have := mul_le_mul_of_nonneg_left this hlam.le
    rw [hb, hw]; nlinarith
  exact weight_ineqs (by linarith) (by linarith) hb0 hbD hw0 hwD hD hadv hη hη0
    (hη'μ.trans hμ1)

/-- The per-requirement algebra of (eq. cf-ind-score). -/
theorem per_req_score {E0 EB EWy EWyB ind SB SBt lamj μ S4 ρ β : ℝ}
    (hlam : 0 < lamj) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hind0 : 0 ≤ ind) (hind1 : ind ≤ 1)
    (hSB0 : 0 ≤ SB) (hSB : SB ≤ 2 * S4) (hSBt0 : 0 ≤ SBt)
    (hSBt : SBt ≤ Real.exp (β - 4 * ρ) * SB) (hD : lamj * (1 + μ + 4 * S4) ≤ ρ / 8)
    (hβ0 : 4 * ρ ≤ β) (hβ1 : β ≤ 1 / 2) (hρ0 : 0 ≤ ρ)
    (eB : EB - E0 = lamj * ((1 - μ) * ind + SB))
    (eWy : EWyB - EWy = lamj * ((1 - μ) * ind + SBt)) (hEW : EWy ≤ E0) :
    Real.exp EWyB - Real.exp EWy ≤ Real.exp β * (Real.exp EB - Real.exp E0) := by
  set G := Real.exp (β - 4 * ρ) with hG
  set b := lamj * ((1 - μ) * ind + SB) with hb
  set D := lamj * (1 + μ + 4 * S4) with hDdef
  have hG1 : 1 ≤ G := Real.one_le_exp (by linarith)
  have hG2 : G ≤ 2 := (Real.exp_le_exp.2 (by linarith)).trans exp_half_le_two
  have hb0 : 0 ≤ b := mul_nonneg hlam.le (by nlinarith)
  have hmi : (1 - μ) * ind ≤ 1 := by nlinarith
  have hbD : b ≤ D := mul_le_mul_of_nonneg_left (by nlinarith) hlam.le
  have hbt0 : 0 ≤ lamj * ((1 - μ) * ind + SBt) := mul_nonneg hlam.le (by nlinarith)
  have hbtG : lamj * ((1 - μ) * ind + SBt) ≤ G * b := by
    have := mul_nonneg (sub_nonneg.2 hG1) (mul_nonneg (sub_nonneg.2 hμ1) hind0)
    have : (1 - μ) * ind + SBt ≤ G * ((1 - μ) * ind + SB) := by nlinarith
    have := mul_le_mul_of_nonneg_left this hlam.le
    rw [hb]; nlinarith
  exact weight_score (by linarith) (by linarith) hEW hb0 hbD hD hbt0 hbtG hG hG2

theorem mul_adv {m a c η' η : ℝ} (hm : 0 ≤ m) (ha : 0 ≤ a) (hη : η' ≤ η)
    (h : (1 + η) * a ≤ c) : (1 + η') * (m * a) ≤ m * c := by
  have : (1 + η') * a ≤ c := (mul_le_mul_of_nonneg_right (by linarith) ha).trans h
  nlinarith

theorem mul_ratio {m a c e G : ℝ} (hm : 0 ≤ m) (ha : 0 ≤ a) (heG : e ≤ G)
    (h : c ≤ e * a) : m * c ≤ G * (m * a) := by
  have : c ≤ G * a := h.trans (mul_le_mul_of_nonneg_right heG ha)
  nlinarith

/-- A sum over the monitored descendants of terms vanishing off the descendants containing `x`
is bounded by a sum over the lower levels: a point lies in at most one vertex of each level. -/
theorem sum_Dset_le (hT : T.WellFormed) (ℓ : T.V → ℕ)
    (hℓ : ∀ a b : T.V, T.StrictAnc a b → ℓ b < ℓ a) (s : T.State) (v : T.V) (x : Pt d)
    (f : T.V → ℝ) (F : ℕ → ℝ) (hF : ∀ k, 0 ≤ F k) (hfz : ∀ u ∈ Dset s v, x ∉ T.E u → f u = 0)
    (hfb : ∀ u ∈ Dset s v, f u ≤ F (ℓ u)) :
    ∑ u ∈ Dset s v, f u ≤ ∑ k ∈ Finset.range (ℓ v), F k := by
  set S := (Dset s v).filter fun u => x ∈ T.E u with hS
  have h1 : ∑ u ∈ Dset s v, f u = ∑ u ∈ S, f u := by
    rw [hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun u hu => ?_
    split_ifs with hx
    · rfl
    · exact hfz u hu hx
  have hinj : Set.InjOn ℓ S := by
    intro a ha b hb hab
    have ha' := Finset.mem_filter.1 ha
    have hb' := Finset.mem_filter.1 hb
    by_contra hne
    rcases comparable hT a b ha'.2 hb'.2 with h1 | h1
    · have := hℓ a b ⟨h1, hne⟩; omega
    · have := hℓ b a ⟨h1, fun h => hne h.symm⟩; omega
  rw [h1]
  calc ∑ u ∈ S, f u ≤ ∑ u ∈ S, F (ℓ u) := Finset.sum_le_sum fun u hu =>
        hfb u (Finset.mem_filter.1 hu).1
    _ = ∑ k ∈ S.image ℓ, F k := (Finset.sum_image hinj).symm
    _ ≤ ∑ k ∈ Finset.range (ℓ v), F k := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) fun k _ _ => hF k
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hk
        exact Finset.mem_range.2 (hℓ v u (mem_Dset.1 (Finset.mem_filter.1 hu).1).1)

section Quantitative
variable (ℓ : T.V → ℕ) (lam : ℕ → ℝ) (μ : ℝ) (h : ℕ → ℕ)
  (hT : T.WellFormed) (hℓ : ∀ a b : T.V, T.StrictAnc a b → ℓ b < ℓ a)
  {γ ρ η η' β : ℕ → ℝ} (hQ : QParams lam μ h γ ρ η η' β)
  (hlight : ∀ v, ∀ Q ∈ T.reqs v, ∀ u, T.StrictAnc v u → (mQ T Q u : ℝ) ≤ γ (ℓ u))

include hT hℓ hQ hlight

omit hT hlight in
/-- The exponent decreases under any White claim (termwise form of `pot_white_mono`). -/
theorem expo_white_le (s : T.State) (y : Pt d) (v : T.V) (Q : Finset (Pt d)) (hQv : Q ∈ T.reqs v) :
    expo ℓ lam μ h (fun u => pot ℓ lam μ h u (T.whiteClaim s y)) (T.whiteClaim s y) v Q ≤
      expo ℓ lam μ h (fun u => pot ℓ lam μ h u s) s v Q := by
  have := expo_white ℓ lam μ h (fun u => pot ℓ lam μ h u s)
    (fun u => pot ℓ lam μ h u (T.whiteClaim s y)) s y v Q hQv
  have hc : (0 : ℝ) ≤ 2 * (if y ∈ Q ∧ y ∈ T.eff s v then 1 else 0) -
      (1 - μ) * (if y ∈ Q ∧ y ∈ T.eff s v ∧ T.Unused s y then 1 else 0) := by
    have := hQ.μ0; have := hQ.μ1
    by_cases h1 : y ∈ Q ∧ y ∈ T.eff s v
    · rw [if_pos h1]; split_ifs <;> linarith
    · rw [if_neg h1, if_neg fun h2 => h1 ⟨h2.1, h2.2.1⟩]; norm_num
  have h1 : 0 ≤ lam (ℓ v) * (2 * (if y ∈ Q ∧ y ∈ T.eff s v then 1 else 0) -
      (1 - μ) * (if y ∈ Q ∧ y ∈ T.eff s v ∧ T.Unused s y then 1 else 0) +
      ∑ u ∈ Dset s v, (mQ T Q u : ℝ) * (gA h (ℓ u) (pot ℓ lam μ h u s) -
        gA h (ℓ u) (pot ℓ lam μ h u (T.whiteClaim s y)))) := by
    refine mul_nonneg (hQ.lam_pos _).le (add_nonneg hc
      (Finset.sum_nonneg fun u hu => mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.2 ?_)))
    exact gA_mono h _ (pot_nonneg ℓ lam μ h hℓ u _)
      (pot_white_mono ℓ lam μ h hℓ (fun k => (hQ.lam_pos k).le) hQ.μ0 u s y)
  linarith

/-- Upper bounds for the Black increment and White decrement, the White advantage, and the
score-growth bound (eq. cf-ind-black, cf-ind-white, cf-ind-advantage, cf-ind-score), proved by
induction on the level when every potential in the subtree of `v` is at most `1/4`.
The nonnegativity bounds are supplied separately by `pot_black_mono` and `pot_white_mono`. -/
theorem pot_quant : ∀ (v : T.V) (s : T.State), (∀ u, T.Anc v u → pot ℓ lam μ h u s ≤ 1 / 4) →
    ∀ x y, T.Unused s x → T.Unused s y →
      pot ℓ lam μ h v (T.blackClaim s x) - pot ℓ lam μ h v s ≤ ρ (ℓ v) * pot ℓ lam μ h v s ∧
      pot ℓ lam μ h v s - pot ℓ lam μ h v (T.whiteClaim s x) ≤ ρ (ℓ v) * pot ℓ lam μ h v s ∧
      (1 + η (ℓ v)) * (pot ℓ lam μ h v (T.blackClaim s x) - pot ℓ lam μ h v s) ≤
        pot ℓ lam μ h v s - pot ℓ lam μ h v (T.whiteClaim s x) ∧
      (x ≠ y → pot ℓ lam μ h v (T.blackClaim (T.whiteClaim s y) x) -
          pot ℓ lam μ h v (T.whiteClaim s y) ≤
        Real.exp (β (ℓ v)) * (pot ℓ lam μ h v (T.blackClaim s x) - pot ℓ lam μ h v s)) := by
  have hlam0 : ∀ k, 0 ≤ lam k := fun k => (hQ.lam_pos k).le
  have hμ0 := hQ.μ0
  have hμ1 := hQ.μ1
  intro v
  induction hn : ℓ v using Nat.strong_induction_on generalizing v with
  | _ j ih =>
    intro s hsb x y hx hy
    -- notation for the potentials of the monitored descendants
    set P : T.V → ℝ := fun u => pot ℓ lam μ h u s with hP
    set PB : T.V → ℝ := fun u => pot ℓ lam μ h u (T.blackClaim s x) with hPB
    set PW : T.V → ℝ := fun u => pot ℓ lam μ h u (T.whiteClaim s x) with hPW
    set PWy : T.V → ℝ := fun u => pot ℓ lam μ h u (T.whiteClaim s y) with hPWy
    set PWyB : T.V → ℝ := fun u => pot ℓ lam μ h u (T.blackClaim (T.whiteClaim s y) x)
      with hPWyB
    set S4 := ∑ k ∈ Finset.range j, γ k * ρ k / h k with hS4
    set Dj := lam j * (1 + μ + 4 * S4) with hDj
    have hDjρ : Dj ≤ ρ j / 8 := hQ.D j
    have hρj := hQ.ρ1 j
    have hρj0 := hQ.ρ0 j
    have hS40 : 0 ≤ S4 := Finset.sum_nonneg fun k _ =>
      div_nonneg (mul_nonneg (hQ.γ0 k) (hQ.ρ0 k)) (by have := hQ.h2 k; positivity)
    -- per-descendant facts
    have hdesc : ∀ u ∈ Dset s v,
        (0 ≤ gA h (ℓ u) (PB u) - gA h (ℓ u) (P u) ∧
          gA h (ℓ u) (PB u) - gA h (ℓ u) (P u) ≤ 2 * ρ (ℓ u) / h (ℓ u)) ∧
        (0 ≤ gA h (ℓ u) (P u) - gA h (ℓ u) (PW u) ∧
          gA h (ℓ u) (P u) - gA h (ℓ u) (PW u) ≤ 4 * ρ (ℓ u) / h (ℓ u)) ∧
        (1 + η (ℓ u)) * (gA h (ℓ u) (PB u) - gA h (ℓ u) (P u)) ≤
          gA h (ℓ u) (P u) - gA h (ℓ u) (PW u) ∧
        (x ≠ y → gA h (ℓ u) (PWyB u) - gA h (ℓ u) (PWy u) ≤
          Real.exp (β (ℓ u) + 3 * ρ (ℓ u)) * (gA h (ℓ u) (PB u) - gA h (ℓ u) (P u))) ∧
        (x ∉ T.E u → gA h (ℓ u) (PB u) - gA h (ℓ u) (P u) = 0 ∧
          gA h (ℓ u) (P u) - gA h (ℓ u) (PW u) = 0) := by
      intro u hu
      have hvu := (mem_Dset.1 hu).1
      have hlt : ℓ u < j := hn ▸ hℓ v u hvu
      have hsbu : ∀ w, T.Anc u w → pot ℓ lam μ h w s ≤ 1 / 4 := fun w hw =>
        hsb w (anc_trans hvu.1 hw)
      obtain ⟨a1, -, a3, a4⟩ := ih (ℓ u) hlt u rfl s hsbu x y hx hy
      obtain ⟨-, a2y, -, -⟩ := ih (ℓ u) hlt u rfl s hsbu y x hy hx
      obtain ⟨-, a2, -, -⟩ := ih (ℓ u) hlt u rfl s hsbu x y hx hy
      have hPu0 : 0 ≤ P u := pot_nonneg ℓ lam μ h hℓ u s
      have hPu4 : P u ≤ 1 / 4 := hsbu u (RegionTree.Anc.refl _)
      have hBm : P u ≤ PB u := pot_black_mono ℓ lam μ h hℓ hlam0 hμ1 u s x
      have hWm : PW u ≤ P u := pot_white_mono ℓ lam μ h hℓ hlam0 hμ0 u s x
      have hWym : PWy u ≤ P u := pot_white_mono ℓ lam μ h hℓ hlam0 hμ0 u s y
      have hWyBm : PWy u ≤ PWyB u :=
        pot_black_mono ℓ lam μ h hℓ hlam0 hμ1 u (T.whiteClaim s y) x
      have hPW0 : 0 ≤ PW u := pot_nonneg ℓ lam μ h hℓ u _
      have hk2 := hQ.h2 (ℓ u)
      have hρu := hQ.ρ1 (ℓ u)
      have hρu0 := hQ.ρ0 (ℓ u)
      refine ⟨gA_black_incr h _ hk2 hPu0 hPu4 hBm (by simpa using a1) hρu0,
        gA_white_decr h _ hk2 hPu4 hPW0 hWm (by simp only [hP, hPW] at a2 ⊢; nlinarith)
          hρu0 (by linarith),
        gA_advantage h _ (by omega) hPu0 hBm hPW0 (hQ.η0 _) a3, fun hxy => ?_, fun hxE => ?_⟩
      · -- the score ratio at `u`
        have h1 := gA_score_ratio h (ℓ u) (by omega) (P := P u) (PW := PWy u)
          (s := PB u - P u) (sW := PWyB u - PWy u) (ρ := ρ (ℓ u)) (e := Real.exp (β (ℓ u)))
          hPu0 hWym (by simp only [hP, hPWy] at a2y ⊢; nlinarith) (by linarith) a1
          (by linarith) (a4 hxy) (Real.exp_pos _).le hρu0 (by linarith)
        rw [show PWy u + (PWyB u - PWy u) = PWyB u by ring,
          show P u + (PB u - P u) = PB u by ring] at h1
        have hr : (1 + ρ (ℓ u)) / (1 - ρ (ℓ u)) ≤ Real.exp (3 * ρ (ℓ u)) := by
          rw [div_le_iff₀ (by linarith)]
          have := Real.add_one_le_exp (3 * ρ (ℓ u))
          nlinarith
        have h2 : Real.exp (β (ℓ u)) * ((1 + ρ (ℓ u)) / (1 - ρ (ℓ u))) ≤
            Real.exp (β (ℓ u) + 3 * ρ (ℓ u)) := by
          rw [Real.exp_add]; exact mul_le_mul_of_nonneg_left hr (Real.exp_pos _).le
        have h3 : 0 ≤ gA h (ℓ u) (PB u) - gA h (ℓ u) (P u) := sub_nonneg.2 (gA_mono h _ hPu0 hBm)
        nlinarith
      · have hxe : x ∉ T.eff s u := fun h1 => hxE (mem_eff.1 h1).1
        have e1 : PB u = P u := pot_black_loc ℓ lam μ h hT hℓ u s x hxe
        have e2 : PW u = P u := pot_white_loc ℓ lam μ h hT hℓ u s x hxe
        rw [e1, e2]; simp
    -- the sums over the monitored descendants
    have hsumB : ∀ Q ∈ T.reqs v, ∑ u ∈ Dset s v, (mQ T Q u : ℝ) *
        (gA h (ℓ u) (PB u) - gA h (ℓ u) (P u)) ≤ 2 * S4 := by
      intro Q hQv
      rw [hS4, Finset.mul_sum, ← hn]
      refine sum_Dset_le hT ℓ hℓ s v x _ _ (fun k => by
        have := hQ.h2 k; have := hQ.γ0 k; have := hQ.ρ0 k; positivity) (fun u hu hxE => by
          rw [((hdesc u hu).2.2.2.2 hxE).1, mul_zero]) fun u hu => ?_
      have hm := hlight v Q hQv u (mem_Dset.1 hu).1
      obtain ⟨⟨d0, d1⟩, -⟩ := hdesc u hu
      have : (mQ T Q u : ℝ) * (gA h (ℓ u) (PB u) - gA h (ℓ u) (P u)) ≤
          γ (ℓ u) * (2 * ρ (ℓ u) / h (ℓ u)) :=
        mul_le_mul hm d1 d0 (hQ.γ0 _)
      calc _ ≤ γ (ℓ u) * (2 * ρ (ℓ u) / h (ℓ u)) := this
        _ = 2 * (γ (ℓ u) * ρ (ℓ u) / h (ℓ u)) := by ring
    have hsumW : ∀ Q ∈ T.reqs v, ∑ u ∈ Dset s v, (mQ T Q u : ℝ) *
        (gA h (ℓ u) (P u) - gA h (ℓ u) (PW u)) ≤ 4 * S4 := by
      intro Q hQv
      rw [hS4, Finset.mul_sum, ← hn]
      refine sum_Dset_le hT ℓ hℓ s v x _ _ (fun k => by
        have := hQ.h2 k; have := hQ.γ0 k; have := hQ.ρ0 k; positivity) (fun u hu hxE => by
          rw [((hdesc u hu).2.2.2.2 hxE).2, mul_zero]) fun u hu => ?_
      have hm := hlight v Q hQv u (mem_Dset.1 hu).1
      obtain ⟨-, ⟨d0, d1⟩, -⟩ := hdesc u hu
      have : (mQ T Q u : ℝ) * (gA h (ℓ u) (P u) - gA h (ℓ u) (PW u)) ≤
          γ (ℓ u) * (4 * ρ (ℓ u) / h (ℓ u)) :=
        mul_le_mul hm d1 d0 (hQ.γ0 _)
      calc _ ≤ γ (ℓ u) * (4 * ρ (ℓ u) / h (ℓ u)) := this
        _ = 4 * (γ (ℓ u) * ρ (ℓ u) / h (ℓ u)) := by ring
    -- per-requirement estimates
    have hper : ∀ Q ∈ T.reqs v,
        (Real.exp (expo ℓ lam μ h PB (T.blackClaim s x) v Q) -
            Real.exp (expo ℓ lam μ h P s v Q) ≤ ρ j * Real.exp (expo ℓ lam μ h P s v Q) ∧
          Real.exp (expo ℓ lam μ h P s v Q) -
            Real.exp (expo ℓ lam μ h PW (T.whiteClaim s x) v Q) ≤
              ρ j * Real.exp (expo ℓ lam μ h P s v Q) ∧
          (1 + η j) * (Real.exp (expo ℓ lam μ h PB (T.blackClaim s x) v Q) -
            Real.exp (expo ℓ lam μ h P s v Q)) ≤
            Real.exp (expo ℓ lam μ h P s v Q) -
              Real.exp (expo ℓ lam μ h PW (T.whiteClaim s x) v Q)) ∧
        (x ≠ y → Real.exp (expo ℓ lam μ h PWyB (T.blackClaim (T.whiteClaim s y) x) v Q) -
            Real.exp (expo ℓ lam μ h PWy (T.whiteClaim s y) v Q) ≤
          Real.exp (β j) * (Real.exp (expo ℓ lam μ h PB (T.blackClaim s x) v Q) -
            Real.exp (expo ℓ lam μ h P s v Q))) := by
      intro Q hQv
      set ind : ℝ := if x ∈ Q ∧ x ∈ T.eff s v ∧ T.Unused s x then 1 else 0 with hind
      have hind0 : 0 ≤ ind := by rw [hind]; split_ifs <;> norm_num
      have hind1 : ind ≤ 1 := by rw [hind]; split_ifs <;> norm_num
      have hcr : (if x ∈ Q ∧ x ∈ T.eff s v then (1 : ℝ) else 0) = ind := by
        rw [hind]
        by_cases h1 : x ∈ Q ∧ x ∈ T.eff s v
        · rw [if_pos h1, if_pos ⟨h1.1, h1.2, hx⟩]
        · rw [if_neg h1, if_neg fun h2 => h1 ⟨h2.1, h2.2.1⟩]
      have hSB0 : 0 ≤ ∑ u ∈ Dset s v, (mQ T Q u : ℝ) * (gA h (ℓ u) (PB u) - gA h (ℓ u) (P u)) :=
        Finset.sum_nonneg fun u hu => mul_nonneg (Nat.cast_nonneg _) (hdesc u hu).1.1
      have hSW0 : 0 ≤ ∑ u ∈ Dset s v, (mQ T Q u : ℝ) * (gA h (ℓ u) (P u) - gA h (ℓ u) (PW u)) :=
        Finset.sum_nonneg fun u hu => mul_nonneg (Nat.cast_nonneg _) (hdesc u hu).2.1.1
      have hadvS : (1 + η' j) * ∑ u ∈ Dset s v, (mQ T Q u : ℝ) *
          (gA h (ℓ u) (PB u) - gA h (ℓ u) (P u)) ≤
          ∑ u ∈ Dset s v, (mQ T Q u : ℝ) * (gA h (ℓ u) (P u) - gA h (ℓ u) (PW u)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun u hu => ?_
        obtain ⟨⟨d0, -⟩, -, d3, -⟩ := hdesc u hu
        exact mul_adv (Nat.cast_nonneg _) d0
          (hQ.η_mono (ℓ u) j (hn ▸ hℓ v u (mem_Dset.1 hu).1)) d3
      have hb := expo_black ℓ lam μ h P PB s x v Q
      have hw := expo_white ℓ lam μ h P PW s x v Q hQv
      rw [← hind, hn] at hb
      rw [hcr, ← hind, hn] at hw
      have hlamj := hQ.lam_pos j
      refine ⟨per_req_main hlamj hμ0 hμ1 hind0 hind1 hSB0 (hsumB Q hQv) hSW0 (hsumW Q hQv)
        hadvS hDjρ (hQ.η_step j) (hQ.η0 j) (hQ.η'μ j) hb hw, fun hxy => ?_⟩
      -- the score after White's claim at `y`
      have hbt := expo_black ℓ lam μ h PWy PWyB (T.whiteClaim s y) x v Q
      have hind' : (if x ∈ Q ∧ x ∈ T.eff (T.whiteClaim s y) v ∧ T.Unused (T.whiteClaim s y) x
          then (1 : ℝ) else 0) = ind := by
        rw [hind]
        have : T.eff (T.whiteClaim s y) v = T.eff s v := rfl
        rw [this, unused_white]
        simp only [ne_eq, hxy, not_false_eq_true, and_true]
      have hDy : Dset (T.whiteClaim s y) v = Dset s v := Dset_congr rfl v
      rw [hind', hDy, hn] at hbt
      have hSBt0 : 0 ≤ ∑ u ∈ Dset s v,
          (mQ T Q u : ℝ) * (gA h (ℓ u) (PWyB u) - gA h (ℓ u) (PWy u)) :=
        Finset.sum_nonneg fun u _ => mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.2
          (gA_mono h _ (pot_nonneg ℓ lam μ h hℓ u _)
            (pot_black_mono ℓ lam μ h hℓ hlam0 hμ1 u (T.whiteClaim s y) x)))
      have hSBt : ∑ u ∈ Dset s v, (mQ T Q u : ℝ) * (gA h (ℓ u) (PWyB u) - gA h (ℓ u) (PWy u)) ≤
          Real.exp (β j - 4 * ρ j) *
            ∑ u ∈ Dset s v, (mQ T Q u : ℝ) * (gA h (ℓ u) (PB u) - gA h (ℓ u) (P u)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun u hu => ?_
        obtain ⟨⟨d0, -⟩, -, -, d4, -⟩ := hdesc u hu
        exact mul_ratio (Nat.cast_nonneg _) d0
          (Real.exp_le_exp.2 (hQ.β_step (ℓ u) j (hn ▸ hℓ v u (mem_Dset.1 hu).1))) (d4 hxy)
      have hEW := expo_white_le ℓ lam μ h hℓ hQ s y v Q hQv
      exact per_req_score hlamj hμ0 hμ1 hind0 hind1 hSB0 (hsumB Q hQv) hSBt0 hSBt hDjρ
        (hQ.β0 j) (hQ.β1 j) (hQ.ρ0 j) hb hbt hEW
    -- summing over the requirements
    rw [pot_eq ℓ lam μ h hℓ v (T.blackClaim s x), pot_eq ℓ lam μ h hℓ v s,
      pot_eq ℓ lam μ h hℓ v (T.whiteClaim s x), pot_eq ℓ lam μ h hℓ v (T.whiteClaim s y),
      pot_eq ℓ lam μ h hℓ v (T.blackClaim (T.whiteClaim s y) x)]
    unfold potF
    simp only [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine ⟨Finset.sum_le_sum fun Q hQv => (hper Q hQv).1.1,
      Finset.sum_le_sum fun Q hQv => (hper Q hQv).1.2.1,
      Finset.sum_le_sum fun Q hQv => (hper Q hQv).1.2.2,
      fun hxy => Finset.sum_le_sum fun Q hQv => (hper Q hQv).2 hxy⟩

end Quantitative

/-! #### Small initial potentials (eq. cf-initial-induction) -/

/-- `∑_{k < n+1} 1/(k+1)² ≤ 5/3 - 2/(2n+3)`; in particular every partial sum is at most `5/3`. -/
theorem sum_inv_sq_le' (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), 1 / ((k : ℝ) + 1) ^ 2 ≤ 5 / 3 - (2 : ℝ) / (2 * (n : ℝ) + 3) := by
  induction n with
  | zero => norm_num [Finset.sum_range_one]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 : 1 / (((n + 1 : ℕ) : ℝ) + 1) ^ 2 ≤ 2 / (2 * (n : ℝ) + 3) - 2 / (2 * ((n + 1 : ℕ) : ℝ) + 3) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    push_cast at h1 ih ⊢
    linarith

theorem sum_inv_sq_le (n : ℕ) : ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1) ^ 2 ≤ 5 / 3 := by
  rcases n with _ | n
  · norm_num
  · exact (sum_inv_sq_le' n).trans (by
      have : (0 : ℝ) ≤ (2 : ℝ) / (2 * (n : ℝ) + 3) := by positivity
      linarith)

theorem eff_init (hT : T.WellFormed) (v : T.V) : T.eff T.init v = T.E v := by
  ext x
  rw [mem_eff]
  refine ⟨fun h => h.1, fun h => ⟨h, fun u hu hvu => ?_⟩⟩
  have hu' : u = T.root := Finset.mem_singleton.1 hu
  subst hu'
  have := strictAnc_depth hT hvu
  rw [hT.2.1] at this
  omega

theorem two_log_le (j : ℕ) : 2 * Real.log ((j : ℝ) + 1) ≤ (j : ℝ) + 1 := by
  have hx : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have h1 := Real.quadratic_le_exp_of_nonneg (x := ((j : ℝ) + 1) / 2) (by positivity)
  have h2 : (j : ℝ) + 1 ≤ Real.exp (((j : ℝ) + 1) / 2) := by nlinarith
  have h3 := Real.log_le_log hx h2
  rw [Real.log_exp] at h3
  linarith

section Initial
variable (ℓ : T.V → ℕ) (lam : ℕ → ℝ) (h : ℕ → ℕ) (ε : ℝ) (α : ℕ → ℝ)
  (hT : T.WellFormed) (hℓ : ∀ a b : T.V, T.StrictAnc a b → ℓ b < ℓ a)

include hT hℓ

/-- The initial induction (eq. cf-initial-induction): `12 P_v(0) ≤ (ε/(8(j+1)²))^{h_j}` at a
level-`j` vertex. -/
theorem pot_init_bound (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) (hlam : ∀ k, 0 < lam k)
    (hh : ∀ k, 16 ≤ h k)
    (hreq : ∀ v, ∀ Q ∈ T.reqs v, α (ℓ v) ≤ Q.card ∧ T.quota v Q = (1 / 2 - ε / 2) * Q.card)
    (hcard : ∀ v, (T.reqs v).card ≤ 2 ^ (2 * d * h (ℓ v)))
    (hlα : ∀ j, lam j * α j =
      4 / ε * (2 * d * Real.log 2 + 1 + Real.log (16 / ε)) * (j + 1) * h j) :
    ∀ v, 12 * pot ℓ lam (ε / 2) h v T.init ≤ (ε / (8 * ((ℓ v : ℝ) + 1) ^ 2)) ^ h (ℓ v) := by
  intro v
  induction hn : ℓ v using Nat.strong_induction_on generalizing v with
  | _ j ih =>
    -- the allowance of every monitored descendant is small
    have hg : ∀ u ∈ Dset T.init v, gA h (ℓ u) (pot ℓ lam (ε / 2) h u T.init) ≤
        ε / (8 * ((ℓ u : ℝ) + 1) ^ 2) := by
      intro u hu
      have hlt : ℓ u < j := hn ▸ hℓ v u (mem_Dset.1 hu).1
      have h1 := ih (ℓ u) hlt u rfl
      have hP0 := pot_nonneg ℓ lam (ε / 2) h hℓ u T.init
      unfold gA
      have hh0 : (h (ℓ u) : ℕ) ≠ 0 := by have := hh (ℓ u); omega
      calc (12 * pot ℓ lam (ε / 2) h u T.init) ^ ((1 : ℝ) / h (ℓ u)) ≤
            ((ε / (8 * ((ℓ u : ℝ) + 1) ^ 2)) ^ h (ℓ u)) ^ ((1 : ℝ) / h (ℓ u)) :=
            Real.rpow_le_rpow (by positivity) h1 (by positivity)
        _ = ε / (8 * ((ℓ u : ℝ) + 1) ^ 2) := by
            rw [one_div]; exact Real.pow_rpow_inv_natCast (by positivity) hh0
    -- each weight is at most `exp(-λ_j ε |Q| / 4)`
    have hQ : ∀ Q ∈ T.reqs v, expo ℓ lam (ε / 2) h (fun u => pot ℓ lam (ε / 2) h u T.init)
        T.init v Q ≤ -(lam j * ε * α j / 4) := by
      intro Q hQv
      obtain ⟨hα, hquota⟩ := hreq v Q hQv
      rw [hn] at hα
      have hQE : Q ⊆ T.E v := hT.2.2.2.2.2 v Q hQv
      have hnQ : nQ T.init v Q = Q.card := by
        unfold nQ
        rw [eff_init hT, Finset.inter_eq_left.2 hQE]
        congr 1
        exact Finset.filter_true_of_mem fun z _ => ⟨Finset.notMem_empty z, Finset.notMem_empty z⟩
      have hout : T.outstanding T.init v Q = (1 / 2 - ε / 2) * Q.card := by
        unfold RegionTree.outstanding; rw [hquota]; simp [RegionTree.init, RegionTree.State.credit]
      -- the allowances: level by level, the cubes of one level are disjoint
      have hA : ∑ u ∈ Dset T.init v, (mQ T Q u : ℝ) * gA h (ℓ u)
          (pot ℓ lam (ε / 2) h u T.init) ≤ ε / 4 * Q.card := by
        have hmaps : ∀ u ∈ Dset T.init v, ℓ u ∈ Finset.range j := fun u hu =>
          Finset.mem_range.2 (hn ▸ hℓ v u (mem_Dset.1 hu).1)
        calc ∑ u ∈ Dset T.init v, (mQ T Q u : ℝ) * gA h (ℓ u) (pot ℓ lam (ε / 2) h u T.init)
            ≤ ∑ u ∈ Dset T.init v, (mQ T Q u : ℝ) * (ε / (8 * ((ℓ u : ℝ) + 1) ^ 2)) :=
              Finset.sum_le_sum fun u hu => mul_le_mul_of_nonneg_left (hg u hu) (Nat.cast_nonneg _)
          _ = ∑ k ∈ Finset.range j, ∑ u ∈ (Dset T.init v).filter (fun u => ℓ u = k),
                (mQ T Q u : ℝ) * (ε / (8 * ((ℓ u : ℝ) + 1) ^ 2)) :=
              (Finset.sum_fiberwise_of_maps_to hmaps _).symm
          _ ≤ ∑ k ∈ Finset.range j, (Q.card : ℝ) * (ε / (8 * ((k : ℝ) + 1) ^ 2)) := by
              refine Finset.sum_le_sum fun k _ => ?_
              rw [Finset.sum_congr rfl fun u hu => by rw [(Finset.mem_filter.1 hu).2], ← Finset.sum_mul]
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              -- disjointness at one level
              have hdisj : Set.PairwiseDisjoint (↑((Dset T.init v).filter fun u => ℓ u = k))
                  (fun u => Q ∩ T.E u) := by
                intro a ha b hb hab
                simp only [Function.onFun]
                rw [Finset.disjoint_left]
                intro z hza hzb
                have ha' := (Finset.mem_filter.1 ha).2
                have hb' := (Finset.mem_filter.1 hb).2
                rcases comparable hT a b (Finset.mem_inter.1 hza).2 (Finset.mem_inter.1 hzb).2
                  with h1 | h1
                · have := hℓ a b ⟨h1, hab⟩; omega
                · have := hℓ b a ⟨h1, fun h => hab h.symm⟩; omega
              have := Finset.card_biUnion hdisj
              unfold mQ
              rw [← Nat.cast_sum, ← this]
              exact_mod_cast Finset.card_le_card (Finset.biUnion_subset.2 fun u _ =>
                Finset.inter_subset_left)
          _ = ε / 8 * Q.card * ∑ k ∈ Finset.range j, 1 / ((k : ℝ) + 1) ^ 2 := by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; field_simp
          _ ≤ ε / 8 * Q.card * (5 / 3) :=
              mul_le_mul_of_nonneg_left (sum_inv_sq_le j) (by positivity)
          _ ≤ ε / 4 * Q.card := by nlinarith [Nat.cast_nonneg (α := ℝ) Q.card]
      unfold expo
      rw [hnQ, hout, hn]
      have hl := hlam j
      have : 2 * ((1 / 2 - ε / 2) * (Q.card : ℝ)) - (1 - ε / 2) * Q.card +
          ∑ u ∈ Dset T.init v, (mQ T Q u : ℝ) * gA h (ℓ u) (pot ℓ lam (ε / 2) h u T.init) ≤
          -(ε * α j / 4) := by nlinarith
      nlinarith
    -- summing over at most `2^{2 d h_j}` requirements
    have hP : pot ℓ lam (ε / 2) h v T.init ≤
        (T.reqs v).card * Real.exp (-(lam j * ε * α j / 4)) := by
      rw [pot_eq ℓ lam (ε / 2) h hℓ]
      unfold potF
      calc _ ≤ ∑ Q ∈ T.reqs v, Real.exp (-(lam j * ε * α j / 4)) :=
            Finset.sum_le_sum fun Q hQv => Real.exp_le_exp.2 (hQ Q hQv)
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    set H : ℝ := ((h j : ℕ) : ℝ) with hH
    have hH16 : (16 : ℝ) ≤ H := by rw [hH]; exact_mod_cast hh j
    set L2 := Real.log 2 with hL2
    have hL2pos : 0 < L2 := Real.log_pos one_lt_two
    have hcardR : ((T.reqs v).card : ℝ) ≤ Real.exp (2 * d * H * L2) := by
      have := hcard v
      rw [hn] at this
      calc ((T.reqs v).card : ℝ) ≤ ((2 ^ (2 * d * h j) : ℕ) : ℝ) := by exact_mod_cast this
        _ = Real.exp (2 * d * H * L2) := by
          rw [hH, hL2, show (2 * d * (h j : ℝ) * Real.log 2) = ((2 * d * h j : ℕ) : ℝ) * Real.log 2
            by push_cast; ring, Real.exp_nat_mul, Real.exp_log two_pos]; push_cast; ring
    have hlα' := hlα j
    set lε := Real.log ε with hlε
    have hlε0 : lε ≤ 0 := Real.log_nonpos hε.le (by linarith)
    have hl16 : Real.log (16 / ε) = 4 * L2 - lε := by
      rw [Real.log_div (by norm_num) hε.ne', show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      push_cast; ring
    -- the exponent bound
    set lj := Real.log ((j : ℝ) + 1) with hlj
    have hlj2 := two_log_le j
    have hl12 : Real.log 12 ≤ 16 * L2 := by
      rw [hL2, ← Real.log_rpow two_pos]
      exact Real.log_le_log (by norm_num) (by norm_num)
    have hδpos : 0 < ε / (8 * ((j : ℝ) + 1) ^ 2) := by positivity
    have hlogδ : Real.log (ε / (8 * ((j : ℝ) + 1) ^ 2)) = lε - 3 * L2 - 2 * lj := by
      rw [Real.log_div hε.ne' (by positivity), Real.log_mul (by norm_num) (by positivity),
        Real.log_pow, show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      push_cast; ring
    have hexp : Real.log 12 + 2 * d * H * L2 - lam j * ε * α j / 4 ≤
        H * (lε - 3 * L2 - 2 * lj) := by
      have e1 : lam j * ε * α j / 4 = (2 * d * L2 + 1 + (4 * L2 - lε)) * (j + 1) * H := by
        rw [mul_right_comm, hlα', ← hl16, hH]; field_simp
      rw [e1]
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      nlinarith [mul_nonneg (mul_nonneg hd0 hL2pos.le) (mul_nonneg hj0 (by linarith : (0 : ℝ) ≤ H)),
        mul_nonneg (mul_nonneg (neg_nonneg.2 hlε0) hj0) (by linarith : (0 : ℝ) ≤ H),
        mul_nonneg (by linarith : (0 : ℝ) ≤ (j : ℝ) + 1 - 2 * lj) (by linarith : (0 : ℝ) ≤ H),
        mul_nonneg (mul_nonneg hL2pos.le hj0) (by linarith : (0 : ℝ) ≤ H)]
    calc 12 * pot ℓ lam (ε / 2) h v T.init
        ≤ 12 * (Real.exp (2 * d * H * L2) * Real.exp (-(lam j * ε * α j / 4))) := by
          have := hP.trans (mul_le_mul_of_nonneg_right hcardR (Real.exp_pos _).le)
          linarith
      _ = Real.exp (Real.log 12 + 2 * d * H * L2 - lam j * ε * α j / 4) := by
          rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_log (by norm_num)]; ring
      _ ≤ Real.exp (H * (lε - 3 * L2 - 2 * lj)) := Real.exp_le_exp.2 hexp
      _ = (ε / (8 * ((j : ℝ) + 1) ^ 2)) ^ h j := by
          rw [← hlogδ, hH, Real.exp_nat_mul, Real.exp_log hδpos]

/-- (P1), initial part: every initial potential is at most `1/16`. -/
theorem pot_init_le (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) (hlam : ∀ k, 0 < lam k)
    (hh : ∀ k, 16 ≤ h k)
    (hreq : ∀ v, ∀ Q ∈ T.reqs v, α (ℓ v) ≤ Q.card ∧ T.quota v Q = (1 / 2 - ε / 2) * Q.card)
    (hcard : ∀ v, (T.reqs v).card ≤ 2 ^ (2 * d * h (ℓ v)))
    (hlα : ∀ j, lam j * α j =
      4 / ε * (2 * d * Real.log 2 + 1 + Real.log (16 / ε)) * (j + 1) * h j) (v : T.V) :
    pot ℓ lam (ε / 2) h v T.init ≤ 1 / 16 := by
  have h1 := pot_init_bound ℓ lam h ε α hT hℓ hε hε4 hlam hh hreq hcard hlα v
  have hδ0 : 0 ≤ ε / (8 * ((ℓ v : ℝ) + 1) ^ 2) := by positivity
  have hδ1 : ε / (8 * ((ℓ v : ℝ) + 1) ^ 2) ≤ 1 / 32 := by
    rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ ((ℓ v : ℝ) + 1) ^ 2 := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) (ℓ v)])
    nlinarith
  have h2 : (ε / (8 * ((ℓ v : ℝ) + 1) ^ 2)) ^ h (ℓ v) ≤ ε / (8 * ((ℓ v : ℝ) + 1) ^ 2) :=
    pow_le_of_le_one hδ0 (by linarith) (by have := hh (ℓ v); omega)
  linarith

end Initial

/-! #### The interface: the explicit potentials satisfy `PotentialProps` at every state -/

/-- The explicit potentials on a well-formed tree with levels satisfy the locality properties and
(P1)–(P4) for the constant `σ`, at every reachable state (the proof does not use reachability),
provided the constants satisfy
the numerical conditions of the proof of Claim A.6 and the requirements have light intersections
with the lower levels. -/
theorem potentialProps_of (ℓ : T.V → ℕ) (lam : ℕ → ℝ) (h : ℕ → ℕ) (ε : ℝ) (α : ℕ → ℝ)
    {γ ρ η η' β : ℕ → ℝ} (σ : ℝ) (hT : T.WellFormed)
    (hℓ : ∀ a b : T.V, T.StrictAnc a b → ℓ b < ℓ a) (hQ : QParams lam (ε / 2) h γ ρ η η' β)
    (hlight : ∀ v, ∀ Q ∈ T.reqs v, ∀ u, T.StrictAnc v u → (mQ T Q u : ℝ) ≤ γ (ℓ u))
    (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) (hh : ∀ k, 16 ≤ h k)
    (hreq : ∀ v, ∀ Q ∈ T.reqs v, α (ℓ v) ≤ Q.card ∧ T.quota v Q = (1 / 2 - ε / 2) * Q.card)
    (hcard : ∀ v, (T.reqs v).card ≤ 2 ^ (2 * d * h (ℓ v)))
    (hlα : ∀ j, lam j * α j =
      4 / ε * (2 * d * Real.log 2 + 1 + Real.log (16 / ε)) * (j + 1) * h j)
    (hσ : 0 < σ ∧ σ ≤ 1 / 16) (hρσ : ∀ j, ρ j ≤ σ) (hησ : ∀ j, 8 * σ ≤ η j)
    (hβσ : ∀ j, Real.exp (β j) ≤ 1 + 2 * σ) :
    T.PotentialProps (pot ℓ lam (ε / 2) h) σ := by
  have hlam0 : ∀ k, 0 ≤ lam k := fun k => (hQ.lam_pos k).le
  have hμ0 := hQ.μ0
  have hμ1 := hQ.μ1
  refine ⟨hσ, fun st _ v => pot_nonneg ℓ lam (ε / 2) h hℓ v st,
    fun st _ v x hx => pot_black_loc ℓ lam (ε / 2) h hT hℓ v st x hx,
    fun st _ v y hy => pot_white_loc ℓ lam (ε / 2) h hT hℓ v st y hy,
    fun st _ u v hvu => pot_act_loc ℓ lam (ε / 2) h hT hℓ v st u hvu,
    pot_init_le ℓ lam h ε α hT hℓ hε hε4 hQ.lam_pos hh hreq hcard hlα,
    fun st _ v hall ⟨Q, hQv, hout⟩ => pot_detect ℓ lam (ε / 2) h hT hℓ hQ.lam_pos st v hall
      Q hQv hout,
    ?_, fun st _ u y => pot_white_mono ℓ lam (ε / 2) h hℓ hlam0 hμ0 u st y, ?_, ?_⟩
  · -- (P2)
    intro st _ v hsb x hx hxu
    rw [score_of_mem _ hx]
    have hq := (pot_quant ℓ lam (ε / 2) h hT hℓ hQ hlight v st hsb x x hxu hxu).1
    have hP0 := pot_nonneg ℓ lam (ε / 2) h hℓ v st
    refine ⟨sub_nonneg.2 (pot_black_mono ℓ lam (ε / 2) h hℓ hlam0 hμ1 v st x),
      hq.trans (mul_le_mul_of_nonneg_right (hρσ _) hP0)⟩
  · -- (P3)
    intro st _ v hsb y hy hyu
    obtain ⟨-, -, hadv, -⟩ := pot_quant ℓ lam (ε / 2) h hT hℓ hQ hlight v st hsb y y hyu hyu
    have hB := sub_nonneg.2 (pot_black_mono ℓ lam (ε / 2) h hℓ hlam0 hμ1 v st y)
    refine ⟨?_, fun x hx hxu hxy => ?_⟩
    · rw [score_of_mem _ hy]
      exact (mul_le_mul_of_nonneg_right (by linarith [hησ (ℓ v)]) hB).trans hadv
    · obtain ⟨-, -, -, hsc⟩ :=
        pot_quant ℓ lam (ε / 2) h hT hℓ hQ hlight v st hsb x y hxu hyu
      have hx' : x ∈ T.eff (T.whiteClaim st y) v := hx
      rw [score_of_mem _ hx', score_of_mem _ hx]
      have hBx := sub_nonneg.2 (pot_black_mono ℓ lam (ε / 2) h hℓ hlam0 hμ1 v st x)
      exact (hsc hxy).trans (mul_le_mul_of_nonneg_right (hβσ _) hBx)
  · -- (P4)
    intro st _ u x _ hPu hx hxu v hvu
    exact ⟨pot_p4 ℓ lam (ε / 2) h hT hℓ hlam0 hμ0 hμ1 st u x hPu hx v hvu,
      reserve_p4 ℓ lam (ε / 2) h hT hℓ hlam0 hμ0 hμ1 st u x hPu hx v hvu⟩

/-! ### The dyadic tree: levels, light intersections, and the count of requirements -/

/-- The level of a vertex of the dyadic tree: `j` for a scale-`j` cube, `J + 1` for the root. -/
def dyLevel (D : Scales) (ε : ℝ) (E : Finset (Pt d)) (J : ℕ) (v : (dyadicTree D ε E J).V) : ℕ :=
  J + 1 - (dyadicTree D ε E J).depth v

theorem dy_depth_le (D : Scales) (ε : ℝ) (E : Finset (Pt d)) (J : ℕ)
    (v : (dyadicTree D ε E J).V) : (dyadicTree D ε E J).depth v ≤ J + 1 := by
  rcases v with _ | ⟨⟨⟨j, c⟩, hp⟩⟩
  · exact Nat.zero_le _
  · dsimp only [dyadicTree, RegionTree.depth]; omega

theorem dyLevel_strict (D : Scales) (hD : StrictMono D.h) (ε : ℝ) (E : Finset (Pt d)) (J : ℕ) :
    ∀ a b : (dyadicTree D ε E J).V, (dyadicTree D ε E J).StrictAnc a b →
      dyLevel D ε E J b < dyLevel D ε E J a := by
  intro a b hab
  have h1 := strictAnc_depth (dyadicTree_wellFormed D hD ε E J) hab
  have h2 := dy_depth_le D ε E J b
  unfold dyLevel; omega

theorem dyLevel_some (D : Scales) (ε : ℝ) (E : Finset (Pt d)) (J : ℕ) (j : Fin (J + 1)) (c : Pt d)
    (hp) : dyLevel D ε E J (some ⟨(j, c), hp⟩ : (dyadicTree D ε E J).V) = j.val := by
  unfold dyLevel
  dsimp only [dyadicTree, RegionTree.depth]
  have := j.isLt
  omega

/-- Every requirement at a scale-`j` cube is `E` intersected with the level-`j` remainder of some
box `Icc p q`, and that remainder has at least `α_j` points. -/
theorem dy_mem_reqs (D : Scales) (ε : ℝ) (E : Finset (Pt d)) (J : ℕ) (j : Fin (J + 1)) (c : Pt d)
    (hp) {Q : Finset (Pt d)}
    (hQ : Q ∈ (dyadicTree D ε E J).reqs (some ⟨(j, c), hp⟩ : (dyadicTree D ε E J).V)) :
    ∃ p q : Pt d, D.α j ≤ ((remainder D E (Set.Icc p q) j).ncard : ℝ) ∧
      ∀ x, x ∈ Q ↔ x ∈ E ∧ x ∈ remainder D E (Set.Icc p q) j := by
  dsimp only [dyadicTree, RegionTree.reqs] at hQ
  obtain ⟨⟨p, q⟩, hpq, rfl⟩ := Finset.mem_image.1 hQ
  refine ⟨p, q, (Finset.mem_filter.1 hpq).2.2.2, fun x => ?_⟩
  rw [Finset.mem_filter]

/-- Light intersections (eq. allscale-light): a requirement at a cube meets every lower vertex in
at most `γ` of that vertex's level points. -/
theorem dy_light (D : Scales) (hD : StrictMono D.h) (hγ : ∀ k, 0 < D.γ k) (ε : ℝ)
    (E : Finset (Pt d)) (J : ℕ) :
    ∀ v, ∀ Q ∈ (dyadicTree D ε E J).reqs v, ∀ u, (dyadicTree D ε E J).StrictAnc v u →
      (mQ (dyadicTree D ε E J) Q u : ℝ) ≤ D.γ (dyLevel D ε E J u) := by
  intro v Q hQ u hvu
  have hlt := dyLevel_strict D hD ε E J v u hvu
  rcases v with _ | ⟨⟨⟨j, c⟩, hp⟩⟩
  · exact absurd hQ (by dsimp only [dyadicTree, RegionTree.reqs]; simp)
  rcases u with _ | ⟨⟨⟨k, c'⟩, hq⟩⟩
  · have := strictAnc_depth (dyadicTree_wellFormed D hD ε E J) hvu
    dsimp only [dyadicTree, RegionTree.depth] at this; omega
  rw [dyLevel_some, dyLevel_some] at hlt
  rw [dyLevel_some]
  obtain ⟨p, q, -, hQiff⟩ := dy_mem_reqs D ε E J j c hp hQ
  set R := Set.Icc p q with hR
  by_contra hgt
  rw [not_le] at hgt
  have hEu : ∀ y, y ∈ (dyadicTree D ε E J).E (some ⟨(k, c'), hq⟩) ↔ y ∈ E ∧ cubeIdx D k y = c' := by
    intro y; dsimp only [dyadicTree, RegionTree.E]; rw [Finset.mem_filter]
  have hne : (Q ∩ (dyadicTree D ε E J).E (some ⟨(k, c'), hq⟩)).Nonempty := by
    rw [← Finset.card_pos]
    unfold mQ at hgt
    have := hγ k
    exact_mod_cast (this.trans hgt)
  obtain ⟨x, hx⟩ := hne
  obtain ⟨hxQ, hxu⟩ := Finset.mem_inter.1 hx
  have hxrem := ((hQiff x).1 hxQ).2
  have hxk := ((hEu x).1 hxu).2
  -- the scale-`k` mass of `x` in `R` is at least `|Q ∩ E_u|`
  have hmass : ((Q ∩ (dyadicTree D ε E J).E (some ⟨(k, c'), hq⟩)).card : ℝ) ≤
      massIn D E R k x := by
    unfold massIn
    rw [← Set.ncard_coe_finset]
    refine Nat.cast_le.2 (Set.ncard_le_ncard (fun y hy => ?_) ?_)
    · have hy' := Finset.mem_inter.1 (Finset.mem_coe.1 hy)
      have hyrem := ((hQiff y).1 hy'.1).2
      exact ⟨⟨hyrem.1, hyrem.2.1⟩, by
        show cubeIdx D k y = cubeIdx D k x
        rw [((hEu y).1 hy'.2).2, hxk]⟩
    · exact (Set.toFinite _).subset (fun y hy => hy.1.1)
  have hP : ∃ m, m ≤ j.val - 1 ∧ (k.val ≤ m ∧ D.γ m ≤ massIn D E R m x) :=
    ⟨k.val, by omega, le_rfl, by unfold mQ at hgt; linarith⟩
  set m := Nat.findGreatest (fun m => k.val ≤ m ∧ D.γ m ≤ massIn D E R m x) (j.val - 1) with hm
  have hmP : k.val ≤ m ∧ D.γ m ≤ massIn D E R m x := by
    obtain ⟨m0, hm0, hP0⟩ := hP
    exact Nat.findGreatest_spec (P := fun m => k.val ≤ m ∧ D.γ m ≤ massIn D E R m x) hm0 hP0
  have hmle : m ≤ j.val - 1 := Nat.findGreatest_le _
  have hsel : Selected D E R j.val m x := by
    refine ⟨by omega, hmP.2, fun m' hm' hm'j => ?_⟩
    have := Nat.findGreatest_is_greatest (P := fun m => k.val ≤ m ∧ D.γ m ≤ massIn D E R m x)
      (show m < m' by omega) (by omega)
    rw [not_and, not_le] at this
    exact this (by omega)
  exact hxrem.2.2 m hsel

theorem dy_req (D : Scales) (ε : ℝ) (E : Finset (Pt d)) (J : ℕ) :
    ∀ v, ∀ Q ∈ (dyadicTree D ε E J).reqs v, D.α (dyLevel D ε E J v) ≤ Q.card ∧
      (dyadicTree D ε E J).quota v Q = (1 / 2 - ε / 2) * Q.card := by
  intro v Q hQ
  refine ⟨?_, rfl⟩
  rcases v with _ | ⟨⟨⟨j, c⟩, hp⟩⟩
  · exact absurd hQ (by dsimp only [dyadicTree, RegionTree.reqs]; simp)
  rw [dyLevel_some]
  obtain ⟨p, q, hα, hQiff⟩ := dy_mem_reqs D ε E J j c hp hQ
  have : (remainder D E (Set.Icc p q) j).ncard = Q.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext y
    rw [Finset.mem_coe, hQiff]
    exact ⟨fun h => ⟨h.1, h⟩, fun h => h.2⟩
  rw [← this]; exact hα

theorem dy_card (D : Scales) (ε : ℝ) (E : Finset (Pt d)) (J : ℕ) :
    ∀ v, ((dyadicTree D ε E J).reqs v).card ≤ 2 ^ (2 * d * D.h (dyLevel D ε E J v)) := by
  intro v
  rcases v with _ | ⟨⟨⟨j, c⟩, hp⟩⟩
  · dsimp only [dyadicTree, RegionTree.reqs]; simp
  rw [dyLevel_some]
  dsimp only [dyadicTree, RegionTree.reqs]
  refine Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans ?_)
  rw [Finset.card_product, Pi.card_Icc]
  have : ∀ i : Fin d, (Finset.Icc (c i * 2 ^ D.h j.val) (c i * 2 ^ D.h j.val + 2 ^ D.h j.val - 1)).card =
      2 ^ D.h j.val := by
    intro i
    rw [Int.card_Icc, show c i * 2 ^ D.h j.val + 2 ^ D.h j.val - 1 + 1 - c i * 2 ^ D.h j.val =
      ((2 ^ D.h j.val : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast]
  simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul, ← pow_add]
  apply le_of_eq; congr 1; ring

/-! ### The constants of Claim A.6 (eq. cf-parameters) -/

/-- `C = (4/ε)(2d log 2 + 1 + log(16/ε))`. -/
def cfC (d : ℕ) (ε : ℝ) : ℝ := 4 / ε * (2 * d * Real.log 2 + 1 + Real.log (16 / ε))

/-- `a = ⌈2/τ⌉`. -/
def cfA (τ : ℝ) : ℕ := ⌈2 / τ⌉₊

/-- The integer `B = B(d, ε)`, large enough for `h_j ≥ 16` and for (eq. cf-move-bound). -/
def cfB (d : ℕ) (ε : ℝ) : ℕ := max 16 ⌈16384 * (1 + ε / 2 + cfC d ε / 32) / ε⌉₊

/-- `Λ_j = B^{j+1} ((j+1)!)^3`, through its recursion `Λ_{j+1} = B (j+2)^3 Λ_j`. -/
def cfLam (B : ℕ) : ℕ → ℕ
  | 0 => B
  | j + 1 => B * (j + 2) ^ 3 * cfLam B j

/-- `h_j = Λ_j^a`. -/
def cfH (B a : ℕ) (j : ℕ) : ℕ := cfLam B j ^ a

/-- `δ_j = ε / (8 (j+1)^2)`. -/
def cfδ (ε : ℝ) (j : ℕ) : ℝ := ε / (8 * ((j : ℝ) + 1) ^ 2)

/-- `α_j = C (j+1) h_j Λ_j`. -/
def cfα (d : ℕ) (ε : ℝ) (B a : ℕ) (j : ℕ) : ℝ := cfC d ε * ((j : ℝ) + 1) * cfH B a j * cfLam B j

/-- `γ_j = α_j / δ_j`. -/
def cfγ (d : ℕ) (ε : ℝ) (B a : ℕ) (j : ℕ) : ℝ := cfα d ε B a j / cfδ ε j

/-- The retained scales and thresholds of Claim A.6. -/
def cfScales (d : ℕ) (ε τ : ℝ) : Scales :=
  ⟨cfH (cfB d ε) (cfA τ), cfα d ε (cfB d ε) (cfA τ), cfγ d ε (cfB d ε) (cfA τ)⟩

/-- `λ_j = 1/Λ_j`. -/
def cfLamInv (B : ℕ) (j : ℕ) : ℝ := 1 / (cfLam B j : ℝ)

/-- `ρ_j = μ / (1024 (j+1)^2)` with `μ = ε/2`. -/
def cfρ (ε : ℝ) (j : ℕ) : ℝ := ε / (2048 * ((j : ℝ) + 1) ^ 2)

/-- `R_{j-1} = ∑_{k<j} ρ_k`. -/
def cfR (ε : ℝ) (j : ℕ) : ℝ := ∑ k ∈ Finset.range j, cfρ ε k

/-- `η_j = μ - 16 R_j`. -/
def cfη (ε : ℝ) (j : ℕ) : ℝ := ε / 2 - 16 * cfR ε (j + 1)

/-- `η_{j-1} = μ - 16 R_{j-1}` (with `η_{-1} = μ`). -/
def cfη' (ε : ℝ) (j : ℕ) : ℝ := ε / 2 - 16 * cfR ε j

/-- `β_j = 16 R_j`. -/
def cfβ (ε : ℝ) (j : ℕ) : ℝ := 16 * cfR ε (j + 1)

theorem cfLam_eq (B j : ℕ) : cfLam B j = B ^ (j + 1) * ((j + 1).factorial) ^ 3 := by
  induction j with
  | zero => simp [cfLam]
  | succ j ih =>
    rw [cfLam, ih, Nat.factorial_succ (j + 1)]
    ring

theorem cfLam_ge (B j : ℕ) : B * (j + 1) ^ 3 ≤ cfLam B j ∧ B ^ (j + 1) ≤ cfLam B j := by
  rw [cfLam_eq]
  have h1 : (j + 1) ^ 3 ≤ ((j + 1).factorial) ^ 3 := Nat.pow_le_pow_left (Nat.self_le_factorial _) 3
  have h2 : B ≤ B ^ (j + 1) := Nat.le_self_pow (by omega) B
  have h3 : 1 ≤ ((j + 1).factorial) ^ 3 := Nat.one_le_pow _ _ (Nat.factorial_pos _)
  exact ⟨Nat.mul_le_mul h2 h1, Nat.le_mul_of_pos_right _ h3⟩

theorem cfLam_pos (B j : ℕ) (hB : 1 ≤ B) : 0 < cfLam B j := by
  have := (cfLam_ge B j).1
  have : 0 < B * (j + 1) ^ 3 := Nat.mul_pos (by omega) (by positivity)
  omega

/-- `∑_{k<j} (k+1) Λ_k ≤ 2j Λ_j / (B (j+1)^3)` (the rapid growth of `Λ`). -/
theorem cfLam_sum (B : ℕ) (hB : 2 ≤ B) (j : ℕ) :
    B * (j + 1) ^ 3 * ∑ k ∈ Finset.range j, (k + 1) * cfLam B k ≤ 2 * j * cfLam B j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, cfLam]
    set S := ∑ k ∈ Finset.range j, (k + 1) * cfLam B k
    have hS : S ≤ (j + 1) * cfLam B j := by
      have h1 : 2 * (j + 1) ^ 3 * S ≤ B * (j + 1) ^ 3 * S :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hB)
      have h2 : S ≤ (j + 1) ^ 3 * S := Nat.le_mul_of_pos_left _ (by positivity)
      have h3 : j * cfLam B j ≤ (j + 1) * cfLam B j := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    have : B * (j + 1 + 1) ^ 3 * S ≤ B * (j + 1 + 1) ^ 3 * ((j + 1) * cfLam B j) :=
      Nat.mul_le_mul_left _ hS
    push_cast
    nlinarith

theorem cfR_nonneg (ε : ℝ) (hε : 0 ≤ ε) (j : ℕ) : 0 ≤ cfR ε j :=
  Finset.sum_nonneg fun k _ => by unfold cfρ; positivity

theorem cfR_le (ε : ℝ) (hε : 0 ≤ ε) (j : ℕ) : cfR ε j ≤ ε / 2048 * (5 / 3) := by
  unfold cfR cfρ
  have : ∑ k ∈ Finset.range j, ε / (2048 * ((k : ℝ) + 1) ^ 2) =
      ε / 2048 * ∑ k ∈ Finset.range j, 1 / ((k : ℝ) + 1) ^ 2 := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left (sum_inv_sq_le j) (by positivity)

theorem cfR_mono (ε : ℝ) (hε : 0 ≤ ε) {i j : ℕ} (hij : i ≤ j) : cfR ε i ≤ cfR ε j :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hij)
    fun k _ _ => by unfold cfρ; positivity

theorem cfR_succ (ε : ℝ) (j : ℕ) : cfR ε (j + 1) = cfR ε j + cfρ ε j := Finset.sum_range_succ _ _

theorem cfρ_le4 (ε : ℝ) (hε : 0 ≤ ε) (k : ℕ) : cfρ ε k ≤ 4 * cfρ ε (k + 1) := by
  unfold cfρ
  push_cast
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have : ((k : ℝ) + 1 + 1) ^ 2 ≤ 4 * ((k : ℝ) + 1) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left this hε]

theorem cfC_pos (d : ℕ) (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) : 0 < cfC d ε := by
  unfold cfC
  have h1 : 0 ≤ Real.log (16 / ε) := Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)
  have h2 : 0 ≤ 2 * (d : ℝ) * Real.log 2 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num); positivity
  positivity

theorem cfB_ge (d : ℕ) (ε : ℝ) : 16 ≤ cfB d ε ∧
    16384 * (1 + ε / 2 + cfC d ε / 32) / ε ≤ cfB d ε := by
  unfold cfB
  refine ⟨le_max_left _ _, (Nat.le_ceil _).trans ?_⟩
  exact_mod_cast le_max_right _ _

theorem cfA_ge (τ : ℝ) (hτ : 0 < τ) : 1 ≤ cfA τ ∧ 2 ≤ (cfA τ : ℝ) * τ := by
  unfold cfA
  refine ⟨Nat.one_le_ceil_iff.2 (by positivity), ?_⟩
  have := Nat.le_ceil (2 / τ)
  rw [div_le_iff₀ hτ] at this
  exact this

/-- The constants satisfy `QParams`: the move bound and the abstract induction inequalities
for `η`, `η'` and `β`. The additional `σ` slack bounds are proved separately by `cf_sigma`. -/
theorem cf_qparams (d : ℕ) (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) (a : ℕ) (ha : 1 ≤ a) :
    QParams (cfLamInv (cfB d ε)) (ε / 2) (cfH (cfB d ε) a) (cfγ d ε (cfB d ε) a) (cfρ ε)
      (cfη ε) (cfη' ε) (cfβ ε) := by
  set B := cfB d ε with hBdef
  obtain ⟨hB16, hBbig⟩ := cfB_ge d ε
  rw [← hBdef] at hB16 hBbig
  have hB1 : 1 ≤ B := by omega
  have hC := cfC_pos d ε hε hε4
  have hLpos : ∀ j, (0 : ℝ) < cfLam B j := fun j => by exact_mod_cast cfLam_pos B j hB1
  have hH : ∀ j, 16 ≤ cfH B a j := by
    intro j
    have h1 : 16 ≤ cfLam B j := hB16.trans ((Nat.le_mul_of_pos_right _ (by positivity)).trans
      (cfLam_ge B j).1)
    exact h1.trans (Nat.le_self_pow (by omega) _)
  have hHpos : ∀ j, (0 : ℝ) < cfH B a j := fun j => by
    have := hH j; exact_mod_cast (show 0 < cfH B a j by omega)
  have hRle := cfR_le ε hε.le
  have hR0 := cfR_nonneg ε hε.le
  refine ⟨fun k => by unfold cfLamInv; exact div_pos one_pos (hLpos k), by linarith, by linarith,
    fun k => (by omega : 2 ≤ 16).trans (hH k), fun k => ?_, fun k => by unfold cfρ; positivity,
    fun k => ?_, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, fun k j hkj => ?_,
    fun k j hkj => ?_, fun j => ?_, fun j => ?_⟩
  · unfold cfγ cfα cfδ; have := hHpos k; have := hLpos k; positivity
  · unfold cfρ
    rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) k])
    nlinarith
  · -- (eq. cf-move-bound)
    have key : ∀ k, cfγ d ε B a k * cfρ ε k / cfH B a k = cfC d ε * ((k : ℝ) + 1) * cfLam B k / 256 := by
      intro k
      unfold cfγ cfα cfδ cfρ
      have := hHpos k
      field_simp
      ring
    simp only [key]
    set S := ∑ k ∈ Finset.range j, ((k : ℝ) + 1) * (cfLam B k : ℝ) with hS
    have hsum : ∑ k ∈ Finset.range j, cfC d ε * ((k : ℝ) + 1) * cfLam B k / 256 =
        cfC d ε / 256 * S := by
      rw [hS, Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; ring
    rw [hsum]
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => by positivity
    have hSB : (B : ℝ) * ((j : ℝ) + 1) ^ 3 * S ≤ 2 * j * cfLam B j := by
      have := cfLam_sum B (by omega) j
      rw [hS]
      exact_mod_cast this
    have hLam : (B : ℝ) * ((j : ℝ) + 1) ^ 3 ≤ cfLam B j := by
      exact_mod_cast (cfLam_ge B j).1
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hBpos : (0 : ℝ) < B := by exact_mod_cast hB1
    -- `S B (j+1)^2 ≤ 2 Λ_j` and `B (j+1)^2 ≤ Λ_j`
    have hSB2 : (B : ℝ) * ((j : ℝ) + 1) ^ 2 * S ≤ 2 * cfLam B j := by
      have h1 : (B : ℝ) * ((j : ℝ) + 1) ^ 2 * S * ((j : ℝ) + 1) ≤ 2 * cfLam B j * ((j : ℝ) + 1) := by
        nlinarith [hLpos j]
      exact le_of_mul_le_mul_right h1 (by linarith)
    have hLam2 : (B : ℝ) * ((j : ℝ) + 1) ^ 2 ≤ cfLam B j := by
      have : (B : ℝ) * ((j : ℝ) + 1) ^ 2 ≤ (B : ℝ) * ((j : ℝ) + 1) ^ 3 := by
        apply mul_le_mul_of_nonneg_left _ hBpos.le
        nlinarith
      linarith
    have hP1 : (1 + ε / 2 + 4 * (cfC d ε / 256 * S)) * ((B : ℝ) * ((j : ℝ) + 1) ^ 2) ≤
        (1 + ε / 2 + cfC d ε / 32) * cfLam B j := by
      nlinarith
    have hP2 : (1 + ε / 2 + cfC d ε / 32) * 16384 ≤ ε * B := by
      rw [div_le_iff₀ hε] at hBbig; linarith
    have hfin : (1 + ε / 2 + 4 * (cfC d ε / 256 * S)) * (16384 * ((j : ℝ) + 1) ^ 2) ≤
        ε * cfLam B j := by
      have h1 := mul_le_mul_of_nonneg_right hP2 (hLpos j).le
      have h2 : (1 + ε / 2 + 4 * (cfC d ε / 256 * S)) * (16384 * ((j : ℝ) + 1) ^ 2) * B ≤
          ε * cfLam B j * B := by nlinarith
      exact le_of_mul_le_mul_right h2 hBpos
    show 1 / (cfLam B j : ℝ) * (1 + ε / 2 + 4 * (cfC d ε / 256 * S)) ≤
      ε / (2048 * ((j : ℝ) + 1) ^ 2) / 8
    calc 1 / (cfLam B j : ℝ) * (1 + ε / 2 + 4 * (cfC d ε / 256 * S)) =
          (1 + ε / 2 + 4 * (cfC d ε / 256 * S)) / cfLam B j := by ring
      _ ≤ ε / (16384 * ((j : ℝ) + 1) ^ 2) := by
          rw [div_le_div_iff₀ (hLpos j) (by positivity)]; linarith
      _ = ε / (2048 * ((j : ℝ) + 1) ^ 2) / 8 := by field_simp; ring
  · unfold cfη cfη'; rw [cfR_succ]; ring
  · unfold cfη; have := hRle (j + 1); linarith
  · unfold cfη'; have := hR0 j; linarith
  · unfold cfη cfη'; have := cfR_mono ε hε.le (show k + 1 ≤ j by omega); linarith
  · -- `β_k + 3ρ_k ≤ β_j - 4ρ_j`
    show 16 * cfR ε (k + 1) + 3 * cfρ ε k ≤ 16 * cfR ε (j + 1) - 4 * cfρ ε j
    have hρk := cfρ_le4 ε hε.le k
    have hρ0 : ∀ i, 0 ≤ cfρ ε i := fun i => by unfold cfρ; positivity
    rcases Nat.lt_or_ge (k + 1) j with hk | hk
    · -- two distinct new terms `ρ_{k+1}` and `ρ_j`
      have h1 : cfR ε (j + 1) = cfR ε (k + 1) + ∑ i ∈ Finset.Ico (k + 1) (j + 1), cfρ ε i := by
        unfold cfR; rw [Finset.sum_range_add_sum_Ico _ (by omega)]
      have h2 : cfρ ε (k + 1) + cfρ ε j ≤ ∑ i ∈ Finset.Ico (k + 1) (j + 1), cfρ ε i := by
        have : ({k + 1, j} : Finset ℕ) ⊆ Finset.Ico (k + 1) (j + 1) := by
          intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          rw [Finset.mem_Ico]; omega
        have h3 := Finset.sum_le_sum_of_subset_of_nonneg this fun i _ _ => hρ0 i
        rwa [Finset.sum_pair (by omega)] at h3
      have := hρ0 (k + 1); have := hρ0 j
      linarith
    · have hkj : j = k + 1 := by omega
      subst hkj
      rw [cfR_succ ε (k + 1)]
      linarith
  · show 4 * cfρ ε j ≤ 16 * cfR ε (j + 1)
    rw [cfR_succ]; have := hR0 j; have : 0 ≤ cfρ ε j := by unfold cfρ; positivity
    linarith
  · show 16 * cfR ε (j + 1) ≤ 1 / 2
    have := hRle (j + 1); linarith

/-- For `σ = ε/128`: `0 < σ ≤ 1/16`, `ρ_j ≤ σ`, `8σ ≤ η_j` and `e^{β_j} ≤ 1 + 2σ` for every `j`
(the non-strict form of eq. cf-slack-bounds). These are the numerical inputs from which (P2)–(P3)
are derived in `potentialProps_of`. -/
theorem cf_sigma (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) :
    (0 < ε / 128 ∧ ε / 128 ≤ 1 / 16) ∧ (∀ j, cfρ ε j ≤ ε / 128) ∧ (∀ j, 8 * (ε / 128) ≤ cfη ε j) ∧
      ∀ j, Real.exp (cfβ ε j) ≤ 1 + 2 * (ε / 128) := by
  have hRle := cfR_le ε hε.le
  refine ⟨⟨by positivity, by linarith⟩, fun j => ?_, fun j => ?_, fun j => ?_⟩
  · unfold cfρ
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (1 : ℝ) ≤ ((j : ℝ) + 1) ^ 2 := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) j])
    nlinarith
  · unfold cfη; have := hRle (j + 1); linarith
  · unfold cfβ
    have hb0 : 0 ≤ 16 * cfR ε (j + 1) := by have := cfR_nonneg ε hε.le (j + 1); linarith
    have hb1 : 16 * cfR ε (j + 1) ≤ 5 * ε / 384 := by have := hRle (j + 1); linarith
    have := Real.abs_exp_sub_one_sub_id_le (x := 16 * cfR ε (j + 1))
      (by rw [abs_of_nonneg hb0]; linarith)
    have h2 := (abs_le.1 this).2
    nlinarith

/-! ### (G1) and (G2) for the constants of Claim A.6 -/

theorem cfLam_strictMono (B : ℕ) (hB : 1 ≤ B) : StrictMono (cfLam B) := by
  refine strictMono_nat_of_lt_succ fun j => ?_
  show cfLam B j < B * (j + 2) ^ 3 * cfLam B j
  have h1 := cfLam_pos B j hB
  have h2 : 2 ≤ B * (j + 2) ^ 3 := by
    have : 8 ≤ (j + 2) ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ (j + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    nlinarith
  nlinarith

theorem summable_inv_sq : Summable fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2 := by
  have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))
  simpa using this

/-- The partial sums of `δ_j = ε/(8(j+1)²)` stay below `ε/4` (G1). -/
theorem cfδ_sum (ε : ℝ) (hε : 0 < ε) :
    Summable (cfδ ε) ∧ ∑' j, cfδ ε j ≤ ε / 4 := by
  have heq : cfδ ε = fun j : ℕ => ε / 8 * (1 / ((j : ℝ) + 1) ^ 2) := by
    funext j; unfold cfδ; field_simp
  have hs : Summable (cfδ ε) := heq ▸ summable_inv_sq.mul_left (ε / 8)
  refine ⟨hs, hs.tsum_le_of_sum_range_le fun n => ?_⟩
  rw [heq, ← Finset.mul_sum]
  have := sum_inv_sq_le n
  nlinarith

/-- (G2): `γ_{j+1} ≤ c h_j^{1+τ}` for a constant `c` depending only on `d, ε, τ`. -/
theorem cf_G2 (d : ℕ) (ε τ : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) (hτ : 0 < τ) :
    ∃ c : ℝ, cfγ d ε (cfB d ε) (cfA τ) 0 ≤ c ∧ ∀ j, cfγ d ε (cfB d ε) (cfA τ) (j + 1) ≤
      c * ((cfH (cfB d ε) (cfA τ) j : ℕ) : ℝ) ^ (1 + τ) := by
  set B := cfB d ε with hBdef
  set a := cfA τ with hadef
  obtain ⟨hB16, -⟩ := cfB_ge d ε
  rw [← hBdef] at hB16
  have hB1 : 1 ≤ B := by omega
  obtain ⟨ha1, haτ⟩ := cfA_ge τ hτ
  rw [← hadef] at ha1 haτ
  have hC := cfC_pos d ε hε hε4
  set N := 3 * a + 6 with hN
  set K : ℝ := 8 * cfC d ε / ε * (B : ℝ) ^ (a + 1) with hK
  have hK0 : 0 ≤ K := by positivity
  -- `n^N / 2^n` is bounded
  obtain ⟨M, hM⟩ := (tendsto_pow_const_div_const_pow_of_one_lt N (r := (2 : ℝ)) one_lt_two).bddAbove_range
  have hM' : ∀ n : ℕ, (n : ℝ) ^ N / 2 ^ n ≤ M := fun n => hM ⟨n, rfl⟩
  have hM0 : 0 ≤ M := (by positivity : (0 : ℝ) ≤ ((0 : ℕ) : ℝ) ^ N / 2 ^ 0).trans (hM' 0)
  refine ⟨max (cfγ d ε B a 0) (2 * K * M), le_max_left _ _, fun j => ?_⟩
  set c := max (cfγ d ε B a 0) (2 * K * M) with hc
  have hLpos : (0 : ℝ) < cfLam B j := by exact_mod_cast cfLam_pos B j hB1
  set L : ℝ := ((cfLam B j : ℕ) : ℝ) with hL
  have hL1 : (1 : ℝ) ≤ L := Nat.one_le_cast.2 (cfLam_pos B j hB1)
  -- the closed form of `γ_{j+1}`
  have hγ : cfγ d ε B a (j + 1) = K * ((j : ℝ) + 2) ^ N * L ^ (a + 1) := by
    have hΛ' : ((cfLam B (j + 1) : ℕ) : ℝ) = (B : ℝ) * ((j : ℝ) + 2) ^ 3 * L := by
      rw [hL]; show ((B * (j + 2) ^ 3 * cfLam B j : ℕ) : ℝ) = _; push_cast; ring
    have e1 : cfγ d ε B a (j + 1) =
        8 * cfC d ε / ε * ((j : ℝ) + 2) ^ 3 * ((cfLam B (j + 1) : ℕ) : ℝ) ^ (a + 1) := by
      unfold cfγ cfα cfδ cfH
      push_cast
      field_simp
      ring
    rw [e1, hΛ', mul_pow, mul_pow, ← pow_mul, hK, hN]
    ring
  -- `h_j^{1+τ} ≥ Λ_j^{a+2}`
  have hh : L ^ (a + 2) ≤ ((cfH B a j : ℕ) : ℝ) ^ (1 + τ) := by
    unfold cfH
    push_cast
    rw [← hL, ← Real.rpow_natCast_mul hLpos.le, ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hL1
    push_cast
    nlinarith
  -- `(j+2)^N ≤ 2 M Λ_j`
  have hpow : ((j : ℝ) + 2) ^ N ≤ 2 * M * L := by
    have h1 := hM' (j + 2)
    push_cast at h1
    rw [div_le_iff₀ (by positivity)] at h1
    have h2 : (2 : ℝ) ^ (j + 1) ≤ L := by
      have : 2 ^ (j + 1) ≤ B ^ (j + 1) := Nat.pow_le_pow_left (by omega) _
      have := this.trans (cfLam_ge B j).2
      rw [hL]; exact_mod_cast this
    have h3 : (2 : ℝ) ^ (j + 2) = 2 * 2 ^ (j + 1) := by ring
    nlinarith
  have hc0 : 2 * K * M ≤ c := le_max_right _ _
  rw [hγ]
  calc K * ((j : ℝ) + 2) ^ N * L ^ (a + 1) ≤ K * (2 * M * L) * L ^ (a + 1) := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hK0) (by positivity)
    _ = 2 * K * M * L ^ (a + 2) := by ring
    _ ≤ c * L ^ (a + 2) := mul_le_mul_of_nonneg_right hc0 (by positivity)
    _ ≤ c * ((cfH B a j : ℕ) : ℝ) ^ (1 + τ) := by
        apply mul_le_mul_of_nonneg_left hh
        exact (by positivity : (0 : ℝ) ≤ 2 * K * M).trans hc0

end AppendixAAux

/-! ## Claim A.6 with the manuscript's uniform constant `σ = ε/128` -/

open AppendixAAux in
/-- **Claim A.6, uniform form** (`claim:cf-potential-existence`, as stated in the manuscript):
for every dimension `d` (the bound `d ≥ 1` of the manuscript is not needed), `0 < ε ≤ 1/4` and
`τ > 0` there are retained scales, thresholds and a constant `c`
(depending only on `d, ε, τ`) satisfying (G1)–(G2), and for every board `E` and every number of
retained levels `J` the dyadic tree is well formed and admits potentials with the locality
properties and (P1)–(P4) for the single constant `σ = ε/128`, independent of `E` and `J`. The
potentials are the manuscript's explicit ones (eq. cf-potential). The theorem
`claim_cf_potential_existence` is derived from this uniform form. 

-/
theorem claim_cf_potential_existence_uniform (d : ℕ) {ε τ : ℝ} (hε : 0 < ε)
    (hε' : ε ≤ 1 / 4) (hτ : 0 < τ) :
    ∃ (D : Scales) (c : ℝ), StrictMono D.h ∧ (∀ j, 0 < D.α j ∧ D.α j < D.γ j) ∧
      Summable (fun j => D.α j / D.γ j) ∧ ∑' j, D.α j / D.γ j ≤ ε / 4 ∧
      D.γ 0 ≤ c ∧ (∀ j, D.γ (j + 1) ≤ c * (D.h j : ℝ) ^ (1 + τ)) ∧
      ∀ (E : Finset (Pt d)) (J : ℕ), (dyadicTree D ε E J).WellFormed ∧
        ∃ Pot : (dyadicTree D ε E J).V → (dyadicTree D ε E J).State → ℝ,
          (dyadicTree D ε E J).PotentialProps Pot (ε / 128) := by
  set B := cfB d ε with hBdef
  set a := cfA τ with hadef
  obtain ⟨hB16, -⟩ := cfB_ge d ε
  rw [← hBdef] at hB16
  have hB1 : 1 ≤ B := by omega
  obtain ⟨ha1, -⟩ := cfA_ge τ hτ
  rw [← hadef] at ha1
  have hC := cfC_pos d ε hε hε'
  set D := cfScales d ε τ with hDdef
  have hDh : D.h = cfH B a := rfl
  have hDα : D.α = cfα d ε B a := rfl
  have hDγ : D.γ = cfγ d ε B a := rfl
  have hQP := cf_qparams d ε hε hε' a ha1
  rw [← hBdef] at hQP
  have hLpos : ∀ j, (0 : ℝ) < cfLam B j := fun j => by exact_mod_cast cfLam_pos B j hB1
  have hmono : StrictMono D.h := by
    rw [hDh]
    exact fun i j hij => Nat.pow_lt_pow_left (cfLam_strictMono B hB1 hij) (by omega)
  have hδpos : ∀ j, 0 < cfδ ε j ∧ cfδ ε j < 1 := fun j => by
    unfold cfδ
    refine ⟨by positivity, ?_⟩
    rw [div_lt_one (by positivity)]
    have : (1 : ℝ) ≤ ((j : ℝ) + 1) ^ 2 := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) j])
    nlinarith
  have hαpos : ∀ j, 0 < cfα d ε B a j := fun j => by
    unfold cfα
    have := hLpos j
    have : (0 : ℝ) < cfH B a j := by
      unfold cfH; push_cast; positivity
    positivity
  have hpos : ∀ j, 0 < D.α j ∧ D.α j < D.γ j := fun j => by
    rw [hDα, hDγ]
    refine ⟨hαpos j, ?_⟩
    unfold cfγ
    rw [lt_div_iff₀ (hδpos j).1]
    have := hαpos j
    nlinarith [(hδpos j).2]
  have hratio : (fun j => D.α j / D.γ j) = cfδ ε := by
    funext j
    rw [hDα, hDγ]
    unfold cfγ
    exact div_div_cancel₀ (hαpos j).ne'
  obtain ⟨hsum, htsum⟩ := cfδ_sum ε hε
  obtain ⟨c, hc0, hc⟩ := cf_G2 d ε τ hε hε' hτ
  refine ⟨D, c, hmono, hpos, hratio ▸ hsum, hratio ▸ htsum, hc0, hc, fun E J => ?_⟩
  have hT := dyadicTree_wellFormed D hmono ε E J
  refine ⟨hT, pot (dyLevel D ε E J) (cfLamInv B) (ε / 2) D.h, ?_⟩
  obtain ⟨hσ, hρσ, hησ, hβσ⟩ := cf_sigma ε hε hε'
  refine potentialProps_of (dyLevel D ε E J) (cfLamInv B) D.h ε D.α (ε / 128) hT
    (dyLevel_strict D hmono ε E J) hQP
    (dy_light D hmono (fun k => (hpos k).1.trans (hpos k).2) ε E J) hε hε' (fun k => ?_)
    (dy_req D ε E J) (dy_card D ε E J) (fun j => ?_) hσ hρσ hησ hβσ
  · rw [hDh]
    show 16 ≤ cfH B a k
    have h1 : 16 ≤ cfLam B k := hB16.trans ((Nat.le_mul_of_pos_right _ (by positivity)).trans
      (cfLam_ge B k).1)
    exact h1.trans (Nat.le_self_pow (by omega) _)
  · rw [hDα, hDh]
    unfold cfLamInv cfα
    rw [← cfC]
    have := hLpos j
    field_simp

/-- **Claim A.6** (`claim:cf-potential-existence`): for `d ≥ 1`, `0 < ε ≤ 1/4` and `τ > 0`, retained
scales, thresholds and a constant `c_{d,ε,τ}` exist that satisfy (G1)–(G3), uniformly in the board,
the packet and the number of retained levels. -/
theorem claim_cf_potential_existence (d : ℕ) (hd : 1 ≤ d) {ε τ : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 4)
    (hτ : 0 < τ) : ∃ (D : Scales) (c : ℝ), ScaleConditions d D ε τ c := by
  obtain ⟨D, c, h1, h2, h3, h4, h5, h6, h7⟩ :=
    claim_cf_potential_existence_uniform d hε hε' hτ
  refine ⟨D, c, h1, h2, h3, h4, h5, h6, fun E J => ⟨(h7 E J).1, ?_⟩⟩
  obtain ⟨Pot, hP⟩ := (h7 E J).2
  exact ⟨Pot, ε / 128, hP⟩

end

end BanachDensityHD
