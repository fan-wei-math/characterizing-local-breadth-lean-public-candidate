import BanachDensity1D.Extension

/-!
# Foundational obligation O2: vertex systems exist
-/

namespace BanachDensity1D

open Set Filter Classical

namespace FoundationsAux

/-- A scale `N ≥ 1` with `1/N ≤ δ` and `s < b_N(L)` for `s = (b(L) - δ)_+` if `s > 0`. -/
theorem exists_scale {X : Set (Set ℤ)} {L : Set ℤ} (hL : L.Infinite) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, 1 ≤ N ∧ (1 : ℝ) / N ≤ δ ∧
      (0 < max (bK X L - δ) 0 → max (bK X L - δ) 0 < bn X L N) := by
  obtain ⟨hT, -, -⟩ := ChainsAux.bK_tendsto (X := X) hL
  have h1 : ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ (1 : ℝ) / N ≤ δ := by
    obtain ⟨M, hM⟩ := exists_nat_gt (1 / δ)
    filter_upwards [eventually_ge_atTop (max M 1)] with N hN
    refine ⟨le_trans (le_max_right _ _) hN, ?_⟩
    have hNpos : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le (by simp) hN
    have : (M : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_left _ _) hN
    rw [div_le_iff₀ hNpos]
    have := (div_lt_iff₀ hδ).1 (lt_of_lt_of_le hM this)
    linarith
  have h2 : ∀ᶠ N : ℕ in atTop, bK X L - δ < bn X L N :=
    hT.eventually (lt_mem_nhds (by linarith))
  obtain ⟨N, ⟨hN1, hN2⟩, hN3⟩ := (h1.and h2).exists
  refine ⟨N, hN1, hN2, fun hpos => ?_⟩
  have : max (bK X L - δ) 0 = bK X L - δ := by
    rcases le_total (bK X L - δ) 0 with h | h
    · rw [max_eq_right h] at hpos; exact absurd hpos (lt_irrefl _)
    · exact max_eq_left h
  rw [this]; exact hN3

/-- The scale chosen by `exists_scale` (`1` when its hypotheses fail). -/
noncomputable def scale (X : Set (Set ℤ)) (L : Set ℤ) (δ : ℝ) : ℕ :=
  if h : L.Infinite ∧ 0 < δ then (exists_scale (X := X) h.1 h.2).choose else 1

theorem scale_spec {X : Set (Set ℤ)} {L : Set ℤ} (hL : L.Infinite) {δ : ℝ} (hδ : 0 < δ) :
    1 ≤ scale X L δ ∧ (1 : ℝ) / scale X L δ ≤ δ ∧
      (0 < max (bK X L - δ) 0 → max (bK X L - δ) 0 < bn X L (scale X L δ)) := by
  have h : L.Infinite ∧ 0 < δ := ⟨hL, hδ⟩
  simp only [scale, dif_pos h]
  exact (exists_scale (X := X) h.1 h.2).choose_spec

/-- An enumeration of the distinct languages of `X` by an initial segment of `ℕ`. -/
theorem exists_enum {X : Set (Set ℤ)} (hX : LangClass X) :
    ∃ (isV : ℕ → Prop) (lab : ℕ → Set ℤ), (∀ u v, isV v → u ≤ v → isV u) ∧
      (∀ v, isV v → lab v ∈ X) ∧ (∀ u v, isV u → isV v → lab u = lab v → u = v) ∧
      (∀ L ∈ X, ∃ v, isV v ∧ lab v = L) := by
  have : Countable X := hX.countable.to_subtype
  rcases finite_or_infinite X with hfin | hinf
  · let e := Finite.equivFin X
    refine ⟨fun v => v < Nat.card X,
      fun v => if h : v < Nat.card X then (e.symm ⟨v, h⟩).1 else ∅, ?_, ?_, ?_, ?_⟩
    · intro u v hv huv; exact lt_of_le_of_lt huv hv
    · intro v hv; simp only [dif_pos hv]; exact (e.symm _).2
    · intro u v hu hv h
      simp only [dif_pos hu, dif_pos hv] at h
      have := e.symm.injective (Subtype.ext h)
      exact congrArg Fin.val this
    · intro L hL
      refine ⟨(e ⟨L, hL⟩).1, (e ⟨L, hL⟩).2, ?_⟩
      simp only [dif_pos (e ⟨L, hL⟩).2]
      rw [Fin.eta, e.symm_apply_apply]
  · have := Encodable.ofCountable X
    have := Denumerable.ofEncodableOfInfinite X
    let e := Denumerable.eqv X
    refine ⟨fun _ => True, fun v => (e.symm v).1, fun _ _ _ _ => trivial,
      fun v _ => (e.symm v).2, ?_, ?_⟩
    · intro u v _ _ h; exact e.symm.injective (Subtype.ext h)
    · intro L hL; exact ⟨e ⟨L, hL⟩, trivial, by simp⟩

/-- Obligation O2 (fixed ε). -/
theorem exists_fixedEpsSystem {X : Set (Set ℤ)} (hX : LangClass X) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : Requirements, IsFixedEpsSystem X ε R := by
  obtain ⟨isV, lab, hin, hmem, hinj, hsurj⟩ := exists_enum hX
  refine ⟨Requirements.mk isV lab (fun v => scale X (lab v) (ε / 2))
    (fun v => max (bK X (lab v) - ε / 2) 0) (fun v => max (bK X (lab v) - ε) 0),
    ⟨hin, hmem, hinj, hsurj, fun _ _ => rfl, fun _ _ => rfl, ?_, ?_, ?_⟩⟩
  · intro v hv
    exact (scale_spec (X := X) (hX.infinite _ (hmem v hv)) (half_pos hε)).1
  · intro v hv
    exact (scale_spec (X := X) (hX.infinite _ (hmem v hv)) (half_pos hε)).2.1
  · intro v hv
    exact (scale_spec (X := X) (hX.infinite _ (hmem v hv)) (half_pos hε)).2.2

/-- The codes `pair (idx L) m`, `L ∈ X`, `m ≥ 1`, of the formal copies. -/
def copyCode (X : Set (Set ℤ)) (idx : X → ℕ) (k : ℕ) : Prop :=
  ∃ L : X, ∃ m, 1 ≤ m ∧ Nat.pair (idx L) m = k

/-- Obligation O2 (formal copies). -/
theorem exists_copySystem {X : Set (Set ℤ)} (hX : LangClass X) :
    ∃ (R : Requirements) (copy : ℕ → ℕ), IsCopySystem X R copy := by
  have : Countable X := hX.countable.to_subtype
  obtain ⟨idx, hidx⟩ := exists_injective_nat X
  set p := copyCode X idx with hp
  obtain ⟨L0, hL0⟩ := hX.nonempty
  have hinf : (Set.ofPred p).Infinite := by
    have hinj : Function.Injective fun m : ℕ => Nat.pair (idx ⟨L0, hL0⟩) (m + 1) := by
      intro a b h
      have := (Nat.pair_eq_pair.1 h).2
      omega
    refine Set.infinite_of_injective_forall_mem hinj fun m => ?_
    exact ⟨⟨L0, hL0⟩, m + 1, by omega, rfl⟩
  have hmem : ∀ v, p (Nat.nth p v) := Nat.nth_mem_of_infinite hinf
  let Lv : ℕ → X := fun v => (hmem v).choose
  let cv : ℕ → ℕ := fun v => (hmem v).choose_spec.choose
  have hcv : ∀ v, 1 ≤ cv v ∧ Nat.pair (idx (Lv v)) (cv v) = Nat.nth p v :=
    fun v => (hmem v).choose_spec.choose_spec
  have hsm := Nat.nth_strictMono hinf
  refine ⟨Requirements.mk (fun _ => True) (fun v => (Lv v).1)
    (fun v => scale X (Lv v).1 ((1 / 2 : ℝ) ^ (cv v + 1)))
    (fun v => max (bK X (Lv v).1 - (1 / 2 : ℝ) ^ (cv v + 1)) 0)
    (fun v => max (bK X (Lv v).1 - (1 / 2 : ℝ) ^ cv v) 0), cv,
    ⟨fun _ => trivial, fun v => (Lv v).2, fun v => (hcv v).1, ?_, ?_, ?_,
      fun _ => rfl, fun _ => rfl, ?_, ?_, ?_⟩⟩
  · intro u v hL hc
    have hL' : Lv u = Lv v := Subtype.ext hL
    apply Nat.nth_injective hinf
    rw [← (hcv u).2, ← (hcv v).2]
    rw [hL', hc]
  · intro L hL m hm
    have hpk : p (Nat.pair (idx ⟨L, hL⟩) m) := ⟨⟨L, hL⟩, m, hm, rfl⟩
    refine ⟨Nat.count p (Nat.pair (idx ⟨L, hL⟩) m), ?_⟩
    have h := (hcv (Nat.count p (Nat.pair (idx ⟨L, hL⟩) m))).2
    rw [Nat.nth_count hpk] at h
    obtain ⟨h1, h2⟩ := Nat.pair_eq_pair.1 h
    exact ⟨congrArg Subtype.val (hidx h1), h2⟩
  · intro u v hL hc
    have hL' : Lv u = Lv v := Subtype.ext hL
    apply hsm.lt_iff_lt.1
    rw [← (hcv u).2, ← (hcv v).2]
    change Nat.pair (idx (Lv u)) (cv u) < Nat.pair (idx (Lv v)) (cv v)
    rw [hL', hc]
    exact Nat.pair_lt_pair_right _ (Nat.lt_succ_self _)
  · intro v
    exact (scale_spec (X := X) (hX.infinite _ (Lv v).2) (by positivity)).1
  · intro v
    exact (scale_spec (X := X) (hX.infinite _ (Lv v).2) (by positivity)).2.1
  · intro v
    exact (scale_spec (X := X) (hX.infinite _ (Lv v).2) (by positivity)).2.2

end FoundationsAux

end BanachDensity1D
