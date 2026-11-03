import BanachDensity1D.Capture

/-!
# Corollary 6.19 and Lemma 6.22: the local-density guarantee

Kleinberg–Wei, Part *Dimension one*, Section 6. The statements were moved here from
`Construction.lean` unchanged (a pure move), so that their proofs can use the lemmas proved
before them.
-/

namespace BanachDensity1D

open Set Filter Classical

namespace DensityAux

variable {R : Requirements} {C : Choices}

/-- The ancestor list is strictly increasing. (The other ancestor facts used below are
`anc_prefix`, `ForestAux.self_mem_anc`, `ForestAux.anc_le`, `ForestAux.lab_anc_sub` and
`CaptureAux.isAnc_of_le`.) -/
lemma anc_pairwise (v : ℕ) : (vdata R C v).anc.Pairwise (· < ·) := by
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    rcases ConstructionAux.vdata_cases R C v with ⟨-, hanc, -, -⟩ | ⟨u, -, huv, -, -, -, hanc, -, -⟩
    · rw [hanc]
      exact List.pairwise_singleton _ _
    · have ih3 := ih u huv
      rw [hanc, List.pairwise_append]
      refine ⟨ih3, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb; subst hb
      have := ForestAux.anc_le R C u a ha; omega

/-- The ancestor list of an ancestor is a prefix of the ancestor list. -/
lemma anc_prefix {a v : ℕ} (h : IsAnc R C a v) : (vdata R C a).anc <+: (vdata R C v).anc := by
  have key : ∀ v, ∀ a ∈ (vdata R C v).anc, (vdata R C a).anc <+: (vdata R C v).anc := by
    intro v
    induction v using Nat.strong_induction_on with
    | _ v ih =>
      rcases ConstructionAux.vdata_cases R C v with ⟨-, hanc, -, -⟩ | ⟨u, -, huv, -, -, -, hanc, -, -⟩
      · rw [hanc]
        intro a ha; rw [List.mem_singleton] at ha; subst ha; rw [hanc]
      · have ih4 := ih u huv
        have hmem : ∀ a ∈ (vdata R C v).anc, a ∈ (vdata R C u).anc ∨ a = v := by
          intro a ha; rw [hanc] at ha; simpa using ha
        intro a ha
        rcases hmem a ha with h | rfl
        · rw [hanc]; exact (ih4 a h).trans (List.prefix_append _ _)
        · exact List.prefix_refl _
  exact key v a h

/-! ### Boards -/


/-- The hypotheses on a vertex system used by the local-density argument: those of the forest
invariants (`ForestAux.Good`) plus `q ≤ max 0 (s - 1/N)`; both the fixed-`ε`
system and the formal-copy system satisfy them. -/
structure GoodSystem (X : Set (Set ℤ)) (R : Requirements) : Prop extends ForestAux.Good X R where
  q_le : ∀ v, R.isV v → R.q v ≤ max 0 (R.s v - 1 / R.N v)

variable {X : Set (Set ℤ)}


/-! ### Layer sums -/

open ChainsAux (layerSum score_eq)

/-- The layer sum of `A :: B :: t` peels off the top layer `A \ B`. -/
lemma laySum_cons_cons (A B : Set ℤ) (t : List (Set ℤ)) (J : Set ℤ) :
    layerSum (A :: B :: t) J = ((A \ B) ∩ J).ncard / 2 + layerSum (B :: t) J := by
  simp [layerSum, layers]

lemma compress_cons_head : ∀ (b : Set ℤ) (t : List (Set ℤ)), ∃ r, compress (b :: t) = b :: r
  | b, [] => ⟨[], rfl⟩
  | b, c :: t => by
    simp only [compress]
    split_ifs with h
    · subst h; exact compress_cons_head b t
    · exact ⟨_, rfl⟩

/-- Compressing a list (deleting consecutive repetitions) does not change its layer sum. -/
lemma laySum_compress (J : Set ℤ) : ∀ l : List (Set ℤ), layerSum (compress l) J = layerSum l J
  | [] => rfl
  | [_] => rfl
  | b :: c :: t => by
    have ih := laySum_compress J (c :: t)
    simp only [compress]
    split_ifs with h
    · subst h; rw [ih, laySum_cons_cons]; simp
    · obtain ⟨r, hr⟩ := compress_cons_head c t
      rw [hr, laySum_cons_cons, ← hr, ih, laySum_cons_cons]

/-- The layer sum as a finite sum over the positions of the list. -/
lemma laySum_getD (J : Set ℤ) : ∀ l : List (Set ℤ),
    layerSum l J = ∑ k ∈ Finset.range l.length, ((l.getD k ∅ \ l.getD (k + 1) ∅) ∩ J).ncard / 2
  | [] => by simp [layerSum, layers]
  | [a] => by simp [layerSum, layers]
  | a :: b :: t => by
    rw [laySum_cons_cons, laySum_getD J (b :: t),
      show (a :: b :: t).length = (b :: t).length + 1 from rfl,
      Finset.sum_range_succ' _ ((b :: t).length)]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    omega


/-! ### Forest paths -/

lemma dropWhile_head (a : ℕ) : ∀ (l : List ℕ), a ∈ l → ∃ r, l.dropWhile (· ≠ a) = a :: r
  | [], h => absurd h List.not_mem_nil
  | x :: l, h => by
    by_cases hx : x = a
    · subst hx; exact ⟨l, by simp⟩
    · have h' : a ∈ l := by rcases List.mem_cons.1 h with h | h; exact absurd h.symm hx; exact h
      obtain ⟨r, hr⟩ := dropWhile_head a l h'
      exact ⟨r, by rw [List.dropWhile_cons_of_pos (by simpa using hx), hr]⟩

lemma mem_dropWhile_iff (a x : ℕ) : ∀ (l : List ℕ), l.Pairwise (· < ·) → a ∈ l →
    (x ∈ l.dropWhile (· ≠ a) ↔ x ∈ l ∧ a ≤ x)
  | [], _, h => absurd h List.not_mem_nil
  | y :: l, hp, h => by
    rw [List.pairwise_cons] at hp
    by_cases hy : y = a
    · subst hy
      simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, not_false_eq_true,
        List.dropWhile_cons_of_neg, List.mem_cons]
      constructor
      · rintro (rfl | hx)
        · exact ⟨Or.inl rfl, le_rfl⟩
        · exact ⟨Or.inr hx, (hp.1 x hx).le⟩
      · exact fun h => h.1
    · have h' : a ∈ l := by rcases List.mem_cons.1 h with h | h; exact absurd h.symm hy; exact h
      have hya := hp.1 a h'
      rw [List.dropWhile_cons_of_pos (by simpa using hy), mem_dropWhile_iff a x l hp.2 h',
        List.mem_cons]
      constructor
      · exact fun h => ⟨Or.inr h.1, h.2⟩
      · rintro ⟨rfl | hx, hax⟩
        · omega
        · exact ⟨hx, hax⟩

lemma dropWhile_pairwise (a : ℕ) : ∀ (l : List ℕ), l.Pairwise (· < ·) →
    (l.dropWhile (· ≠ a)).Pairwise (· < ·)
  | [], _ => by simp
  | y :: l, hp => by
    rw [List.dropWhile_cons]
    split_ifs
    · exact dropWhile_pairwise a l (List.pairwise_cons.1 hp).2
    · exact hp

/-- The vertex path from `a` to `v` (when `a ⪯ v`). -/
noncomputable def pathV (R : Requirements) (C : Choices) (a v : ℕ) : List ℕ :=
  (vdata R C v).anc.dropWhile (· ≠ a)

/-- `ForestAux.uniform_board_gen` (the first conjunct of Lemma 6.14, a pairing-score bound) in
`layerSum` form: rewritten on the uncompressed vertex path and multiplied out by the board size. -/
lemma uniform_board_laySum (hX : LangClass X) (hS : ForestAux.Good X R) (hC : C.Valid X R) :
    ∀ v, R.isV v → ∀ a, IsAnc R C a v → ∀ x,
      max 0 (R.s a - 1 / R.N a) * ((R.lab a ∩ boardOf R C a x).ncard : ℝ) ≤
        (layerSum ((pathV R C a v).map R.lab) (R.lab a ∩ boardOf R C a x) : ℝ) := by
  intro v hv a ha x
  have h := ForestAux.uniform_board_gen hX hS hC hv ha x
  have haV := ConstructionAux.isV_of_anc R C v hv a ha
  obtain ⟨-, hN, -⟩ := ForestAux.board_spec hX hS.lab_mem hS.N_pos hC a haV x
  have hN1 := hS.N_pos a haV
  have hpos : (0 : ℝ) < ((R.lab a ∩ boardOf R C a x).ncard : ℝ) := by
    have : 0 < (R.lab a ∩ boardOf R C a x).ncard := by omega
    exact_mod_cast this
  rw [score_eq, ConstructionAux.pathChain_eq_readChain, ConstructionAux.readChain, laySum_compress, one_div_mul_eq_div, le_div_iff₀ hpos] at h
  exact h

lemma getD_anti {labs : List (Set ℤ)} (hdesc : ∀ k, labs.getD (k + 1) ∅ ⊆ labs.getD k ∅)
    {k k' : ℕ} (h : k ≤ k') : labs.getD k' ∅ ⊆ labs.getD k ∅ := by
  induction k', h using Nat.le_induction with
  | base => exact Subset.rfl
  | succ k' _ ih => exact (hdesc k').trans ih

lemma card_filter_mem (Bd : Finset ℤ) (E : Set ℤ) :
    (Bd.filter (fun y => y ∈ E)).card = (E ∩ (Bd : Set ℤ)).ncard := by
  rw [← ncard_coe_finset, Finset.coe_filter]
  congr 1; ext y; simp [and_comm]

/-- The local pairing game (Lemma 6.18) on the rounds of an enumeration: the visible set on a
round with input in `Bd` is the trace of a level `lev t` of a descending list of languages, the
levels move up, and the algorithm responds inside the visible set when it can. Then the layer sum
of `labs` over `Bd` is at most the number of outputs in `Bd`. -/
lemma game_abstract (Bd : Finset ℤ) (labs : List (Set ℤ))
    (hdesc : ∀ k, labs.getD (k + 1) ∅ ⊆ labs.getD k ∅)
    (hBd : ∀ y ∈ Bd, y ∈ labs.getD 0 ∅)
    (inp outp : ℕ → ℤ)
    (havail_in : ∀ t, ∀ i ≤ t, inp i ≠ outp t) (havail_out : ∀ t, ∀ s < t, outp s ≠ outp t)
    (hcov : ∀ y ∈ Bd, ∃ s, inp s = y)
    (lev : ℕ → ℕ)
    (hlev : ∀ t, inp t ∈ Bd → lev t < labs.length ∧ inp t ∈ labs.getD (lev t) ∅)
    (hmono : ∀ t t', t ≤ t' → inp t ∈ Bd → inp t' ∈ Bd → lev t' ≤ lev t)
    (hresp : ∀ t, inp t ∈ Bd → (∃ y ∈ Bd, y ∈ labs.getD (lev t) ∅ ∧ (∀ i ≤ t, inp i ≠ y) ∧
        ∀ s < t, outp s ≠ y) → outp t ∈ Bd ∧ outp t ∈ labs.getD (lev t) ∅) :
    layerSum labs (Bd : Set ℤ) ≤ (Bd.filter (fun y => ∃ t, outp t = y)).card := by
  -- the last round needed
  let fs : ℤ → ℕ := fun y => if h : ∃ s, inp s = y then Nat.find h else 0
  set tE := Bd.sup fs with htE
  have hfs : ∀ y ∈ Bd, inp (fs y) = y ∧ fs y ≤ tE := by
    intro y hy
    have h := hcov y hy
    refine ⟨?_, Finset.le_sup (f := fs) hy⟩
    show inp (if h : ∃ s, inp s = y then Nat.find h else 0) = y
    rw [dif_pos h]; exact Nat.find_spec h
  let p : ℕ → Prop := fun r => inp r ∈ Bd ∧ r ≤ tE
  have hf : (Set.ofPred p).Finite := (Set.finite_Iic tE).subset fun r hr => hr.2
  set T := (hf.toFinset).card with hT
  let rr : ℕ → ℕ := fun j => if j < T then Nat.nth p j else tE + 1
  have hrr_p : ∀ j < T, p (rr j) := fun j hj => by
    simp only [rr, hj, ↓reduceIte]; exact Nat.nth_mem_of_lt_card hf hj
  have hrr_le : ∀ j, rr j ≤ tE + 1 := fun j => by
    by_cases hj : j < T
    · have := (hrr_p j hj).2; omega
    · simp only [rr, hj, ↓reduceIte]; exact le_rfl
  have hkey : ∀ s, p s → ∀ j ≤ T, (s < rr j ↔ Nat.count p s < j) := by
    intro s hs j hj
    have hc := Nat.count_lt_card hf hs
    have hn := Nat.nth_count hs
    by_cases hjT : j < T
    · simp only [rr, hjT, ↓reduceIte]
      constructor
      · intro h
        by_contra h'; push Not at h'
        have := Nat.nth_le_nth_of_lt_card hf h' hc
        rw [hn] at this; omega
      · intro h
        have := Nat.nth_lt_nth_of_lt_card hf h hjT
        rwa [hn] at this
    · have hjT' : j = T := by omega
      simp only [rr, hjT, ↓reduceIte]
      constructor
      · intro _; omega
      · intro _; have := hs.2; omega
  have hrr_mono : ∀ j j', j ≤ j' → rr j ≤ rr j' := by
    intro j j' h
    by_cases hj' : j' < T
    · have hj : j < T := by omega
      simp only [rr, hj, hj', ↓reduceIte]
      exact Nat.nth_le_nth_of_lt_card hf h hj'
    · simp only [rr, hj', ↓reduceIte]; exact hrr_le j
  have hrr_lt : ∀ j < T, rr j < rr (j + 1) := by
    intro j hj
    by_cases hj' : j + 1 < T
    · simp only [rr, hj, hj', ↓reduceIte]
      exact Nat.nth_lt_nth_of_lt_card hf (Nat.lt_succ_self j) hj'
    · have h2 : Nat.nth p j ≤ tE := by
        have := (hrr_p j hj).2; simpa [rr, hj] using this
      simp only [rr, hj, hj', ↓reduceIte]; omega
  have hrr_nth : ∀ s, p s → rr (Nat.count p s) = s := by
    intro s hs
    have hc : Nat.count p s < T := Nat.count_lt_card hf hs
    simp only [rr, hc, ↓reduceIte]; exact Nat.nth_count hs
  -- inputs in `Bd` before `rr j`
  have hinp_before : ∀ j ≤ T, ∀ s, inp s ∈ Bd → s < rr j → Nat.count p s < j := by
    intro j hj s hs hlt
    have hps : p s := ⟨hs, by have := hrr_le j; omega⟩
    exact (hkey s hps j hj).1 hlt
  set m := labs.length with hm
  let Y : ℕ → Finset ℤ := fun i => Bd.filter (fun y => y ∈ labs.getD (m - i) ∅)
  let stage : ℕ → ℕ := fun j => if j < T then m - lev (rr j) else m
  let a : ℕ → ℤ := fun j => inp (rr j)
  let W : ℕ → Finset ℤ := fun j => Bd.filter (fun y => ∃ s < rr j, outp s = y)
  let Bl : ℕ → Finset ℤ := fun j =>
    Bd.filter (fun y => (∃ s < rr j, inp s = y) ∧ ¬ ∃ s < rr j, outp s = y)
  have hYm_eq : ∀ j < T, Y (stage j) = Bd.filter (fun y => y ∈ labs.getD (lev (rr j)) ∅) := by
    intro j hj
    have hl := (hlev (rr j) (hrr_p j hj).1).1
    simp only [Y, stage, hj, ↓reduceIte]
    congr 2; ext y; rw [show m - (m - lev (rr j)) = lev (rr j) by omega]
  have hgame := lem_pairing_game Bd m Y
    (by
      simp only [Y, Nat.sub_zero]
      ext y
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro _
      rw [List.getD_eq_default _ _ (le_of_eq hm)]
      exact id)
    (by
      intro i i' h y
      simp only [Y, Finset.mem_filter]
      exact fun hy => ⟨hy.1, getD_anti hdesc (by omega) hy.2⟩)
    (by
      simp only [Y, Nat.sub_self]
      ext y; simp only [Finset.mem_filter, and_iff_left_iff_imp]; exact hBd y)
    T stage
    (by
      intro j j' h
      simp only [stage]
      by_cases hj' : j' < T
      · have hj : j < T := by omega
        rw [if_pos hj, if_pos hj']
        have := hmono (rr j) (rr j') (hrr_mono j j' h) (hrr_p j hj).1 (hrr_p j' hj').1
        omega
      · rw [if_neg hj']; split_ifs <;> omega)
    (by intro j; simp only [stage]; split_ifs <;> omega)
    a
    (by
      intro j hj
      rw [hYm_eq j hj, Finset.mem_filter]
      exact ⟨(hrr_p j hj).1, (hlev (rr j) (hrr_p j hj).1).2⟩)
    W Bl
    (by
      ext y
      simp only [Bl, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      rintro hy ⟨s, hs, rfl⟩
      have := hinp_before 0 (Nat.zero_le _) s hy hs
      omega)
    (Finset.filter_subset _ _)
    (by
      intro j hj
      ext y
      simp only [a]
      have hp := hrr_p j hj
      -- inputs before `rr (j+1)`
      have hin : y ∈ Bd → ((∃ s < rr (j + 1), inp s = y) ↔
          (∃ s < rr j, inp s = y) ∨ y = inp (rr j)) := by
        intro hy
        constructor
        · rintro ⟨s, hs, rfl⟩
          have hc := hinp_before (j + 1) (by omega) s hy hs
          rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | hc
          · left
            have hps : p s := ⟨hy, by have := hrr_le (j + 1); omega⟩
            exact ⟨s, (hkey s hps j hj.le).2 hc, rfl⟩
          · right
            have hps : p s := ⟨hy, by have := hrr_le (j + 1); omega⟩
            have := hrr_nth s hps
            rw [hc] at this; rw [this]
        · rintro (⟨s, hs, rfl⟩ | rfl)
          · exact ⟨s, hs.trans (hrr_lt j hj), rfl⟩
          · exact ⟨rr j, hrr_lt j hj, rfl⟩
      have hout : (∃ i ≤ rr j, inp i = y) → ((∃ s < rr (j + 1), outp s = y) ↔
          (∃ s < rr j, outp s = y)) := by
        rintro ⟨i, hi, rfl⟩
        constructor
        · rintro ⟨s, hs, hse⟩
          by_cases hsj : s < rr j
          · exact ⟨s, hsj, hse⟩
          · exact absurd hse.symm (havail_in s i (by omega))
        · rintro ⟨s, hs, hse⟩; exact ⟨s, hs.trans (hrr_lt j hj), hse⟩
      have haB : inp (rr j) ∈ Bd := hp.1
      have hR : y ∈ (if inp (rr j) ∈ W j then Bl j else insert (inp (rr j)) (Bl j)) ↔
          (y ∈ Bd ∧ (∃ s < rr j, inp s = y) ∧ ¬∃ s < rr j, outp s = y) ∨
          (y = inp (rr j) ∧ ¬ ∃ s < rr j, outp s = inp (rr j)) := by
        split_ifs with hw
        · simp only [W, Finset.mem_filter] at hw
          simp only [Bl, Finset.mem_filter]
          constructor
          · intro h; exact Or.inl h
          · rintro (h | ⟨rfl, h⟩)
            · exact h
            · exact absurd hw.2 h
        · simp only [W, Finset.mem_filter, not_and] at hw
          simp only [Finset.mem_insert, Bl, Finset.mem_filter]
          constructor
          · rintro (rfl | h)
            · exact Or.inr ⟨rfl, hw haB⟩
            · exact Or.inl h
          · rintro (h | ⟨rfl, -⟩)
            · exact Or.inr h
            · exact Or.inl rfl
      rw [hR]
      simp only [Bl, Finset.mem_filter]
      by_cases hyB : y ∈ Bd
      swap
      · constructor
        · rintro ⟨h, -⟩; exact absurd h hyB
        · rintro (⟨h, -⟩ | ⟨rfl, -⟩)
          · exact absurd h hyB
          · exact absurd haB hyB
      rw [hin hyB]
      constructor
      · rintro ⟨-, (⟨s, hs, e⟩ | rfl), hno⟩
        · exact Or.inl ⟨hyB, ⟨s, hs, e⟩, fun ho => hno ((hout ⟨s, hs.le, e⟩).2 ho)⟩
        · exact Or.inr ⟨rfl, fun ho => hno ((hout ⟨rr j, le_rfl, rfl⟩).2 ho)⟩
      · rintro (⟨-, ⟨s, hs, e⟩, hno⟩ | ⟨rfl, hno⟩)
        · exact ⟨hyB, Or.inl ⟨s, hs, e⟩, fun ho => hno ((hout ⟨s, hs.le, e⟩).1 ho)⟩
        · exact ⟨hyB, Or.inr rfl, fun ho => hno ((hout ⟨rr j, le_rfl, rfl⟩).1 ho)⟩)
    (by
      intro j hj y
      simp only [W, Finset.mem_filter]
      rintro ⟨hy, s, hs, e⟩
      exact ⟨hy, s, hs.trans_le (hrr_mono j (j + 1) (Nat.le_succ j)), e⟩)
    (fun j _ => Finset.filter_subset _ _)
    (by
      intro j _
      rw [Finset.disjoint_left]
      intro y hy hy'
      simp only [W, Bl, Finset.mem_filter] at hy hy'
      exact hy'.2.2 hy.2)
    (by
      intro j hj ⟨x, hxY, hxW, hxB⟩
      have hp := hrr_p j hj
      set t := rr j
      rw [hYm_eq j hj, Finset.mem_filter] at hxY
      have hprem : ∃ y ∈ Bd, y ∈ labs.getD (lev t) ∅ ∧ (∀ i ≤ t, inp i ≠ y) ∧
          ∀ s < t, outp s ≠ y := by
        refine ⟨x, hxY.1, hxY.2, ?_, ?_⟩
        · intro i hi e
          apply hxB
          simp only [Bl, Finset.mem_filter]
          refine ⟨hxY.1, ⟨i, by have := hrr_lt j hj; omega, e⟩, ?_⟩
          rintro ⟨s, hs, hse⟩
          by_cases hst : s < t
          · exact hxW (Finset.mem_filter.2 ⟨hxY.1, s, hst, hse⟩)
          · exact havail_in s i (by omega) (e.trans hse.symm)
        · intro s hs e
          exact hxW (Finset.mem_filter.2 ⟨hxY.1, s, hs, e⟩)
      obtain ⟨ho1, ho2⟩ := hresp t hp.1 hprem
      refine ⟨outp t, ?_, ?_, ?_, ?_⟩
      · rw [hYm_eq j hj, Finset.mem_filter]; exact ⟨ho1, ho2⟩
      · simp only [W, Finset.mem_filter, not_and, not_exists]
        intro _ s hs e
        exact havail_out t s hs e
      · simp only [Bl, Finset.mem_filter, not_and, not_not]
        intro _ _
        exact ⟨t, hrr_lt j hj, rfl⟩
      · simp only [W, Finset.mem_filter]
        exact ⟨ho1, t, hrr_lt j hj, rfl⟩)
    (by
      intro x hx
      obtain ⟨h1, h2⟩ := hfs x hx
      have hps : p (fs x) := ⟨by rw [h1]; exact hx, h2⟩
      refine ⟨Nat.count p (fs x), Nat.count_lt_card hf hps, ?_⟩
      simp only [a]; rw [hrr_nth _ hps, h1])
  -- the sum is the layer sum
  have hsum : ∑ i ∈ Finset.range m, (Y (i + 1) \ Y i).card / 2 = layerSum labs (Bd : Set ℤ) := by
    rw [laySum_getD, ← hm, ← Finset.sum_range_reflect
      (fun k => ((labs.getD k ∅ \ labs.getD (k + 1) ∅) ∩ (Bd : Set ℤ)).ncard / 2) m]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    have e : Y (i + 1) \ Y i = Bd.filter (fun y => y ∈ labs.getD (m - 1 - i) ∅ \
        labs.getD (m - 1 - i + 1) ∅) := by
      ext y
      simp only [Y, Finset.mem_sdiff, Finset.mem_filter, Set.mem_sdiff]
      rw [show m - (i + 1) = m - 1 - i by omega, show m - i = m - 1 - i + 1 by omega]
      tauto
    rw [e]; congr 1; convert card_filter_mem Bd _
  have hW : (W T).card ≤ (Bd.filter (fun y => ∃ t, outp t = y)).card := by
    refine Finset.card_le_card fun y hy => ?_
    simp only [W, Finset.mem_filter] at hy ⊢
    obtain ⟨hy, s, -, e⟩ := hy
    exact ⟨hy, s, e⟩
  omega


/-! ### Rounds, records and the serving scan -/

lemma inputsUpTo_length (w : ℕ → ℤ) (t : ℕ) : (inputsUpTo w t).length = t + 1 := by
  simp [inputsUpTo]

lemma mem_inputsUpTo_iff (w : ℕ → ℤ) (t : ℕ) (y : ℤ) :
    y ∈ inputsUpTo w t ↔ ∃ s ≤ t, w s = y := by
  simp only [inputsUpTo, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨i, by omega, rfl⟩
  · rintro ⟨s, hs, rfl⟩; exact ⟨⟨s, by omega⟩, rfl⟩

/-- Membership in the record history up to round `t`: a guess `y` at some round `r ≤ t`, with
`v ⪯ y` and the input of round `r` in `I`. -/
lemma mem_recordHistory_iff (w : ℕ → ℤ) (t v : ℕ) (I : Set ℤ) (y : ℕ) :
    y ∈ recordHistory R C (inputsUpTo w t) v I ↔
      ∃ r ≤ t, guess R (inputsUpTo w r) = some y ∧ IsAnc R C v y ∧ w r ∈ I := by
  simp only [recordHistory, mem_ofPred_eq, inputsUpTo_length]
  constructor
  · rintro ⟨r, hr, hg, ha, hI⟩
    rw [BasicAux.inputsUpTo_take w (by omega)] at hg
    rw [CaptureAux.inputsUpTo_getD w (by omega)] at hI
    exact ⟨r, by omega, hg, ha, hI⟩
  · rintro ⟨r, hr, hg, ha, hI⟩
    refine ⟨r, by omega, ?_, ha, ?_⟩
    · rw [BasicAux.inputsUpTo_take w hr]; exact hg
    · rw [CaptureAux.inputsUpTo_getD w hr]; exact hI

/-- The outputs before round `t` are the generator's outputs at rounds `s < t`. -/
lemma mem_prevOuts_iff (w : ℕ → ℤ) : ∀ t (y : ℤ),
    y ∈ algOutputs R C (inputsUpTo w t).dropLast ↔ ∃ s < t, (algGen R C).out w s = y
  | 0, y => by
    have : (inputsUpTo w 0).dropLast = [] := by simp [inputsUpTo]
    rw [this, ConstructionAux.algOutputs_nil]; simp
  | t + 1, y => by
    have ih := mem_prevOuts_iff w t y
    rw [ConstructionAux.inputsUpTo_dropLast,
      ConstructionAux.algOutputs_eq R C (ConstructionAux.inputsUpTo_ne_nil w t),
      ← ConstructionAux.algGen_out, List.mem_append, ih, List.mem_singleton]
    constructor
    · rintro (⟨s, hs, e⟩ | e)
      · exact ⟨s, by omega, e⟩
      · exact ⟨t, by omega, e.symm⟩
    · rintro ⟨s, hs, e⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
      · exact Or.inl ⟨s, hs, e⟩
      · exact Or.inr e.symm

lemma lca_anti {S S' : Set ℕ} (hSS : S ⊆ S') {y₀ v : ℕ} (hy₀ : y₀ ∈ S)
    (hv : ∀ y ∈ S', IsAnc R C v y) : IsAnc R C (lca R C S') (lca R C S) := by
  have h' := CaptureAux.lca_spec (hSS hy₀) hv
  have h := CaptureAux.lca_spec hy₀ (fun y hy => hv y (hSS hy))
  have hbdd : BddAbove {a | ∀ y ∈ S, IsAnc R C a y} :=
    ⟨y₀, fun a ha => (CaptureAux.isAnc_le _ _ (ha y₀ hy₀)).1⟩
  have hle : lca R C S' ≤ lca R C S := le_csSup hbdd fun y hy => h'.1 y (hSS hy)
  exact CaptureAux.isAnc_of_le _ _ _ (h'.1 y₀ (hSS hy₀)) (h.1 y₀ hy₀) hle

lemma idxOf_mono {a b : ℕ} : ∀ (l : List ℕ), l.Pairwise (· < ·) → a ∈ l → b ∈ l → a ≤ b →
    l.idxOf a ≤ l.idxOf b
  | [], _, h, _, _ => absurd h List.not_mem_nil
  | y :: l, hp, ha, hb, hab => by
    rw [List.pairwise_cons] at hp
    by_cases hya : y = a
    · rw [List.idxOf_cons_eq _ hya]; exact Nat.zero_le _
    · have ha' : a ∈ l := by
        rcases List.mem_cons.1 ha with h | h; exact absurd h.symm hya; exact h
      have hyb : y ≠ b := by have := hp.1 a ha'; omega
      have hb' : b ∈ l := by
        rcases List.mem_cons.1 hb with h | h; exact absurd h.symm hyb; exact h
      rw [List.idxOf_cons_ne _ hya, List.idxOf_cons_ne _ hyb]
      exact Nat.succ_le_succ (idxOf_mono l hp.2 ha' hb' hab)

lemma getD_map_idxOf (P : List ℕ) {Z : ℕ} (hZ : Z ∈ P) :
    (P.map R.lab).getD (P.idxOf Z) ∅ = R.lab Z := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hZ), List.getElem_idxOf]
  rfl

lemma getD_map_desc (P : List ℕ) (hP : P.Pairwise (· < ·)) {Q : ℕ}
    (hPQ : ∀ y ∈ P, IsAnc R C y Q) (k : ℕ) :
    (P.map R.lab).getD (k + 1) ∅ ⊆ (P.map R.lab).getD k ∅ := by
  by_cases hk : k + 1 < P.length
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_map, List.getElem?_eq_getElem hk, List.getElem?_eq_getElem (by omega)]
    simp only [Option.map_some, Option.getD_some]
    have hlt : P[k] < P[k + 1] := List.pairwise_iff_getElem.1 hP k (k + 1) (by omega) hk
      (Nat.lt_succ_self k)
    exact (CaptureAux.isAnc_le _ _ (CaptureAux.isAnc_of_le _ _ _ (hPQ _ (List.getElem_mem _))
      (hPQ _ (List.getElem_mem _)) hlt.le)).2
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    exact empty_subset _

/-- History inclusion (the argument of Lemma 6.15) together with regularity: on a round whose
input lies in a regular `z`-board, the pod of an ancestor `u ⪯ z` lies in the pod of `z`. -/
lemma pod_sub (hX : LangClass X) (hS : ForestAux.Good X R) (hC : C.Valid X R) {z : ℕ}
    (hz : R.isV z) {w : ℕ → ℤ} {t₀ : ℕ}
    (ht₀ : ∀ t ≥ t₀, ∃ Q, guess R (inputsUpTo w t) = some Q ∧ IsAnc R C z Q) (x : ℤ)
    (hreg : ¬ Exceptional R C w z t₀ (boardOf R C z x)) {t u Q : ℕ}
    (ht : w t ∈ boardOf R C z x) (hQ : guess R (inputsUpTo w t) = some Q)
    (hzQ : IsAnc R C z Q) (huz : IsAnc R C u z) :
    pod R C (inputsUpTo w t) u ⊆ pod R C (inputsUpTo w t) z := by
  have hIz : boardOf R C z (w t) = boardOf R C z x := ConstructionAux.cutBoard_eq_of_mem ht
  set Iu := boardOf R C u (w t) with hIu
  have hIuI : Iu ⊆ boardOf R C z (w t) := CaptureAux.board_sub hX hS.lab_mem hS.N_pos hC hz huz (w t)
  have hU : ∀ y ∈ recordHistory R C (inputsUpTo w t) u Iu, IsAnc R C z y := by
    intro y hy
    obtain ⟨r, hr, hg, huy, hI⟩ := (mem_recordHistory_iff w t u Iu y).1 hy
    by_cases hrt : r < t₀
    · exfalso
      apply hreg
      refine Or.inr ⟨u, huz, r, hrt, y, hg, huy, ?_⟩
      have : boardOf R C u (w r) = Iu := ConstructionAux.cutBoard_eq_of_mem hI
      rw [this, ← hIz]; exact hIuI
    · obtain ⟨Q', hQ', hzQ'⟩ := ht₀ r (by omega)
      rw [hg] at hQ'; cases hQ'; exact hzQ'
  have hQmem : Q ∈ recordHistory R C (inputsUpTo w t) u Iu :=
    (mem_recordHistory_iff w t u Iu Q).2 ⟨t, le_rfl, hQ, CaptureAux.isAnc_trans _ _ _ huz hzQ,
      ConstructionAux.mem_cutBoard_self _ _⟩
  have hsub : recordHistory R C (inputsUpTo w t) u Iu ⊆
      recordHistory R C (inputsUpTo w t) z (boardOf R C z (w t)) := by
    intro y hy
    obtain ⟨r, hr, hg, -, hI⟩ := (mem_recordHistory_iff w t u Iu y).1 hy
    exact (mem_recordHistory_iff w t z _ y).2 ⟨r, hr, hg, hU y hy, hIuI hI⟩
  have hanc := lca_anti hsub hQmem (v := z) fun y hy =>
    ((mem_recordHistory_iff w t z _ y).1 hy).choose_spec.2.2.1
  intro y hy
  simp only [pod, CaptureAux.inputsUpTo_getLastD] at hy ⊢
  exact ⟨hIuI hy.1, (CaptureAux.isAnc_le _ _ hanc).2 hy.2⟩

/-- The serving scan on a round whose input lies in a regular `z`-board: if the pod of `z` has
an available point, the output lies in the pod of `z`. -/
lemma out_mem_pod (hX : LangClass X) (hS : ForestAux.Good X R) (hC : C.Valid X R) {z : ℕ}
    (hz : R.isV z) {w : ℕ → ℤ} {t₀ : ℕ}
    (ht₀ : ∀ t ≥ t₀, ∃ Q, guess R (inputsUpTo w t) = some Q ∧ IsAnc R C z Q) (x : ℤ)
    (hreg : ¬ Exceptional R C w z t₀ (boardOf R C z x)) {t Q : ℕ}
    (ht : w t ∈ boardOf R C z x) (hQ : guess R (inputsUpTo w t) = some Q)
    (hzQ : IsAnc R C z Q)
    (hne : (pod R C (inputsUpTo w t) z \ {y | y ∈ inputsUpTo w t ∨
      y ∈ algOutputs R C (inputsUpTo w t).dropLast}).Nonempty) :
    (algGen R C).out w t ∈ pod R C (inputsUpTo w t) z := by
  set ws := inputsUpTo w t
  set used : Set ℤ := {y | y ∈ ws ∨ y ∈ algOutputs R C ws.dropLast}
  obtain ⟨rest, hrest⟩ := anc_prefix hzQ
  have hfind : ∃ v, (vdata R C Q).anc.find? (fun v => decide ((pod R C ws v \ used).Nonempty)) =
      some v ∧ IsAnc R C v z := by
    rw [← hrest, List.find?_append]
    rcases h : (vdata R C z).anc.find? (fun v => decide ((pod R C ws v \ used).Nonempty))
      with _ | v
    · exfalso
      rw [List.find?_eq_none] at h
      exact h z (ForestAux.self_mem_anc R C z) (by simpa using hne)
    · exact ⟨v, by simp, List.mem_of_find?_eq_some h⟩
  obtain ⟨v, hv, hvz⟩ := hfind
  have hvp := List.find?_some hv
  rw [ConstructionAux.algGen_out]
  have heq : algStep R C ws (algOutputs R C ws.dropLast) = C.pick (pod R C ws v) used := by
    have hv' : List.find? (fun v => decide (pod R C ws v \
        {x | x ∈ ws ∨ x ∈ algOutputs R C ws.dropLast}).Nonempty) (vdata R C Q).anc = some v := hv
    simp only [algStep, hQ, hv']; rfl
  rw [heq]
  have hmem := hC.pick_spec _ used (of_decide_eq_true hvp)
  exact pod_sub hX hS hC hz ht₀ x hreg ht hQ hzQ hvz hmem.1

/-- Generic form of Corollary 6.19 (regular boards), for any system satisfying `GoodSystem`. -/
theorem regular_board_gen (hX : LangClass X) (hS : GoodSystem X R) (hC : C.Valid X R)
    {z : ℕ} (hz : R.isV z) {w : ℕ → ℤ} (hw : IsFullEnumeration w (R.lab z)) {t₀ : ℕ}
    (ht₀ : ∀ t ≥ t₀, ∃ Q, guess R (inputsUpTo w t) = some Q ∧ IsAnc R C z Q) (x : ℤ)
    (hreg : ¬ Exceptional R C w z t₀ (boardOf R C z x)) :
    R.q z * ((R.lab z ∩ boardOf R C z x).ncard : ℝ) ≤
      (((algGen R C).outputSet w ∩ R.lab z ∩ boardOf R C z x).ncard : ℝ) := by
  set K := R.lab z with hK
  set I := boardOf R C z x with hI
  have hJfin : (K ∩ I).Finite := (ForestAux.board_spec hX hS.lab_mem hS.N_pos hC z hz x).1
  have hwK : ∀ r, w r ∈ K := fun r => hw ▸ mem_range_self r
  -- rounds with input in `I` are post-capture
  have hlate : ∀ r, w r ∈ I → t₀ ≤ r := by
    intro r hr
    by_contra h
    exact hreg (Or.inl ⟨r, by omega, Or.inl ⟨hwK r, hr⟩⟩)
  have hguess : ∀ r, w r ∈ I → ∃ Q, guess R (inputsUpTo w r) = some Q ∧ IsAnc R C z Q :=
    fun r hr => ht₀ r (hlate r hr)
  rcases (K ∩ I).eq_empty_or_nonempty with hJe | ⟨y₀, hy₀⟩
  · rw [hJe, ncard_empty]; simp only [Nat.cast_zero, mul_zero]; positivity
  have hex : ∃ r, w r ∈ I := by
    obtain ⟨r, hr⟩ : y₀ ∈ range w := hw ▸ hy₀.1
    exact ⟨r, hr ▸ hy₀.2⟩
  set t1 := Nat.find hex with ht1
  have ht1I : w t1 ∈ I := Nat.find_spec hex
  have ht1min : ∀ r, w r ∈ I → t1 ≤ r := fun r hr => Nat.find_min' hex hr
  obtain ⟨Q1, hQ1, hzQ1⟩ := hguess t1 ht1I
  have hQ1V : R.isV Q1 := (ConstructionAux.guess_critical hQ1).1.1
  -- the target record
  let hist : ℕ → Set ℕ := fun t => recordHistory R C (inputsUpTo w t) z I
  let Z : ℕ → ℕ := fun t => record R C (inputsUpTo w t) z I
  have hzhist : ∀ t, ∀ y ∈ hist t, IsAnc R C z y := fun t y hy =>
    ((mem_recordHistory_iff w t z I y).1 hy).choose_spec.2.2.1
  have hQ1hist : ∀ t, t1 ≤ t → Q1 ∈ hist t := fun t ht =>
    (mem_recordHistory_iff w t z I Q1).2 ⟨t1, ht, hQ1, hzQ1, ht1I⟩
  have hZspec : ∀ t, t1 ≤ t → (∀ y ∈ hist t, IsAnc R C (Z t) y) ∧ IsAnc R C z (Z t) :=
    fun t ht => (CaptureAux.lca_spec (hQ1hist t ht) (hzhist t)).imp_right And.left
  have hZmono : ∀ t t', t1 ≤ t → t ≤ t' → IsAnc R C (Z t') (Z t) := by
    intro t t' ht htt'
    refine lca_anti (S := hist t) (S' := hist t') ?_ (hQ1hist t ht) (hzhist t')
    intro y hy
    obtain ⟨r, hr, h1, h2, h3⟩ := (mem_recordHistory_iff w t z I y).1 hy
    exact (mem_recordHistory_iff w t' z I y).2 ⟨r, hr.trans htt', h1, h2, h3⟩
  -- the vertex path from `z` to `Q1`
  set P := pathV R C z Q1 with hP
  have hPpw : P.Pairwise (· < ·) := dropWhile_pairwise z _ (anc_pairwise Q1)
  have hmemP : ∀ y, y ∈ P ↔ IsAnc R C y Q1 ∧ z ≤ y := fun y =>
    mem_dropWhile_iff z y _ (anc_pairwise Q1) hzQ1
  have hZP : ∀ t, t1 ≤ t → Z t ∈ P := fun t ht =>
    (hmemP _).2 ⟨(hZspec t ht).1 Q1 (hQ1hist t ht), (CaptureAux.isAnc_le _ _ (hZspec t ht).2).1⟩
  obtain ⟨rP, hrP⟩ := dropWhile_head z _ hzQ1
  set labs := P.map R.lab with hlabs
  have hdesc := getD_map_desc P hPpw (Q := Q1) fun y hy => ((hmemP y).1 hy).1
  set Bd := hJfin.toFinset with hBd
  have hBdc : (Bd : Set ℤ) = K ∩ I := hJfin.coe_toFinset
  have hmemBd : ∀ y, y ∈ Bd ↔ y ∈ K ∧ y ∈ I := fun y => hJfin.mem_toFinset
  have hadm := ConstructionAux.algGen_admissible hX hS.lab_mem hC
  have hgame := game_abstract Bd labs hdesc
    (by
      intro y hy
      have : labs.getD 0 ∅ = K := by
        show (P.map R.lab).getD 0 ∅ = R.lab z
        rw [hP, pathV, hrP]; rfl
      rw [this]; exact ((hmemBd y).1 hy).1)
    w ((algGen R C).out w)
    (fun t i hi => (hadm w t).1 i hi) (fun t s hs => (hadm w t).2 s hs)
    (by
      intro y hy
      obtain ⟨r, hr⟩ : y ∈ range w := hw ▸ ((hmemBd y).1 hy).1
      exact ⟨r, hr⟩)
    (fun t => P.idxOf (Z t))
    (by
      intro t ht
      have htI := ((hmemBd _).1 ht).2
      have ht1t := ht1min t htI
      refine ⟨by rw [hlabs, List.length_map]; exact List.idxOf_lt_length_of_mem (hZP t ht1t), ?_⟩
      show w t ∈ (P.map R.lab).getD (P.idxOf (Z t)) ∅
      rw [getD_map_idxOf P (hZP t ht1t)]
      obtain ⟨Q, hQ, hzQ⟩ := hguess t htI
      have hQh : Q ∈ hist t := (mem_recordHistory_iff w t z I Q).2 ⟨t, le_rfl, hQ, hzQ, htI⟩
      refine (CaptureAux.isAnc_le _ _ ((hZspec t ht1t).1 Q hQh)).2 ?_
      exact (ConstructionAux.guess_critical hQ).1.2
        (show w t ∈ inputsUpTo w t from (mem_inputsUpTo_iff w t _).2 ⟨t, le_rfl, rfl⟩))
    (by
      intro t t' htt' ht ht'
      have ht1t := ht1min t ((hmemBd _).1 ht).2
      exact idxOf_mono P hPpw (hZP t' (ht1t.trans htt')) (hZP t ht1t)
        (CaptureAux.isAnc_le _ _ (hZmono t t' ht1t htt')).1)
    (by
      intro t ht ⟨y, hyB, hyl, hyin, hyout⟩
      have htI := ((hmemBd _).1 ht).2
      have ht1t := ht1min t htI
      obtain ⟨Q, hQ, hzQ⟩ := hguess t htI
      have hpodz : pod R C (inputsUpTo w t) z = I ∩ R.lab (Z t) := by
        simp only [pod, CaptureAux.inputsUpTo_getLastD]
        rw [show boardOf R C z (w t) = I from ConstructionAux.cutBoard_eq_of_mem htI]
      have hgl : labs.getD (P.idxOf (Z t)) ∅ = R.lab (Z t) := getD_map_idxOf P (hZP t ht1t)
      rw [hgl] at hyl ⊢
      have hout := out_mem_pod hX hS.toGood hC hz ht₀ x hreg htI hQ hzQ (by
        refine ⟨y, by rw [hpodz]; exact ⟨((hmemBd y).1 hyB).2, hyl⟩, ?_⟩
        rintro (h | h)
        · obtain ⟨s, hs, e⟩ := (mem_inputsUpTo_iff w t y).1 h
          exact hyin s hs e
        · obtain ⟨s, hs, e⟩ := (mem_prevOuts_iff w t y).1 h
          exact hyout s hs e)
      rw [hpodz] at hout
      exact ⟨(hmemBd _).2 ⟨(CaptureAux.isAnc_le _ _ (hZspec t ht1t).2).2 hout.2, hout.1⟩, hout.2⟩)
  -- the uniform board bound
  have hub := uniform_board_laySum hX hS.toGood hC Q1 hQ1V z hzQ1 x
  have hq := hS.q_le z hz
  have hcard : (Bd.filter (fun y => ∃ t, (algGen R C).out w t = y)).card =
      ((algGen R C).outputSet w ∩ K ∩ I).ncard := by
    rw [← ncard_coe_finset, Finset.coe_filter]
    congr 1; ext y
    simp only [mem_ofPred_eq, hmemBd, Generator.outputSet, mem_inter_iff, mem_range]
    tauto
  rw [hBdc] at hgame
  have h1 : (layerSum labs (K ∩ I) : ℝ) ≤ ((algGen R C).outputSet w ∩ K ∩ I).ncard := by
    rw [← hcard]; exact_mod_cast hgame
  have h0 : (0 : ℝ) ≤ ((K ∩ I).ncard : ℝ) := Nat.cast_nonneg _
  calc R.q z * ((K ∩ I).ncard : ℝ) ≤ max 0 (R.s z - 1 / R.N z) * ((K ∩ I).ncard : ℝ) :=
        mul_le_mul_of_nonneg_right hq h0
    _ ≤ layerSum labs (K ∩ I) := hub
    _ ≤ _ := h1

/-! ### From regular boards to the lower Banach density -/

/-- Summing Corollary 6.19 over a finite union of whole regular board traces. -/
lemma sum_boards {z : ℕ} {K O S : Set ℤ} {q : ℝ} (hSf : S.Finite) (hSK : S ⊆ K)
    (hfull : ∀ y ∈ S, K ∩ boardOf R C z y ⊆ S)
    (hreg : ∀ y ∈ S, q * ((K ∩ boardOf R C z y).ncard : ℝ) ≤
      ((O ∩ K ∩ boardOf R C z y).ncard : ℝ)) :
    q * (S.ncard : ℝ) ≤ ((O ∩ S).ncard : ℝ) := by
  have hOSf : (O ∩ S).Finite := hSf.subset inter_subset_right
  set Sf := hSf.toFinset
  set OSf := hOSf.toFinset
  set f : ℤ → Set ℤ := boardOf R C z
  set t := Sf.image f
  have h1 := Finset.card_eq_sum_card_fiberwise (s := Sf) (t := t) (f := f)
    (fun y hy => Finset.mem_image_of_mem f hy)
  have h2 := Finset.card_eq_sum_card_fiberwise (s := OSf) (t := t) (f := f)
    (fun y hy => Finset.mem_image_of_mem f (hSf.mem_toFinset.2 (hOSf.mem_toFinset.1 hy).2))
  have hfib : ∀ I ∈ t, ((Sf.filter (fun y => f y = I)).card : ℝ) = (K ∩ I).ncard ∧
      ((OSf.filter (fun y => f y = I)).card : ℝ) = (O ∩ K ∩ I).ncard := by
    intro I hI
    obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.1 hI
    have hy₀S : y₀ ∈ S := hSf.mem_toFinset.1 hy₀
    have key : ∀ y, y ∈ S ∧ f y = f y₀ ↔ y ∈ K ∧ y ∈ f y₀ := by
      intro y
      constructor
      · rintro ⟨hy, he⟩
        exact ⟨hSK hy, he ▸ ConstructionAux.mem_cutBoard_self _ _⟩
      · rintro ⟨hyK, hy⟩
        exact ⟨hfull y₀ hy₀S ⟨hyK, hy⟩, ConstructionAux.cutBoard_eq_of_mem hy⟩
    constructor
    · rw [← ncard_coe_finset]; congr 2; ext y
      simp only [Finset.coe_filter, Finite.mem_toFinset, mem_ofPred_eq, mem_inter_iff, Sf]
      exact key y
    · rw [← ncard_coe_finset]; congr 2; ext y
      simp only [Finset.coe_filter, Finite.mem_toFinset, mem_ofPred_eq, mem_inter_iff, OSf]
      constructor
      · rintro ⟨⟨hO, hS⟩, he⟩; exact ⟨⟨hO, ((key y).1 ⟨hS, he⟩).1⟩, ((key y).1 ⟨hS, he⟩).2⟩
      · rintro ⟨⟨hO, hK⟩, hy⟩; exact ⟨⟨hO, ((key y).2 ⟨hK, hy⟩).1⟩, ((key y).2 ⟨hK, hy⟩).2⟩
  have eS : (S.ncard : ℝ) = ∑ I ∈ t, ((Sf.filter (fun y => f y = I)).card : ℝ) := by
    rw [← hSf.coe_toFinset, ncard_coe_finset]; exact_mod_cast h1
  have eO : ((O ∩ S).ncard : ℝ) = ∑ I ∈ t, ((OSf.filter (fun y => f y = I)).card : ℝ) := by
    rw [← hOSf.coe_toFinset, ncard_coe_finset]; exact_mod_cast h2
  rw [eS, eO, Finset.mul_sum]
  refine Finset.sum_le_sum fun I hI => ?_
  rw [(hfib I hI).1, (hfib I hI).2]
  obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.1 hI
  exact hreg y₀ (hSf.mem_toFinset.1 hy₀)

lemma union_bound {K : Set ℤ} {B : ℕ} (F : ℕ → Set ℤ)
    (hF : ∀ r, (K ∩ F r).Finite ∧ (K ∩ F r).ncard ≤ B) :
    ∀ n, (K ∩ ⋃ r ∈ Finset.range n, F r).Finite ∧ (K ∩ ⋃ r ∈ Finset.range n, F r).ncard ≤ n * B
  | 0 => by simp
  | n + 1 => by
    obtain ⟨ih1, ih2⟩ := union_bound F hF n
    rw [Finset.range_add_one, Finset.set_biUnion_insert, inter_union_distrib_left]
    refine ⟨(hF n).1.union ih1, (ncard_union_le _ _).trans ?_⟩
    have := (hF n).2
    rw [Nat.succ_mul]; omega

/-- Two points in a board: the interval between them lies in it. -/
lemma mem_cutBoard_between {Cs : Set ℤ} {y y' a : ℤ} (hy' : y' ∈ cutBoard Cs y)
    (h1 : min y y' ≤ a) (h2 : a ≤ max y y') : a ∈ cutBoard Cs y := by
  intro c hc hca
  have := hy' c hc
  simp only [min_le_iff, lt_max_iff] at h1 h2 hca this
  omega

/-- The passage from regular boards to large relative intervals (tex l.3723–3737), for any
system satisfying `GoodSystem`, at a capture time `t₀`. -/
theorem density_gen (hX : LangClass X) (hS : GoodSystem X R) (hC : C.Valid X R)
    {z : ℕ} (hz : R.isV z) {w : ℕ → ℤ} (hw : IsFullEnumeration w (R.lab z)) {t₀ : ℕ}
    (ht₀ : ∀ t ≥ t₀, ∃ Q, guess R (inputsUpTo w t) = some Q ∧ IsAnc R C z Q) :
    R.q z ≤ outputDensity ((algGen R C).outputSet w) (R.lab z) := by
  set K := R.lab z with hK
  set O := (algGen R C).outputSet w with hO
  set B := (vdata R C z).B with hB
  have hbs : ∀ x, (K ∩ boardOf R C z x).Finite ∧ R.N z ≤ (K ∩ boardOf R C z x).ncard ∧
      (K ∩ boardOf R C z x).ncard ≤ B := ForestAux.board_spec hX hS.lab_mem hS.N_pos hC z hz
  have hKinf : K.Infinite := hX.infinite _ (hS.lab_mem z hz)
  obtain ⟨hT, h0, -⟩ := BasicAux.outputDensity_tendsto (O := O) hKinf
  rcases le_or_gt (R.q z) 0 with hq | hq
  · linarith
  set q := R.q z
  set c : ℕ := 2 * B + t₀ * (2 * B) with hc
  have hwK : ∀ r, w r ∈ K := fun r => hw ▸ mem_range_self r
  -- the main estimate on an interval
  have key : ∀ a b : ℤ, q * ((K ∩ Icc a b).ncard : ℝ) ≤
      (((O ∩ K) ∩ Icc a b).ncard : ℝ) + q * c := by
    intro a b
    let F : ℕ → Set ℤ := fun r => boardOf R C z (w r) ∪ boardOf R C z ((algGen R C).out w r)
    have hF : ∀ r, (K ∩ F r).Finite ∧ (K ∩ F r).ncard ≤ 2 * B := by
      intro r
      rw [inter_union_distrib_left]
      refine ⟨(hbs _).1.union (hbs _).1, (ncard_union_le _ _).trans ?_⟩
      have := (hbs (w r)).2.2; have := (hbs ((algGen R C).out w r)).2.2; omega
    obtain ⟨hEf, hEc⟩ := union_bound F hF t₀
    set E := ⋃ r ∈ Finset.range t₀, F r
    set Bad := K ∩ (boardOf R C z a ∪ boardOf R C z b ∪ E) with hBad
    have hBadf : Bad.Finite := by
      rw [hBad, inter_union_distrib_left, inter_union_distrib_left]
      exact ((hbs a).1.union (hbs b).1).union hEf
    have hBadc : Bad.ncard ≤ c := by
      rw [hBad, inter_union_distrib_left, inter_union_distrib_left]
      refine (ncard_union_le _ _).trans ?_
      have := (ncard_union_le (K ∩ boardOf R C z a) (K ∩ boardOf R C z b))
      have := (hbs a).2.2; have := (hbs b).2.2
      omega
    set A := K ∩ Icc a b
    have hAf : A.Finite := (finite_Icc a b).subset inter_subset_right
    set A' := A \ Bad
    have hA'f : A'.Finite := hAf.subset diff_subset
    -- points of `K` whose board meets a bad board are bad
    have hbadOf : ∀ y ∈ K, ∀ y', y' ∈ boardOf R C z y →
        (y' ∈ boardOf R C z a ∨ y' ∈ boardOf R C z b ∨ y' ∈ E) → y ∈ Bad := by
      intro y hyK y' hy' h
      have tr : ∀ u, y' ∈ boardOf R C z u → y ∈ boardOf R C z u := by
        intro u hu
        have e1 : boardOf R C z y' = boardOf R C z y := ConstructionAux.cutBoard_eq_of_mem hy'
        have e2 : boardOf R C z y' = boardOf R C z u := ConstructionAux.cutBoard_eq_of_mem hu
        rw [← e2, e1]; exact ConstructionAux.mem_cutBoard_self _ _
      refine ⟨hyK, ?_⟩
      rcases h with h | h | h
      · exact Or.inl (Or.inl (tr a h))
      · exact Or.inl (Or.inr (tr b h))
      · simp only [E, mem_iUnion, Finset.mem_range, F, mem_union] at h ⊢
        obtain ⟨r, hr, h | h⟩ := h
        · exact Or.inr ⟨r, hr, Or.inl (tr _ h)⟩
        · exact Or.inr ⟨r, hr, Or.inr (tr _ h)⟩
    have hfull : ∀ y ∈ A', K ∩ boardOf R C z y ⊆ A' := by
      rintro y ⟨⟨hyK, hya, hyb⟩, hyBad⟩ y' ⟨hy'K, hy'⟩
      refine ⟨⟨hy'K, ?_, ?_⟩, ?_⟩
      · by_contra h
        apply hyBad
        have ha : a ∈ boardOf R C z y :=
          mem_cutBoard_between hy' (by rw [min_le_iff]; right; omega) (by rw [le_max_iff]; left; exact hya)
        exact hbadOf y hyK a ha (Or.inl (ConstructionAux.mem_cutBoard_self _ _))
      · by_contra h
        apply hyBad
        have hb : b ∈ boardOf R C z y :=
          mem_cutBoard_between hy' (by rw [min_le_iff]; left; exact hyb) (by rw [le_max_iff]; right; omega)
        exact hbadOf y hyK b hb (Or.inr (Or.inl (ConstructionAux.mem_cutBoard_self _ _)))
      · rintro ⟨-, h⟩
        apply hyBad
        rcases h with (h | h) | h
        · exact hbadOf y hyK y' hy' (Or.inl h)
        · exact hbadOf y hyK y' hy' (Or.inr (Or.inl h))
        · exact hbadOf y hyK y' hy' (Or.inr (Or.inr h))
    have hregA : ∀ y ∈ A', ¬ Exceptional R C w z t₀ (boardOf R C z y) := by
      rintro y ⟨⟨hyK, -, -⟩, hyBad⟩ hex
      apply hyBad
      have hE : ∀ r < t₀, ∀ u, u = w r ∨ u = (algGen R C).out w r →
          u ∈ boardOf R C z y → y ∈ Bad := by
        rintro r hr u hu huy
        refine hbadOf y hyK u huy (Or.inr (Or.inr ?_))
        simp only [E, mem_iUnion, Finset.mem_range, F, mem_union]
        rcases hu with rfl | rfl
        · exact ⟨r, hr, Or.inl (ConstructionAux.mem_cutBoard_self _ _)⟩
        · exact ⟨r, hr, Or.inr (ConstructionAux.mem_cutBoard_self _ _)⟩
      rcases hex with ⟨r, hr, h | h⟩ | ⟨a', -, r, hr, Q, -, -, hsub⟩
      · exact hE r hr _ (Or.inl rfl) h.2
      · exact hE r hr _ (Or.inr rfl) h.2
      · exact hE r hr _ (Or.inl rfl) (hsub (ConstructionAux.mem_cutBoard_self _ _))
    have hsum := sum_boards (O := O) (q := q) hA'f (fun y hy => hy.1.1) hfull
      (fun y hy => regular_board_gen hX hS hC hz hw ht₀ y (hregA y hy))
    have hAle : A.ncard ≤ A'.ncard + Bad.ncard := by
      calc A.ncard ≤ (A' ∪ Bad).ncard := ncard_le_ncard (fun y hy => by
            by_cases h : y ∈ Bad
            · exact Or.inr h
            · exact Or.inl ⟨hy, h⟩) (hA'f.union hBadf)
        _ ≤ _ := ncard_union_le _ _
    have hOle : (O ∩ A').ncard ≤ ((O ∩ K) ∩ Icc a b).ncard := by
      refine ncard_le_ncard ?_ (hAf.subset (by rintro y ⟨⟨-, h1⟩, h2⟩; exact ⟨h1, h2⟩))
      rintro y ⟨hO, ⟨hK, hI⟩, -⟩; exact ⟨⟨hO, hK⟩, hI⟩
    have h1 : (A.ncard : ℝ) ≤ A'.ncard + Bad.ncard := by exact_mod_cast hAle
    have h2 : ((O ∩ A').ncard : ℝ) ≤ ((O ∩ K) ∩ Icc a b).ncard := by exact_mod_cast hOle
    have h3 : (Bad.ncard : ℝ) ≤ c := by exact_mod_cast hBadc
    nlinarith
  -- the limit
  have hinf : ∀ n : ℕ, q - q * c / ((n : ℝ) + 1) ≤ BasicAux.banachInf (O ∩ K) K (n + 1) := by
    intro n
    haveI := BasicAux.banach_inf_nonempty hKinf (n + 1)
    refine le_ciInf fun Rr => ?_
    obtain ⟨⟨a, b⟩, hR⟩ := Rr
    simp only at hR ⊢
    have hd : ((n : ℝ) + 1) ≤ (K ∩ Icc a b).ncard := by exact_mod_cast hR
    have hd0 : (0 : ℝ) < (K ∩ Icc a b).ncard := by linarith
    rw [le_div_iff₀ hd0]
    have hk := key a b
    have hqc : 0 ≤ q * c := by positivity
    have h4 : q * c ≤ q * c / ((n : ℝ) + 1) * (K ∩ Icc a b).ncard := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left hd hqc
    nlinarith
  have hle : ∀ n, BasicAux.banachInf (O ∩ K) K n ≤ outputDensity O K :=
    fun n => (BasicAux.banachInf_mono hKinf).ge_of_tendsto hT n
  have hlim : Tendsto (fun n : ℕ => q - q * c / ((n : ℝ) + 1)) atTop (nhds q) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (q * c)
    have h' := (tendsto_const_nhds (x := q)).sub h
    simp only [mul_zero, sub_zero] at h'
    refine h'.congr fun n => ?_
    ring
  exact le_of_tendsto' hlim fun n => (hinf n).trans (hle (n + 1))

/-! ### The two vertex systems -/

/-- The fixed-`ε` system satisfies `GoodSystem`. -/
lemma goodSystem_fixed {ε : ℝ} (hR : IsFixedEpsSystem X ε R) : GoodSystem X R where
  toGood := ForestAux.good_of_fixedEps hR
  q_le := ForestAux.fixedEps_q_le hR

/-- The formal-copy system satisfies `GoodSystem`. -/
lemma goodSystem_copy {copy : ℕ → ℕ} (hR : IsCopySystem X R copy) :
    GoodSystem X R where
  toGood := ForestAux.good_of_copy hR
  q_le v _ := by
    rw [hR.q_def v, hR.s_def v]
    have h1 := hR.N_small v
    have h2 : ((1 : ℝ) / 2) ^ (copy v + 1) * 2 = (1 / 2) ^ copy v := by rw [pow_succ]; ring
    refine max_le ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_right _ _)
    have := le_max_left (bK X (R.lab v) - (1 / 2 : ℝ) ^ (copy v + 1)) 0
    linarith

/-- The fixed-`ε` density bound (completion of the proof of Theorem 6.1, tex l.3723–3737):
`δ_B(O, K) ≥ q_z` on every full enumeration of `K = L_z`. -/
theorem fixed_density {X : Set (Set ℤ)} (hX : LangClass X) {ε : ℝ}
    {R : Requirements} (hR : IsFixedEpsSystem X ε R) {C : Choices} (hC : C.Valid X R)
    {z : ℕ} (hz : R.isV z) {w : ℕ → ℤ} (hw : IsFullEnumeration w (R.lab z)) :
    R.q z ≤ outputDensity ((algGen R C).outputSet w) (R.lab z) := by
  -- `0 < 1 / N_z ≤ ε / 2`, for the call to Lemma 6.16
  have hε : 0 < ε := by
    have hN : (1 : ℝ) ≤ R.N z := by exact_mod_cast hR.N_pos z hz
    have := hR.N_small z hz
    have : (0 : ℝ) < 1 / R.N z := div_pos one_pos (by linarith)
    linarith
  obtain ⟨t₀, ht₀⟩ := lem_capture hX hε hR hC hz hw
  exact density_gen hX (goodSystem_fixed hR) hC hz hw ht₀

end DensityAux

/-- **Corollary 6.19** (`cor:regular-board-density`). Fix a full enumeration of `K = L_z` and a
capture time `t₀` as in Lemma 6.16. Every regular (not exceptional) `z`-board `I` satisfies
`|O ∩ K ∩ I| ≥ q_z |K ∩ I|`. The hypothesis `hε : 0 < ε` mirrors the paper's fixed `ε > 0` of
Section 6.4; the Lean proof does not use it. -/
theorem cor_regular_board_density {X : Set (Set ℤ)} (hX : LangClass X) {ε : ℝ} (hε : 0 < ε)
    {R : Requirements} (hR : IsFixedEpsSystem X ε R) {C : Choices} (hC : C.Valid X R)
    {z : ℕ} (hz : R.isV z) {w : ℕ → ℤ} (hw : IsFullEnumeration w (R.lab z)) {t₀ : ℕ}
    (ht₀ : ∀ t ≥ t₀, ∃ Q, guess R (inputsUpTo w t) = some Q ∧ IsAnc R C z Q) (x : ℤ)
    (hreg : ¬ Exceptional R C w z t₀ (boardOf R C z x)) :
    R.q z * ((R.lab z ∩ boardOf R C z x).ncard : ℝ) ≤
      (((algGen R C).outputSet w ∩ R.lab z ∩ boardOf R C z x).ncard : ℝ) := by
  exact DensityAux.regular_board_gen hX (DensityAux.goodSystem_fixed hR) hC hz hw ht₀ x hreg

/-- **Lemma 6.22** (`lem:fixed-copy-density`). Fix `m ≥ 1` and a full enumeration of `K`. The
output set `O` of the formal-copy algorithm satisfies `δ_B(O, K) ≥ q_{K,m} = (b(K) - 2^{-m})_+`. -/
theorem lem_fixed_copy_density {X : Set (Set ℤ)} (hX : LangClass X) {R : Requirements}
    {copy : ℕ → ℕ} (hR : IsCopySystem X R copy) {C : Choices} (hC : C.Valid X R)
    {K : Set ℤ} (hK : K ∈ X) {m : ℕ} (hm : 1 ≤ m) {w : ℕ → ℤ} (hw : IsFullEnumeration w K) :
    max (bK X K - (1 / 2 : ℝ) ^ m) 0 ≤ outputDensity ((algGen R C).outputSet w) K := by
  obtain ⟨z, hzK, hzm⟩ := hR.surj K hK m hm
  subst hzK
  obtain ⟨t₀, ht₀⟩ := lem_capture_fixed_copy hX hR hC hw
  have h := DensityAux.density_gen hX (DensityAux.goodSystem_copy hR) hC (hR.all z) hw ht₀
  rwa [hR.q_def z, hzm] at h

end BanachDensity1D
