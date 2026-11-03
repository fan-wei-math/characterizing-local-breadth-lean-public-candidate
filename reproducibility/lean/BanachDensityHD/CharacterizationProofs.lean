import BanachDensityHD.Sewing

/-!
# Section 8: proof development for the characterization

Helper lemmas (namespace `CharAux`) for the proofs in `BanachDensityHD/Characterization.lean`:
Lemma 8.13, Theorem 8.7, Corollaries 8.8 and 8.9, Theorem 8.1(2), and the necessity half of
Theorem 8.2. These lemmas supply the proofs of the listed results.

-/

namespace BanachDensityHD

open Set Filter
open scoped Classical

/-! ## Proof development (helpers for §8) -/

namespace CharAux

/-- `hLog g` is positive on `ℕ_{≥1}` when `g ≥ 1`. -/
theorem hLog_pos {g : ℝ → ℝ} (hg1 : ∀ x, 1 ≤ x → 1 ≤ g x) (n : ℕ) (hn : 1 ≤ n) :
    0 < hLog g n := by
  unfold hLog
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have := hg1 n h1
  have : 0 < Real.log (2 + n) := Real.log_pos (by linarith)
  positivity

/-- The stages `hs 0 = h₀`, `hs (k+1) = hs k ++ e k :: r k (hs k)` stay inside `L`, all extend
`h₀`, and have a common limit sequence that is a full enumeration of `L = range e` (the generic
diagonal construction used in the commitment arguments). -/
theorem stages_limit {d : ℕ} (L : Set (Pt d)) (e : ℕ → Pt d) (he : range e = L)
    (r : ℕ → List (Pt d) → List (Pt d)) (hr : ∀ k l, ∀ x ∈ r k l, x ∈ L) (h₀ : List (Pt d))
    (h₀L : ∀ x ∈ h₀, x ∈ L) :
    let hs : ℕ → List (Pt d) := fun k => Nat.rec h₀ (fun k h => h ++ e k :: r k h) k
    (∀ k, ∀ x ∈ hs k, x ∈ L) ∧ (∀ k, ∃ r', hs k = h₀ ++ r') ∧
    ∃ w : ℕ → Pt d, (∀ k i (hi : i < (hs k).length), w i = (hs k)[i]) ∧
      IsFullEnumeration w L := by
  intro hs
  have hs_succ : ∀ k, hs (k + 1) = hs k ++ e k :: r k (hs k) := fun k => rfl
  have heL : ∀ k, e k ∈ L := fun k => by rw [← he]; exact mem_range_self k
  have hsL : ∀ k, ∀ x ∈ hs k, x ∈ L := by
    intro k
    induction k with
    | zero => exact h₀L
    | succ k ih =>
      intro x hx
      rw [hs_succ] at hx
      simp only [List.mem_append, List.mem_cons] at hx
      rcases hx with hx | rfl | hx
      · exact ih x hx
      · exact heL k
      · exact hr k _ x hx
  have hpre : ∀ k, ∃ r', hs k = h₀ ++ r' := by
    intro k
    induction k with
    | zero => exact ⟨[], by simp [hs]⟩
    | succ k ih =>
      obtain ⟨r', hr'⟩ := ih
      exact ⟨r' ++ e k :: r k (hs k), by rw [hs_succ, hr', List.append_assoc]⟩
  have hlen : ∀ k, k ≤ (hs k).length := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [hs_succ]; simp only [List.length_append, List.length_cons]; omega
  obtain ⟨w, hw, hrange⟩ := SeparationAux.limit_exists hs (fun k => ⟨_, hs_succ k⟩) hlen
  refine ⟨hsL, hpre, w, hw, ?_⟩
  ext y
  rw [hrange]
  constructor
  · rintro ⟨k, hk⟩; exact hsL k y hk
  · intro hy
    rw [← he] at hy
    obtain ⟨k, rfl⟩ := hy
    exact ⟨k + 1, by rw [hs_succ]; simp⟩

/-- An enumeration of an infinite countable language. -/
theorem enum_of_mem {d : ℕ} {L : Set (Pt d)} (hL : L.Nonempty) : ∃ e : ℕ → Pt d, range e = L :=
  let ⟨f, hf⟩ := (Set.to_countable L).exists_eq_range hL
  ⟨f, hf.symm⟩

/-- The density commitment (second part of Lemma 8.13), after a fixed prefix `xs ⊆ L`. -/
theorem density_commit {d : ℕ} {X : Set (Set (Pt d))} {g : ℝ → ℝ}
    (hg1 : ∀ x, 1 ≤ x → 1 ≤ g x) (G : Generator (Pt d))
    (hG : G ∈ ValidGen X) {L : Set (Pt d)} (e : ℕ → Pt d) (he : range e = L)
    {αL q : ℝ} (hach : Guarantees (dH (hLog g)) G L αL) (hq : q < αL)
    (xs : List (Pt d)) (hxL : ∀ x ∈ xs, x ∈ L) :
    ∃ ext : List (Pt d), ∃ s : ℝ, 1 ≤ s ∧ (∀ x ∈ ext, x ∈ L) ∧
      ∀ cont : List (Pt d), (∀ x ∈ cont, x ∈ L) →
        ∀ R : Rect d, s * (hLog g) R.vol ≤ mass L R →
          (L ∩ R.pts ⊆ {x | x ∈ xs ++ ext ++ cont} ∪ outsOf G (xs ++ ext ++ cont)) →
          q * (mass L R : ℝ) ≤ ((outsOf G (xs ++ ext ++ cont) ∩ L ∩ R.pts).ncard : ℝ) := by
  by_contra hcon
  push Not at hcon
  let Bad : ℕ → List (Pt d) → List (Pt d) → Prop := fun k l c => (∀ x ∈ c, x ∈ L) ∧
    ∃ R : Rect d, ((k : ℝ) + 1) * (hLog g) R.vol ≤ mass L R ∧
      (L ∩ R.pts ⊆ {x | x ∈ l ++ c} ∪ outsOf G (l ++ c)) ∧
      ((outsOf G (l ++ c) ∩ L ∩ R.pts).ncard : ℝ) < q * (mass L R : ℝ)
  let r : ℕ → List (Pt d) → List (Pt d) := fun k l =>
    if h : ∃ c, Bad k (l ++ [e k]) c then h.choose else []
  have hr : ∀ k l, ∀ x ∈ r k l, x ∈ L := by
    intro k l x hx
    simp only [r] at hx
    split_ifs at hx with h
    · exact h.choose_spec.1 x hx
    · simp at hx
  obtain ⟨hsL, hpre, w, hw, hfull⟩ := stages_limit L e he r hr xs hxL
  set hs : ℕ → List (Pt d) := fun k => Nat.rec xs (fun k h => h ++ e k :: r k h) k with hhs
  have hs_succ : ∀ k, hs (k + 1) = hs k ++ e k :: r k (hs k) := fun k => rfl
  have heL : ∀ k, e k ∈ L := fun k => by rw [← he]; exact mem_range_self k
  have hbad : ∀ k : ℕ, ∃ R : Rect d, ((k : ℝ) + 1) * (hLog g) R.vol ≤ mass L R ∧
      ((G.outputSet w ∩ L ∩ R.pts).ncard : ℝ) < q * (mass L R : ℝ) := by
    intro k
    obtain ⟨r', hr'⟩ := hpre k
    have hext : ∀ x ∈ r' ++ [e k], x ∈ L := by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hsL k x (by rw [hr']; exact List.mem_append_right _ hx)
      · rw [List.mem_singleton.1 hx]; exact heL k
    have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
    obtain ⟨c, hcL, R, hR, hocc, hlt⟩ := hcon (r' ++ [e k]) ((k : ℝ) + 1) hk1 hext
    have hex : ∃ c, Bad k (hs k ++ [e k]) c := ⟨c, hcL, R, hR, by
      rw [hr']; simpa [List.append_assoc] using hocc, by
      rw [hr']; simpa [List.append_assoc] using hlt⟩
    have hrk : r k (hs k) = hex.choose := by simp only [r, dite_eq_left hex]
    obtain ⟨-, R, hR, hocc, hlt⟩ := hex.choose_spec
    rw [← hrk] at hocc hlt
    have hl : hs k ++ [e k] ++ r k (hs k) = hs (k + 1) := by rw [hs_succ]; simp
    rw [hl] at hocc hlt
    refine ⟨R, hR, lt_of_le_of_lt ?_ hlt⟩
    have hsub : G.outputSet w ∩ L ∩ R.pts ⊆ outsOf G (hs (k + 1)) ∩ L ∩ R.pts := by
      rintro y ⟨⟨hyO, hyL⟩, hyR⟩
      exact ⟨⟨SeparationAux.sealed hG.1 (hw (k + 1)) hyO (hocc ⟨hyL, hyR⟩), hyL⟩, hyR⟩
    exact_mod_cast Set.ncard_le_ncard hsub ((BasicAux.rect_pts_finite R).inter_of_right _)
  -- the density along `w` is at most `q`
  have hpos : ∀ n, 1 ≤ n → 0 < hLog g n := hLog_pos hg1
  have hlim := (deltaH_tendsto (hLog g) hpos (G.outputSet w) L).1
  have hle : deltaH (hLog g) (G.outputSet w) L ≤ q := by
    have h2 : Tendsto (fun k : ℕ => testInf (hLog g) (G.outputSet w) L ((k : ℝ) + 1)) atTop
        (nhds (deltaH (hLog g) (G.outputSet w) L)) :=
      hlim.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    refine le_of_tendsto' h2 fun k => ?_
    obtain ⟨R, hR, hlt⟩ := hbad k
    have hmem : ((G.outputSet w ∩ L ∩ R.pts).ncard : ℝ) / mass L R ∈
        BasicAux.tests (hLog g) (G.outputSet w) L ((k : ℝ) + 1) := ⟨R, hR, rfl⟩
    rw [BasicAux.testInf_eq, ite_eq_left ⟨_, hmem⟩]
    have hmpos : (0 : ℝ) < mass L R := by
      have := hpos _ (BasicAux.rect_vol_pos R)
      have : (0 : ℝ) < ((k : ℝ) + 1) * hLog g R.vol := by positivity
      linarith
    refine (csInf_le (BasicAux.tests_bdd _ _ _ _) hmem).trans ?_
    rw [div_le_iff₀ hmpos]
    exact hlt.le
  have := hach w hfull
  unfold dH at this
  have := EReal.coe_le_coe_iff.1 this
  linarith

/-- Lemma 8.13, in the form used by the proofs: the statement of `lem_hd_commitments`
(`Characterization.lean`) without its hypotheses `2 ≤ d` and `g` monotone, and with `q < αL` in
place of `0 ≤ q < αL` (none of these is needed by the argument). -/
theorem hd_commitments {d : ℕ} {X : Set (Set (Pt d))} (hX : LangClass X)
    {g : ℝ → ℝ} (hg1 : ∀ x, 1 ≤ x → 1 ≤ g x) (G : Generator (Pt d)) (hG : G ∈ ValidGen X)
    {L : Set (Pt d)} (hL : L ∈ X)
    {αL q : ℝ} (hach : Guarantees (dH (hLog g)) G L αL) (hq : q = 0 ∨ q < αL)
    (xs : List (Pt d)) (hxL : ∀ x ∈ xs, x ∈ L) :
    ∃ ext : List (Pt d), ∃ s : ℝ, 1 ≤ s ∧ (∀ x ∈ ext, x ∈ L) ∧
      ∀ cont : List (Pt d), (∀ x ∈ cont, x ∈ L) →
        (∀ j < cont.length, G ((xs ++ ext ++ cont).take ((xs ++ ext).length + j + 1)) ∈ L) ∧
        ∀ R : Rect d, s * (hLog g) R.vol ≤ mass L R →
          (L ∩ R.pts ⊆ {x | x ∈ xs ++ ext ++ cont} ∪ outsOf G (xs ++ ext ++ cont)) →
          q * (mass L R : ℝ) ≤ ((outsOf G (xs ++ ext ++ cont) ∩ L ∩ R.pts).ncard : ℝ) := by
  obtain ⟨e, he⟩ := CharAux.enum_of_mem (hX.infinite L hL).nonempty
  obtain ⟨ext₀, hext₀L, hval⟩ := SeparationAux.commit_strong (hX.infinite L hL) (hG.2 L hL) xs hxL
  have hxs0 : ∀ x ∈ xs ++ ext₀, x ∈ L := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hxL x hx
    · exact hext₀L x hx
  rcases hq with rfl | hqα
  · refine ⟨ext₀, 1, le_rfl, hext₀L, fun cont hc => ⟨fun j hj => hval cont hc j hj,
      fun R _ _ => by simp⟩⟩
  · obtain ⟨ext₁, s, hs1, hext₁L, hden⟩ :=
      CharAux.density_commit hg1 G hG e he hach hqα (xs ++ ext₀) hxs0
    refine ⟨ext₀ ++ ext₁, s, hs1, fun x hx => ?_, fun cont hc => ⟨fun j hj => ?_,
      fun R hR hocc => ?_⟩⟩
    · rcases List.mem_append.1 hx with hx | hx
      · exact hext₀L x hx
      · exact hext₁L x hx
    · have hc' : ∀ x ∈ ext₁ ++ cont, x ∈ L := by
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hext₁L x hx
        · exact hc x hx
      have := hval (ext₁ ++ cont) hc' (ext₁.length + j) (by simp; omega)
      have e1 : xs ++ ext₀ ++ (ext₁ ++ cont) = xs ++ (ext₀ ++ ext₁) ++ cont := by simp
      have e2 : (xs ++ ext₀).length + (ext₁.length + j) + 1 =
          (xs ++ (ext₀ ++ ext₁)).length + j + 1 := by simp; omega
      rwa [e1, e2] at this
    · have e1 : xs ++ ext₀ ++ ext₁ ++ cont = xs ++ (ext₀ ++ ext₁) ++ cont := by simp
      rw [← e1] at hocc ⊢
      exact hden cont hc R hR hocc

/-! ### Theorem 8.7: list and transport lemmas -/

section Lists
variable {β : Type*}

theorem getLastD_take (l : List β) (x : β) (i : ℕ) (hi : i < l.length) :
    (l.take (i + 1)).getLastD x = l[i] := by
  rw [List.getLastD_eq_getLast?, List.getLast?_take]
  simp [List.getElem?_eq_getElem hi]

theorem getLastD_eq_getLast (l : List β) (x : β) (hl : l ≠ []) : l.getLastD x = l.getLast hl := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hl]
  rfl

end Lists

/-- Transport of geometric feasibility along an equality of the number of levels. -/
theorem geom_transport {d : ℕ} (h : ℕ → ℝ) {r r' : ℕ} (e : r = r')
    {Ls : Fin (r + 1) → Set (Pt d)} {qs ss : Fin (r + 1) → ℝ}
    {Ls' : Fin (r' + 1) → Set (Pt d)} {qs' ss' : Fin (r' + 1) → ℝ} {a : ℝ}
    (hL : ∀ i : Fin (r' + 1), Ls' i = Ls (Fin.cast (by omega) i))
    (hq : ∀ i : Fin (r' + 1), qs' i = qs (Fin.cast (by omega) i))
    (hs : ∀ i : Fin (r' + 1), ss' i = ss (Fin.cast (by omega) i))
    (hF : GeomFeasible h Ls qs ss a) : GeomFeasible h Ls' qs' ss' a := by
  subst e
  have e1 : Ls' = Ls := funext fun i => by simpa using hL i
  have e2 : qs' = qs := funext fun i => by simpa using hq i
  have e3 : ss' = ss := funext fun i => by simpa using hs i
  subst e1 e2 e3
  exact hF

/-- A nonempty prefix of a chain is a chain. -/
theorem isChain_take {α : Type*} {X : Set (Set α)} {l : List (Set α)} (hl : IsChain X l)
    {n : ℕ} (hn : 1 ≤ n) : IsChain X (l.take n) := by
  obtain ⟨hne, hX, hc⟩ := hl
  refine ⟨?_, fun L hL => hX L (List.mem_of_mem_take hL), hc.take n⟩
  intro h
  rcases List.take_eq_nil_iff.1 h with h | h
  · omega
  · exact hne h

/-- A chain's consecutive entries. -/
theorem isChain_getElem {α : Type*} {X : Set (Set α)} {l : List (Set α)} (hl : IsChain X l)
    (i : ℕ) (hi : i + 1 < l.length) : l[i + 1] ⊂ l[i] :=
  List.isChain_iff_getElem.1 hl.2.2 i hi

/-- The histories of `X` are countably many. -/
theorem countable_lists {α : Type*} {X : Set (Set α)} (hX : X.Countable) :
    {l : List (Set α) | ∀ L ∈ l, L ∈ X}.Countable := by
  have := hX.to_subtype
  refine (Set.countable_range (fun l : List X => l.map Subtype.val)).mono ?_
  intro l hl
  refine ⟨l.attach.map fun x => ⟨x.1, hl x.1 x.2⟩, ?_⟩
  simp [List.map_attach_eq_pmap]

section Paths
variable {d : ℕ}

/-- The tree path of a list: the data `f` of its nonempty prefixes. -/
noncomputable def pathG {β : Type*} (f : List β → Deco d) (l : List β) : List (Deco d) :=
  (List.range l.length).map fun i => f (l.take (i + 1))

section
variable {β : Type*} (f : List β → Deco d)

theorem pathG_length (l : List β) : (pathG f l).length = l.length := by simp [pathG]

theorem pathG_getElem (l : List β) (i : ℕ) (hi : i < (pathG f l).length) :
    (pathG f l)[i] = f (l.take (i + 1)) := by simp [pathG]

theorem pathG_take (l : List β) (n : ℕ) : (pathG f l).take n = pathG f (l.take n) := by
  apply List.ext_getElem
  · simp [pathG_length]
  · intro i h1 h2
    rw [List.getElem_take, pathG_getElem, pathG_getElem]
    simp only [List.length_take, pathG_length] at h1
    rw [List.take_take]
    congr 2
    omega

theorem pathG_snoc (l : List β) (M : β) : pathG f (l ++ [M]) = pathG f l ++ [f (l ++ [M])] := by
  apply List.ext_getElem
  · simp [pathG_length]
  · intro i h1 h2
    rw [pathG_getElem]
    simp only [pathG_length, List.length_append, List.length_singleton] at h1
    rcases Nat.lt_or_ge i l.length with hi | hi
    · rw [List.getElem_append_left (by rw [pathG_length]; exact hi), pathG_getElem,
        List.take_append_of_le_length (by omega)]
    · have : i = l.length := by omega
      subst this
      rw [List.getElem_append_right (by rw [pathG_length]), List.take_of_length_le (by simp)]
      simp [pathG_length]

theorem pathG_getLast (l : List β) (hp : pathG f l ≠ []) : (pathG f l).getLast hp = f l := by
  have hlen : 0 < l.length := by
    have := List.length_pos_iff.mpr hp; rwa [pathG_length] at this
  rw [List.getLast_eq_getElem, pathG_getElem, pathG_length, List.take_of_length_le (by omega)]

end

end Paths

/-! ### Theorem 8.7, decoration ⇒ tree -/

section DecoToTree
variable {d : ℕ} {X : Set (Set (Pt d))} {h : ℕ → ℝ} {q : Set (Pt d) → ℝ} {K : Set (Pt d)}

/-- Membership of a list in a set of histories. -/
def InU (X : Set (Set (Pt d))) (U : Set (History X)) (l : List (Set (Pt d))) : Prop :=
  ∃ hc : IsChain X l, (⟨l, hc⟩ : History X) ∈ U

/-- The vertex data of the history `l`, given protected sets `F`. -/
noncomputable def decoOf (F : List (Set (Pt d)) → Finset (Pt d)) (s a : List (Set (Pt d)) → ℝ)
    (l : List (Set (Pt d))) : Deco d :=
  .mk (l.getLastD ∅) 1 (F l) (s l) (a l)

variable (F : List (Set (Pt d)) → Finset (Pt d)) (s a : List (Set (Pt d)) → ℝ)

theorem decoOf_L (l : List (Set (Pt d))) : (decoOf F s a l).L = l.getLastD ∅ := rfl
theorem decoOf_s (l : List (Set (Pt d))) : (decoOf F s a l).s = s l := rfl
theorem decoOf_a (l : List (Set (Pt d))) : (decoOf F s a l).a = a l := rfl
theorem decoOf_P (l : List (Set (Pt d))) : (decoOf F s a l).P = F l := rfl

/-- **Theorem 8.7, (⇐)**: an open neighbourhood with a `q`-good decoration gives a protected
tree (one vertex per history of the neighbourhood). -/
theorem tree_of_deco (hXc : X.Countable) (hK : K ∈ X) {U : Set (History X)}
    {s a : List (Set (Pt d)) → ℝ} (hU : IsQGoodDecoration X h q K hK U s a) :
    ∃ T, IsProtectedTree X h q K T := by
  obtain ⟨hUK, hUo, hUs, hUpre, hUsa, hUa, hUg⟩ := hU
  have hopen := (HistoriesAux.isOpen_iff U).1 hUo
  choose Fs hFfin hFsub hFext using hopen
  let F : List (Set (Pt d)) → Finset (Pt d) := fun l =>
    if hl : InU X U l then (hFfin ⟨l, hl.1⟩ hl.2).toFinset else ∅
  have hF : ∀ l (hl : InU X U l), (F l : Set (Pt d)) = Fs ⟨l, hl.1⟩ hl.2 := by
    intro l hl; simp [F, hl]
  have hInU_take : ∀ l, InU X U l → ∀ n, 1 ≤ n → InU X U (l.take n) := fun l hl n hn =>
    ⟨isChain_take hl.1 hn, hUpre _ hl.2 n hn (isChain_take hl.1 hn)⟩
  have hK1 : InU X U [K] := ⟨(History.single K hK).2, hUs⟩
  let paths : Set (List (Deco d)) := {p | ∃ l, InU X U l ∧ p = pathG (decoOf F s a) l}
  have hroot : [decoOf F s a [K]] ∈ paths := ⟨[K], hK1, by simp [pathG]⟩
  have hhead : ∀ p ∈ paths, p.head? = some (decoOf F s a [K]) := by
    rintro p ⟨l, hl, rfl⟩
    obtain ⟨x, l', rfl⟩ := List.exists_cons_of_ne_nil hl.1.1
    have hx : x = K := hUK hl.2
    subst hx
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by simp [pathG_length]),
      pathG_getElem]
    simp
  have hpre : ∀ p ∈ paths, ∀ n, 1 ≤ n → p.take n ∈ paths := by
    rintro p ⟨l, hl, rfl⟩ n hn
    exact ⟨l.take n, hInU_take l hl n hn, pathG_take (decoOf F s a) l n⟩
  have hcount : paths.Countable := by
    refine ((countable_lists hXc).image (pathG (decoOf F s a))).mono ?_
    rintro p ⟨l, hl, rfl⟩
    exact ⟨l, hl.1.2.1, rfl⟩
  refine ⟨DTree.mk paths (decoOf F s a [K]) hroot hhead hpre hcount, rfl, ?_, ?_, ?_, ?_⟩
  · -- vertex data
    rintro p ⟨l, hl, rfl⟩ v hv
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    rw [pathG_getElem]
    rw [pathG_length] at hi
    have hl' := hInU_take l hl (i + 1) (by omega)
    refine ⟨?_, ?_, (hUsa _ hl'.2).1, (hUsa _ hl'.2).2, rfl⟩
    · rw [decoOf_L, getLastD_take l ∅ i hi]
      exact hl.1.2.1 _ (List.getElem_mem _)
    · rw [decoOf_P, decoOf_L, hF _ hl']
      exact hFsub _ hl'.2
  · -- edges
    rintro p v w ⟨l, hl, hp⟩
    have hlen : l.length = p.length + 2 := by
      have := congrArg List.length hp
      simp only [pathG_length, List.length_append, List.length_cons, List.length_nil] at this
      omega
    have hv : v = (pathG (decoOf F s a) l)[p.length]'(by rw [pathG_length]; omega) := by
      simp [← hp]
    have hw : w = (pathG (decoOf F s a) l)[p.length + 1]'(by rw [pathG_length]; omega) := by
      simp [← hp]
    rw [pathG_getElem] at hv hw
    subst hv hw
    rw [decoOf_L, decoOf_L, getLastD_take l ∅ _ (by omega), getLastD_take l ∅ _ (by omega),
      decoOf_a, decoOf_a]
    refine ⟨isChain_getElem hl.1 p.length (by omega), ?_⟩
    have h1 := hInU_take l hl (p.length + 1) (by omega)
    have h2 := hInU_take l hl (p.length + 1 + 1) (by omega)
    refine hUa _ h1.2 _ h2.2 (l[p.length + 1]'(by omega)) ⟨hl.1.2.1 _ (List.getElem_mem _), ?_, ?_⟩
    · show _ ⊂ (l.take (p.length + 1)).getLastD ∅
      rw [getLastD_take l ∅ _ (by omega)]
      exact isChain_getElem hl.1 p.length (by omega)
    · show l.take (p.length + 1 + 1) = l.take (p.length + 1) ++ [l[p.length + 1]'(by omega)]
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
      rfl
  · -- children
    rintro p ⟨l, hl, rfl⟩ hp M hM hPM hML
    rw [pathG_getLast, decoOf_P, hF _ hl] at hPM
    rw [pathG_getLast, decoOf_L] at hML
    have hΓ := hFext ⟨l, hl.1⟩ hl.2 (HistoriesAux.snoc ⟨l, hl.1⟩ M hM hML) M
      (HistoriesAux.snoc_isSnoc (⟨l, hl.1⟩ : History X) M hM hML) hPM
    refine ⟨decoOf F s a (l ++ [M]), by simp [decoOf_L], l ++ [M],
      ⟨(HistoriesAux.snoc ⟨l, hl.1⟩ M hM hML).2, hΓ⟩, (pathG_snoc (decoOf F s a) l M).symm⟩
  · -- feasibility
    rintro p ⟨l, hl, rfl⟩ hp
    have hg := hUg _ hl.2
    unfold DecoratedGood at hg
    rw [pathG_getLast, decoOf_a]
    refine geom_transport h (by rw [pathG_length]) ?_ ?_ ?_ hg
    · intro i
      simp only [pathFn, listFn, List.get_eq_getElem, pathG_getElem, decoOf_L, Fin.val_cast]
      rw [getLastD_take]
    · intro i
      simp only [pathFn, listFn, List.get_eq_getElem, pathG_getElem, decoOf_L, Fin.val_cast]
      rw [getLastD_take]
    · intro i
      simp only [pathFn, List.get_eq_getElem, pathG_getElem, decoOf_s, Fin.val_cast]

end DecoToTree

/-! ### Theorem 8.7, tree ⇒ decoration -/

section TreeToDeco
variable {d : ℕ}

variable (T : DTree d)

/-- One selected tree path per history (on reversed lists): extend the selected path of the
history by a child carrying the next language, if there is one. -/
noncomputable def selR : List (Set (Pt d)) → List (Deco d)
  | [] => []
  | M :: Hr =>
      if hw : ∃ w : Deco d, w.L = M ∧ (selR Hr).reverse ++ [w] ∈ T.paths then
        hw.choose :: selR Hr
      else selR Hr

/-- The selected tree path of a history (the pruning of Theorem 8.7: one child per label). -/
noncomputable def sel (H : List (Set (Pt d))) : List (Deco d) := (selR T H.reverse).reverse

theorem sel_nil : sel T [] = [] := rfl

theorem sel_snoc (H : List (Set (Pt d))) (M : Set (Pt d)) :
    sel T (H ++ [M]) = if hw : ∃ w : Deco d, w.L = M ∧ sel T H ++ [w] ∈ T.paths then
      sel T H ++ [hw.choose] else sel T H := by
  have e : sel T (H ++ [M]) = (selR T (M :: H.reverse)).reverse := by simp [sel]
  rw [e, selR]
  by_cases hw : ∃ w : Deco d, w.L = M ∧ sel T H ++ [w] ∈ T.paths
  · have hw' : ∃ w : Deco d, w.L = M ∧ (selR T H.reverse).reverse ++ [w] ∈ T.paths := hw
    rw [dite_eq_left hw, dite_eq_left hw']
    simp [sel]
  · have hw' : ¬ ∃ w : Deco d, w.L = M ∧ (selR T H.reverse).reverse ++ [w] ∈ T.paths := hw
    rw [dite_eq_right hw, dite_eq_right hw']
    rfl

theorem sel_length_le (H : List (Set (Pt d))) : (sel T H).length ≤ H.length := by
  induction H using List.reverseRecOn with
  | nil => simp [sel_nil]
  | append_singleton H M ih =>
    rw [sel_snoc]
    split_ifs
    all_goals (simp only [List.length_append, List.length_cons, List.length_nil]; omega)

/-- `H` is a nonempty list of languages whose selected path is a tree path carrying exactly the
languages of `H`. -/
def SelGood (H : List (Set (Pt d))) : Prop :=
  H ≠ [] ∧ sel T H ∈ T.paths ∧ (sel T H).map Deco.L = H

theorem selGood_snoc {H : List (Set (Pt d))} {M : Set (Pt d)} (hg : SelGood T (H ++ [M])) :
    (H = [] ∨ SelGood T H) ∧ ∃ w : Deco d, w.L = M ∧ sel T (H ++ [M]) = sel T H ++ [w] := by
  have hg' := hg
  obtain ⟨-, hp, hmap⟩ := hg'
  rw [sel_snoc] at hp hmap ⊢
  split_ifs at hp hmap ⊢ with hw
  · have hwL := hw.choose_spec.1
    rw [List.map_append, List.map_singleton, hwL] at hmap
    have hmapH := List.append_cancel_right hmap
    refine ⟨?_, hw.choose, hwL, rfl⟩
    rcases eq_or_ne H [] with hH | hH
    · exact Or.inl hH
    · refine Or.inr ⟨hH, ?_, hmapH⟩
      have hne : 1 ≤ (sel T H).length := by
        have := congrArg List.length hmapH
        rw [List.length_map] at this
        have := List.length_pos_iff.mpr hH
        omega
      have := TreesAux.dtree_prefix T _ hp (sel T H).length hne
      simpa using this
  · exfalso
    have := congrArg List.length hmap
    have := sel_length_le T H
    simp at *
    omega

theorem selGood_take {H : List (Set (Pt d))} (hg : SelGood T H) {n : ℕ} (hn : 1 ≤ n) :
    SelGood T (H.take n) ∧ sel T (H.take n) = (sel T H).take n := by
  induction H using List.reverseRecOn with
  | nil => exact absurd rfl hg.1
  | append_singleton H M ih =>
    obtain ⟨hH, w, -, hsel⟩ := selGood_snoc T hg
    have hlen : (sel T H).length = H.length := by
      have := congrArg List.length hg.2.2
      rw [hsel] at this
      simpa using this
    rcases Nat.lt_or_ge H.length n with hnl | hnl
    · rw [List.take_of_length_le (by simp; omega),
        List.take_of_length_le (by rw [hsel]; simp; omega)]
      exact ⟨hg, rfl⟩
    · rw [List.take_append_of_le_length hnl, hsel, List.take_append_of_le_length (by omega)]
      rcases hH with rfl | hH
      · simp at hnl; omega
      · exact ih hH

/-- **Theorem 8.7, (⇒)**: a protected tree gives an open neighbourhood with a `q`-good
decoration (the histories along the pruned tree). -/
theorem deco_of_tree {X : Set (Set (Pt d))} {h : ℕ → ℝ} {q : Set (Pt d) → ℝ} {K : Set (Pt d)}
    (hK : K ∈ X) {T : DTree d} (hT : IsProtectedTree X h q K T) :
    ∃ (U : Set (History X)) (s a : List (Set (Pt d)) → ℝ),
      IsQGoodDecoration X h q K hK U s a := by
  obtain ⟨hroot, hvert, hedge, hchild, hfeas⟩ := hT
  let dflt : Deco d := .mk ∅ 1 ∅ 1 0
  let U : Set (History X) := {Γ | SelGood T Γ.1}
  let s : List (Set (Pt d)) → ℝ := fun H => ((sel T H).getLastD dflt).s
  let a : List (Set (Pt d)) → ℝ := fun H => ((sel T H).getLastD dflt).a
  have hsel_ne : ∀ H, SelGood T H → sel T H ≠ [] := by
    intro H hg hnil
    have := hg.2.2
    rw [hnil] at this
    exact hg.1 this.symm
  have hlast : ∀ H (hg : SelGood T H), H.getLastD ∅ = ((sel T H).getLast (hsel_ne H hg)).L := by
    intro H hg
    conv_lhs => rw [← hg.2.2]
    rw [getLastD_eq_getLast _ _ (by simpa using hsel_ne H hg), List.getLast_map]
  -- extension by a child
  have hext : ∀ H (hg : SelGood T H) M, M ∈ X → ↑((sel T H).getLast (hsel_ne H hg)).P ⊆ M →
      M ⊂ H.getLastD ∅ → SelGood T (H ++ [M]) := by
    intro H hg M hM hPM hML
    rw [hlast H hg] at hML
    obtain ⟨w, hwM, hw⟩ := hchild _ hg.2.1 (hsel_ne H hg) M hM hPM hML
    have hex : ∃ w : Deco d, w.L = M ∧ sel T H ++ [w] ∈ T.paths := ⟨w, hwM, hw⟩
    have hs : sel T (H ++ [M]) = sel T H ++ [hex.choose] := by rw [sel_snoc, dite_eq_left hex]
    refine ⟨by simp, hs ▸ hex.choose_spec.2, ?_⟩
    rw [hs, List.map_append, hg.2.2]
    simp [hex.choose_spec.1]
  have hgK : SelGood T [K] := by
    have hex : ∃ w : Deco d, w.L = K ∧ sel T [] ++ [w] ∈ T.paths :=
      ⟨T.root, hroot, by simpa [sel_nil] using TreesAux.dtree_root_mem T⟩
    have hs : sel T [K] = [hex.choose] := by
      have := sel_snoc T [] K
      rw [dite_eq_left hex] at this
      simpa [sel_nil] using this
    refine ⟨by simp, ?_, ?_⟩
    · rw [hs]; simpa [sel_nil] using hex.choose_spec.2
    · rw [hs]; simp [hex.choose_spec.1]
  have hhead : ∀ H, SelGood T H → H.headD ∅ = K := by
    intro H hg
    have h1 := TreesAux.dtree_head T _ hg.2.1
    conv_lhs => rw [← hg.2.2]
    rw [List.headD_eq_head?_getD, List.head?_map, h1]
    simpa using hroot
  have hgetLast_mem : ∀ H (hg : SelGood T H), (sel T H).getLast (hsel_ne H hg) ∈ sel T H :=
    fun H hg => List.getLast_mem _
  refine ⟨U, s, a, fun H hH => hhead H.1 hH, ?_, hgK, ?_, ?_, ?_, ?_⟩
  · -- open
    rw [HistoriesAux.isOpen_iff]
    intro H hH
    refine ⟨↑((sel T H.1).getLast (hsel_ne _ hH)).P, Finset.finite_toSet _, ?_, ?_⟩
    · show _ ⊆ H.1.getLastD ∅
      rw [hlast _ hH]
      exact (hvert _ hH.2.1 _ (hgetLast_mem _ hH)).2.1
    · rintro Γ M ⟨hM, hML, hΓ⟩ hPM
      show SelGood T Γ.1
      rw [hΓ]
      exact hext _ hH M hM hPM hML
  · -- prefixes
    intro H hH n hn _
    exact (selGood_take T hH hn).1
  · -- cutoffs and radii
    intro H hH
    have hv := hvert _ hH.2.1 _ (hgetLast_mem _ hH)
    simp only [s, a, getLastD_eq_getLast _ _ (hsel_ne _ hH)]
    exact ⟨hv.2.2.1, hv.2.2.2.1⟩
  · -- radii increase
    rintro H hH Γ hΓ M ⟨-, -, hΓe⟩
    have hgΓ : SelGood T (H.1 ++ [M]) := hΓe ▸ hΓ
    obtain ⟨-, w, -, hsw⟩ := selGood_snoc T hgΓ
    have hne := hsel_ne _ hH
    have hdec := List.dropLast_append_getLast hne
    have hpath : (sel T H.1).dropLast ++ [(sel T H.1).getLast hne, w] ∈ T.paths := by
      have := hgΓ.2.1
      rw [hsw, ← hdec] at this
      simpa using this
    have := (hedge _ _ _ hpath).2
    simp only [a, hΓe, hsw, getLastD_eq_getLast _ _ hne]
    simpa using this
  · -- feasibility
    intro H hH
    have hne := hsel_ne _ hH
    have hF := hfeas _ hH.2.1 hne
    unfold DecoratedGood
    have hlenH : (sel T H.1).length = H.1.length := by
      have := congrArg List.length hH.2.2
      simpa using this
    have hgetL : ∀ (i : ℕ) (hi : i < H.1.length),
        H.1[i] = ((sel T H.1)[i]'(by omega)).L := by
      intro i hi
      have := List.getElem_of_eq hH.2.2.symm hi
      rw [this, List.getElem_map]
    have ha : a H.1 = ((sel T H.1).getLast hne).a := by
      simp only [a, getLastD_eq_getLast _ _ hne]
    rw [ha]
    refine geom_transport h (by rw [hlenH]) ?_ ?_ ?_ hF
    · intro i
      simp only [pathFn, listFn, List.get_eq_getElem, Fin.val_cast]
      exact hgetL _ _
    · intro i
      simp only [pathFn, listFn, List.get_eq_getElem, Fin.val_cast]
      rw [hgetL]
    · intro i
      simp only [pathFn, List.get_eq_getElem, Fin.val_cast, s]
      have hi : i.val < H.1.length := by have := i.isLt; have := List.length_pos_iff.mpr hH.1; omega
      rw [(selGood_take T hH (n := i.val + 1) (by omega)).2,
        getLastD_take _ _ _ (by omega)]

end TreeToDeco


/-! ### Corollaries 8.8 and 8.9 -/

section Obstruction
variable {d : ℕ}

/-- The root-to-leaf paths of an admissible obstruction tree rooted in `X` are chains of `X`. -/
theorem aot_paths_chain {X : Set (Set (Pt d))} :
    ∀ T : LTree (Pt d), T.Admissible X → T.label ∈ X → ∀ P ∈ T.paths, IsChain X P := by
  intro T
  induction T with
  | leaf L =>
    intro _ hL P hP
    rw [show P = [L] from hP]
    exact ⟨by simp, fun M hM => by rw [List.mem_singleton.1 hM]; exact hL,
      List.isChain_singleton L⟩
  | node L c ih =>
    intro hadm hL P hP
    obtain ⟨i, Q, hQ, rfl⟩ := hP
    obtain ⟨hiX, hilt, hiadm⟩ := hadm.1 i
    have hQc := ih i hiadm hiX Q hQ
    obtain ⟨Q', rfl⟩ := HistoriesAux.paths_head hQ
    refine ⟨by simp, ?_, ?_⟩
    · intro M hM
      rcases List.mem_cons.1 hM with rfl | hM
      · exact hL
      · exact hQc.2.1 M hM
    · exact List.isChain_cons_cons.2 ⟨hilt, hQc.2.2⟩

/-- A basic neighbourhood of `(K)` stays inside an open set `W ∋ (K)` when its tests are those of
the finite-test characterization of `W`. -/
theorem basic_sub {X : Set (Set (Pt d))} {W : Set (History X)} {H₀ : History X}
    (Fn : History X → Set (Pt d))
    (hFn : ∀ H ∈ W, ∀ Γ : History X, ∀ M, History.IsSnoc H Γ M → Fn H ⊆ M → Γ ∈ W)
    (hH₀ : H₀ ∈ W) : ∀ Γ, InBasic H₀ Fn Γ → Γ ∈ W := by
  intro Γ hΓ
  induction hΓ with
  | base => exact hH₀
  | step _ hs hM ih => exact hFn _ ih _ _ hs hM

/-- Every history of a basic neighbourhood of `(K)` begins at `K`. -/
theorem basic_head {X : Set (Set (Pt d))} {K : Set (Pt d)} (hK : K ∈ X)
    (Fn : History X → Set (Pt d)) :
    ∀ Γ, InBasic (History.single K hK) Fn Γ → Γ.1.headD ∅ = K := by
  intro Γ hΓ
  induction hΓ with
  | base => rfl
  | @step Γ Γ' M _ hs _ ih =>
    rw [hs.2.2]
    obtain ⟨x, l, hl⟩ := List.exists_cons_of_ne_nil Γ.2.1
    rw [hl] at ih ⊢
    simpa using ih

/-- A basic neighbourhood of `(K)` is closed under nonempty prefixes. -/
theorem basic_prefix {X : Set (Set (Pt d))} {K : Set (Pt d)} (hK : K ∈ X)
    (Fn : History X → Set (Pt d)) :
    ∀ Γ, InBasic (History.single K hK) Fn Γ → ∀ n, 1 ≤ n → ∀ hc : IsChain X (Γ.1.take n),
      InBasic (History.single K hK) Fn ⟨Γ.1.take n, hc⟩ := by
  intro Γ hΓ
  induction hΓ with
  | base =>
    intro n hn hc
    have : (⟨(History.single K hK).1.take n, hc⟩ : History X) = History.single K hK := by
      apply Subtype.ext
      show [K].take n = [K]
      exact List.take_of_length_le (by simp; omega)
    rw [this]
    exact InBasic.base
  | @step Γ Γ' M hb hs hM ih =>
    intro n hn hc
    rcases Nat.lt_or_ge Γ.1.length n with hlt | hle
    · have : (⟨Γ'.1.take n, hc⟩ : History X) = Γ' := by
        apply Subtype.ext
        show Γ'.1.take n = Γ'.1
        rw [hs.2.2]
        exact List.take_of_length_le (by simp; omega)
      rw [this]
      exact InBasic.step hb hs hM
    · have e : Γ'.1.take n = Γ.1.take n := by
        rw [hs.2.2, List.take_append_of_le_length hle]
      have hc' : IsChain X (Γ.1.take n) := e ▸ hc
      have := ih n hn hc'
      have e' : (⟨Γ'.1.take n, hc⟩ : History X) = ⟨Γ.1.take n, hc'⟩ := Subtype.ext e
      rw [e']
      exact this

end Obstruction

section Obstruction2
variable {d : ℕ}

/-- **Corollary 8.8, (⇐)**: a global assignment for which every admissible obstruction tree has a
good terminal history gives a protected tree. -/
theorem tree_of_assignment {X : Set (Set (Pt d))} (hXc : X.Countable) {h : ℕ → ℝ}
    {q : Set (Pt d) → ℝ} {K : Set (Pt d)} (hK : K ∈ X) (s a : List (Set (Pt d)) → ℝ)
    (h1 : ∀ H, IsChain X H → H.headD ∅ = K → 1 ≤ s H ∧ 0 ≤ a H)
    (h2 : ∀ H M, IsChain X (H ++ [M]) → H ≠ [] → H.headD ∅ = K → a H < a (H ++ [M]))
    (h3 : ∀ T : LTree (Pt d), def_aot X K T →
      ∃ P ∈ T.paths, ∃ hP : P ≠ [], DecoratedGood h q s a P hP) :
    ∃ T, IsProtectedTree X h q K T := by
  let D : Set (History X) := {G | ¬ DecoratedGood h q s a G.1 G.2.1}
  have hnot : History.single K hK ∉ closure D := by
    intro hcl
    obtain ⟨T, hT, hP⟩ := (HistoriesAux.lem_obstruction_closure_gen D _).1 hcl
    obtain ⟨P, hPT, hPne, hgood⟩ := h3 T hT
    obtain ⟨G, hGD, hGe⟩ := hP P hPT
    obtain ⟨Q, rfl⟩ := HistoriesAux.paths_head hPT
    have hGP : G.1 = T.label :: Q := by
      rw [hGe]
      have : (History.single K hK).last = T.label := hT.1.symm
      simp [History.single, ← this, History.last]
    apply hGD
    show DecoratedGood h q s a G.1 G.2.1
    revert hgood
    generalize hPne = hP'
    revert hP'
    rw [← hGP]
    intro hP' hg
    exact hg
  have hW : IsOpen (closure D)ᶜ := isClosed_closure.isOpen_compl
  have hopen := (HistoriesAux.isOpen_iff _).1 hW
  choose Fs hFfin hFsub hFext using hopen
  let Fn : History X → Set (Pt d) := fun H => if hH : H ∈ (closure D)ᶜ then Fs H hH else ∅
  have hFnT : FiniteTests Fn := by
    intro H
    by_cases hH : H ∈ (closure D)ᶜ
    · simp only [Fn, hH, ↓reduceDIte]; exact ⟨hFfin H hH, hFsub H hH⟩
    · simp only [Fn, hH, ↓reduceDIte]; exact ⟨finite_empty, empty_subset _⟩
  have hFn : ∀ H ∈ (closure D)ᶜ, ∀ Γ : History X, ∀ M, History.IsSnoc H Γ M → Fn H ⊆ M →
      Γ ∈ (closure D)ᶜ := by
    intro H hH Γ M hs hM
    simp only [Fn, hH, ↓reduceDIte] at hM
    exact hFext H hH Γ M hs hM
  let V : Set (History X) := {Γ | InBasic (History.single K hK) Fn Γ}
  have hVW : V ⊆ (closure D)ᶜ := fun Γ hΓ => basic_sub Fn hFn hnot Γ hΓ
  refine tree_of_deco hXc hK (U := V) (s := s) (a := a) ⟨fun Γ hΓ => basic_head hK Fn Γ hΓ,
    TopologicalSpace.isOpen_generateFrom_of_mem ⟨_, Fn, hFnT, rfl⟩, InBasic.base,
    fun H hH n hn hc => basic_prefix hK Fn H hH n hn hc,
    fun H hH => h1 H.1 H.2 (basic_head hK Fn H hH), ?_, ?_⟩
  · rintro H hH Γ hΓ M ⟨-, -, hΓe⟩
    have hc : IsChain X (H.1 ++ [M]) := hΓe ▸ Γ.2
    rw [hΓe]
    exact h2 H.1 M hc H.2.1 (basic_head hK Fn H hH)
  · intro H hH
    by_contra hng
    exact hVW hH (subset_closure hng)

/-- **Corollary 8.8, (⇒)**: a protected tree gives a global assignment for which every admissible
obstruction tree has a good terminal history. -/
theorem assignment_of_tree {X : Set (Set (Pt d))} {h : ℕ → ℝ}
    {q : Set (Pt d) → ℝ} {K : Set (Pt d)} (hK : K ∈ X) {T₀ : DTree d}
    (hT₀ : IsProtectedTree X h q K T₀) :
    ∃ s a : List (Set (Pt d)) → ℝ,
        (∀ H, IsChain X H → H.headD ∅ = K → 1 ≤ s H ∧ 0 ≤ a H) ∧
        (∀ H M, IsChain X (H ++ [M]) → H ≠ [] → H.headD ∅ = K → a H < a (H ++ [M])) ∧
        ∀ T : LTree (Pt d), def_aot X K T →
          ∃ P ∈ T.paths, ∃ hP : P ≠ [], DecoratedGood h q s a P hP := by
  obtain ⟨U, s, a, hUK, hUo, hUs, hUpre, hUsa, hUa, hUg⟩ := deco_of_tree hK hT₀
  let f : List (Set (Pt d)) → ℝ := fun l => if InU X U l then |a l| else 0
  have hf0 : ∀ l, 0 ≤ f l := fun l => by simp only [f]; split_ifs <;> positivity
  let A : List (Set (Pt d)) → ℝ := fun l =>
    (∑ n ∈ Finset.range (l.length + 1), f (l.take n)) + l.length
  let s' : List (Set (Pt d)) → ℝ := fun l => if InU X U l then s l else 1
  let a' : List (Set (Pt d)) → ℝ := fun l => if InU X U l then a l else A l
  have hA0 : ∀ l, 0 ≤ A l := fun l => by
    have := Finset.sum_nonneg fun n (_ : n ∈ Finset.range (l.length + 1)) => hf0 (l.take n)
    simp only [A]; positivity
  have hAsnoc : ∀ H M, A H + 1 ≤ A (H ++ [M]) ∧ f H + 1 ≤ A (H ++ [M]) := by
    intro H M
    have hsum : ∑ n ∈ Finset.range ((H ++ [M]).length + 1), f ((H ++ [M]).take n) =
        (∑ n ∈ Finset.range (H.length + 1), f (H.take n)) + f (H ++ [M]) := by
      rw [show (H ++ [M]).length + 1 = H.length + 1 + 1 by simp, Finset.sum_range_succ]
      congr 1
      · refine Finset.sum_congr rfl fun n hn => ?_
        rw [List.take_append_of_le_length (by simp at hn; omega)]
      · rw [List.take_of_length_le (by simp)]
    have hle : f H ≤ ∑ n ∈ Finset.range (H.length + 1), f (H.take n) := by
      have := Finset.single_le_sum (fun n (_ : n ∈ Finset.range (H.length + 1)) => hf0 (H.take n))
        (Finset.self_mem_range_succ H.length)
      rwa [List.take_of_length_le le_rfl] at this
    have e : A (H ++ [M]) = (∑ n ∈ Finset.range (H.length + 1), f (H.take n)) +
        f (H ++ [M]) + H.length + 1 := by
      simp only [A]; rw [hsum]; simp only [List.length_append, List.length_singleton]; push_cast
      ring
    have eA : A H = (∑ n ∈ Finset.range (H.length + 1), f (H.take n)) + H.length := rfl
    have := hf0 (H ++ [M])
    have : (0 : ℝ) ≤ H.length := Nat.cast_nonneg _
    rw [e, eA]
    constructor <;> linarith
  have hInU_take : ∀ l, InU X U l → ∀ n, 1 ≤ n → InU X U (l.take n) := fun l hl n hn =>
    ⟨isChain_take hl.1 hn, hUpre _ hl.2 n hn (isChain_take hl.1 hn)⟩
  refine ⟨s', a', ?_, ?_, ?_⟩
  · intro H _ _
    simp only [s', a']
    split_ifs with hH
    · exact hUsa _ hH.2
    · exact ⟨le_rfl, hA0 H⟩
  · intro H M hc hne hhead
    have hHc : IsChain X H := by
      have := isChain_take hc (n := H.length) (by have := List.length_pos_iff.mpr hne; omega)
      rwa [List.take_append_of_le_length le_rfl, List.take_of_length_le le_rfl] at this
    by_cases hHM : InU X U (H ++ [M])
    · have hH : InU X U H := by
        have := hInU_take _ hHM H.length (by have := List.length_pos_iff.mpr hne; omega)
        rwa [List.take_append_of_le_length le_rfl, List.take_of_length_le le_rfl] at this
      simp only [a', if_pos hH, if_pos hHM]
      have hlt : M ⊂ H.getLastD ∅ := by
        have hi := isChain_getElem hc (H.length - 1)
          (by simp; have := List.length_pos_iff.mpr hne; omega)
        have hlen := List.length_pos_iff.mpr hne
        rw [List.getElem_append_right (by omega), List.getElem_append_left (by omega)] at hi
        rw [getLastD_eq_getLast _ _ hne, List.getLast_eq_getElem]
        simpa [show H.length - 1 + 1 - H.length = 0 by omega] using hi
      exact hUa ⟨H, hHc⟩ hH.2 ⟨H ++ [M], hc⟩ hHM.2 M
        ⟨hc.2.1 M (by simp), hlt, rfl⟩
    · simp only [a', if_neg hHM]
      by_cases hH : InU X U H
      · simp only [if_pos hH]
        have := (hAsnoc H M).2
        simp only [f, if_pos hH] at this
        linarith [le_abs_self (a H)]
      · simp only [if_neg hH]
        linarith [(hAsnoc H M).1]
  · intro T hT
    let D : Set (History X) := Uᶜ
    have hnot : History.single K hK ∉ closure D := by
      rw [closure_compl, Set.mem_compl_iff, not_not, hUo.interior_eq]
      exact hUs
    rw [HistoriesAux.lem_obstruction_closure_gen] at hnot
    push Not at hnot
    have hlast : (History.single K hK).last = K := rfl
    rw [hlast] at hnot
    obtain ⟨P, hPT, hP⟩ := hnot T hT
    have hPc : IsChain X P := aot_paths_chain T hT.2 (hT.1 ▸ hK) P hPT
    obtain ⟨Q, rfl⟩ := HistoriesAux.paths_head hPT
    have hPU : (⟨T.label :: Q, hPc⟩ : History X) ∈ U := by
      by_contra hn
      apply hP _ hn
      show T.label :: Q = [K] ++ (T.label :: Q).tail
      rw [hT.1]; rfl
    refine ⟨_, hPT, hPc.1, ?_⟩
    have hg := hUg _ hPU
    unfold DecoratedGood at hg ⊢
    have hin0 : InU X U (T.label :: Q) := ⟨hPc, hPU⟩
    have ha : a' (T.label :: Q) = a (T.label :: Q) := by simp only [a', if_pos hin0]
    have hs : (fun i : Fin ((T.label :: Q).length - 1 + 1) =>
        s' ((T.label :: Q).take (i.val + 1))) =
        fun i => s ((T.label :: Q).take (i.val + 1)) := by
      funext i
      have hin := hInU_take _ hin0 (i.val + 1) (by omega)
      simp only [s', if_pos hin]
    rw [ha, hs]
    exact hg

end Obstruction2

/-! ### Necessity of Theorem 8.1: the White strategy induced by a committed generator -/

section Necessity
variable {d : ℕ}

/-- `outsOf` of an extended list. -/
theorem outsOf_snoc (G : Generator (Pt d)) (l : List (Pt d)) (x : Pt d) :
    outsOf G (l ++ [x]) = outsOf G l ∪ {G (l ++ [x])} := by
  ext y
  simp only [outsOf, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff, List.length_append,
    List.length_singleton]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rcases Nat.lt_or_ge i l.length with h | h
    · left; exact ⟨i, h, by rw [List.take_append_of_le_length (by omega)]⟩
    · right; rw [List.take_of_length_le (by simp; omega)]
  · rintro (⟨i, hi, rfl⟩ | rfl)
    · exact ⟨i, by omega, by rw [List.take_append_of_le_length (by omega)]⟩
    · exact ⟨l.length, by omega, by rw [List.take_of_length_le (by simp)]⟩

/-- A fresh output is not an earlier output. -/
theorem fresh_not_outs {G : Generator (Pt d)} (hG : G.Fresh) (l : List (Pt d)) (x : Pt d) :
    G (l ++ [x]) ∉ outsOf G l ∧ G (l ++ [x]) ∉ l ++ [x] := by
  have hf := SeparationAux.fresh_list hG (l ++ [x]) (t := l.length) (by simp)
  rw [show l.length + 1 = (l ++ [x]).length by simp, List.take_length] at hf
  refine ⟨?_, hf.1⟩
  rintro ⟨i, hi, hy⟩
  apply hf.2 i hi
  rw [List.take_append_of_le_length (by omega), hy]

variable (S : StopGame d) (G : Generator (Pt d)) (pre : List (Pt d))

/-- One step of the White strategy induced by `G` after the prefix `pre`: Black's claim is the
next input, and `G`'s output is White's reply when it is free. -/
noncomputable def genStep (acc : S.State × List (Pt d)) :
    BMove d → (S.State × List (Pt d)) × Option (Pt d)
  | .claim x =>
      let st₁ : S.State := ⟨acc.1.level, insert x acc.1.black, acc.1.white⟩
      let rep : Option (Pt d) :=
        if S.Free st₁ (G (pre ++ acc.2 ++ [x])) then some (G (pre ++ acc.2 ++ [x])) else none
      ((S.afterClaim acc.1 x rep, acc.2 ++ [x]), rep)
  | .down =>
      ((if h : 0 < acc.1.level.val then
          ⟨⟨acc.1.level.val - 1, by have := acc.1.level.isLt; omega⟩, acc.1.black, acc.1.white⟩
        else acc.1, acc.2), none)

/-- Replaying Black's moves against the induced strategy (state, claims so far, last reply). -/
noncomputable def genRun (ms : List (BMove d)) : (S.State × List (Pt d)) × Option (Pt d) :=
  ms.foldl (fun acc m => genStep S G pre acc.1 m) ((S.init, []), none)

/-- The White strategy induced by `G` after the prefix `pre`. -/
noncomputable def genStrat : WStrategy d := fun ms => (genRun S G pre ms).2

theorem genRun_append (ms : List (BMove d)) (m : BMove d) :
    genRun S G pre (ms ++ [m]) = genStep S G pre (genRun S G pre ms).1 m := by
  simp [genRun, List.foldl_append]

end Necessity

section NecInv
variable {d r : ℕ} (Ls : Fin (r + 1) → Set (Pt d)) (qs : Fin (r + 1) → ℝ)
  (rects : Fin (r + 1) → Finset (Rect d)) (G : Generator (Pt d)) (pre : List (Pt d))

/-- The invariant of the strategy induced by a committed generator, along legal plays. -/
theorem gen_inv (hanti : Antitone Ls) (hG : G.Fresh)
    (hvalid : ∀ j : Fin (r + 1), ∀ cl : List (Pt d), (∀ c ∈ cl, c ∈ Ls j) → cl ≠ [] →
      G (pre ++ cl) ∈ Ls j)
    {ms : List (BMove d)} {st : (packetGame Ls qs rects).State}
    (hR : (packetGame Ls qs rects).Reach (genStrat (packetGame Ls qs rects) G pre) ms st) :
    (genRun (packetGame Ls qs rects) G pre ms).1.1 = st ∧
    st.black = {x | x ∈ (genRun (packetGame Ls qs rects) G pre ms).1.2} ∧
    (∀ c ∈ (genRun (packetGame Ls qs rects) G pre ms).1.2, c ∈ Ls st.level) ∧
    st.white ⊆ outsOf G (pre ++ (genRun (packetGame Ls qs rects) G pre ms).1.2) ∧
    (∀ y ∈ outsOf G (pre ++ (genRun (packetGame Ls qs rects) G pre ms).1.2), y ∉ outsOf G pre →
      y ∈ packetSupport Ls rects → y ∈ st.white) := by
  set S := packetGame Ls qs rects with hS
  induction hR with
  | nil =>
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · simp [genRun, StopGame.init, StopGame.State.black]
    · simp [genRun]
    · simp [StopGame.init, StopGame.State.white]
    · intro y hy hy'; simp [genRun] at hy; exact absurd hy hy'
  | @claim ms st x hreach hfree hleg ih =>
    obtain ⟨hrun, hB, hC, hW, hO⟩ := ih
    rcases st with ⟨lvl, b, w⟩
    simp only [StopGame.State.black, StopGame.State.white, StopGame.State.level] at hB hC hW hO
    set cl := (genRun S G pre ms).1.2 with hcl
    have hrun' : (genRun S G pre ms).1 = (⟨lvl, b, w⟩, cl) := Prod.ext hrun rfl
    have happ : genRun S G pre (ms ++ [BMove.claim x]) =
        genStep S G pre (⟨lvl, b, w⟩, cl) (BMove.claim x) := by rw [genRun_append, hrun']
    have hσ : genStrat S G pre (ms ++ [BMove.claim x]) =
        (genStep S G pre (⟨lvl, b, w⟩, cl) (BMove.claim x)).2 := by
      show (genRun S G pre (ms ++ [BMove.claim x])).2 = _; rw [happ]
    rw [hσ, happ]
    have hxL : x ∈ Ls lvl := hfree.1.2
    have hcl' : ∀ c ∈ cl ++ [x], c ∈ Ls lvl := by
      intro c hc
      rcases List.mem_append.1 hc with hc | hc
      · exact hC c hc
      · rw [List.mem_singleton.1 hc]; exact hxL
    have hyL : G (pre ++ cl ++ [x]) ∈ Ls lvl := by
      rw [List.append_assoc]; exact hvalid lvl _ hcl' (by simp)
    have hyfresh := fresh_not_outs hG (pre ++ cl) x
    by_cases hy : S.Free ⟨lvl, insert x b, w⟩ (G (pre ++ cl ++ [x]))
    · have hstep : genStep S G pre (⟨lvl, b, w⟩, cl) (BMove.claim x) =
          ((⟨lvl, insert x b, insert (G (pre ++ cl ++ [x])) w⟩, cl ++ [x]),
            some (G (pre ++ cl ++ [x]))) := by
        simp only [genStep, StopGame.State.level, StopGame.State.black, StopGame.State.white,
          StopGame.afterClaim, hy, ↓reduceIte]
        rfl
      rw [hstep]
      simp only [StopGame.State.black, StopGame.State.white, StopGame.State.level]
      refine ⟨rfl, ?_, hcl', ?_, ?_⟩
      · show insert x b = {z | z ∈ cl ++ [x]}
        rw [hB]; ext z; simp [or_comm]
      · rw [← List.append_assoc, outsOf_snoc]
        intro z hz
        rcases Set.mem_insert_iff.1 hz with rfl | hz
        · exact Or.inr rfl
        · exact Or.inl (hW hz)
      · intro z hz hz' hzU
        rw [← List.append_assoc, outsOf_snoc] at hz
        rcases hz with hz | hz
        · exact Set.mem_insert_of_mem _ (hO z hz hz' hzU)
        · rw [Set.mem_singleton_iff.1 hz]; exact Set.mem_insert _ _
    · have hstep : genStep S G pre (⟨lvl, b, w⟩, cl) (BMove.claim x) =
          ((⟨lvl, insert x b, w⟩, cl ++ [x]), none) := by
        simp only [genStep, StopGame.State.level, StopGame.State.black, StopGame.State.white,
          StopGame.afterClaim, hy, ↓reduceIte]
        rfl
      rw [hstep]
      simp only [StopGame.State.black, StopGame.State.white, StopGame.State.level]
      refine ⟨rfl, ?_, hcl', ?_, ?_⟩
      · show insert x b = {z | z ∈ cl ++ [x]}
        rw [hB]; ext z; simp [or_comm]
      · exact fun z hz => by rw [← List.append_assoc]; exact SeparationAux.outsOf_mono G _ _ (hW hz)
      · intro z hz hz' hzU
        rw [← List.append_assoc, outsOf_snoc] at hz
        rcases hz with hz | hz
        · exact hO z hz hz' hzU
        · exfalso
          rw [Set.mem_singleton_iff.1 hz] at hzU
          apply hy
          refine ⟨⟨hzU, hyL⟩, ?_, fun hw => hyfresh.1 (hW hw)⟩
          intro hb
          rcases Set.mem_insert_iff.1 hb with hb | hb
          · exact hyfresh.2 (by rw [hb]; simp)
          · rw [hB] at hb
            exact hyfresh.2 (List.mem_append_left _ (List.mem_append_right _ hb))
  | @down ms st i hreach hi ih =>
    obtain ⟨hrun, hB, hC, hW, hO⟩ := ih
    rcases st with ⟨lvl, b, w⟩
    simp only [StopGame.State.black, StopGame.State.white, StopGame.State.level] at hB hC hW hO
    set cl := (genRun S G pre ms).1.2 with hcl
    have hrun' : (genRun S G pre ms).1 = (⟨lvl, b, w⟩, cl) := Prod.ext hrun rfl
    have happ : genRun S G pre (ms ++ [BMove.down]) =
        genStep S G pre (⟨lvl, b, w⟩, cl) BMove.down := by rw [genRun_append, hrun']
    rw [happ]
    change i.val + 1 = lvl.val at hi
    have hpos : 0 < lvl.val := by omega
    have hstep : genStep S G pre (⟨lvl, b, w⟩, cl) BMove.down =
        ((⟨⟨lvl.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) lvl.isLt⟩, b, w⟩, cl), none) := by
      simp only [genStep, StopGame.State.level, StopGame.State.black, StopGame.State.white, hpos,
        ↓reduceDIte]
    rw [hstep]
    have hfi : (⟨lvl.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) lvl.isLt⟩ :
        Fin ((packetGame Ls qs rects).r + 1)) = i := Fin.ext (by show lvl.val - 1 = i.val; omega)
    refine ⟨by rw [hfi]; rfl, hB, ?_, hW, hO⟩
    intro c hc
    show c ∈ Ls i
    exact hanti (Fin.le_iff_val_le_val.2 (by omega)) (hC c hc)

/-- Geometric feasibility from commitments (the core of the necessity proof of Theorem 8.1): if
every level `j` of a nonincreasing chain has a committing prefix `pres j` (validity and density
commitments of Lemma 8.13), the actual prefix `pre` extends every `pres j` inside `Ls j`, and every
point used by `pre` lies in `Q_a`, then White wins every eligible packet outside `Q_a` by playing
the generator's outputs on Black's claims. -/
theorem feasible_of_commit {h : ℕ → ℝ} (ss : Fin (r + 1) → ℝ) (a : ℝ)
    (hanti : Antitone Ls) (hG : G.Fresh) (pres : Fin (r + 1) → List (Pt d))
    (hpre : ∀ j, ∃ rest, pre = pres j ++ rest ∧ ∀ x ∈ rest, x ∈ Ls j)
    (hval : ∀ j cont, (∀ x ∈ cont, x ∈ Ls j) → ∀ k < cont.length,
      G ((pres j ++ cont).take ((pres j).length + k + 1)) ∈ Ls j)
    (hden : ∀ j cont, (∀ x ∈ cont, x ∈ Ls j) → ∀ R : Rect d, ss j * h R.vol ≤ mass (Ls j) R →
      (Ls j ∩ R.pts ⊆ {x | x ∈ pres j ++ cont} ∪ outsOf G (pres j ++ cont)) →
      qs j * (mass (Ls j) R : ℝ) ≤ ((outsOf G (pres j ++ cont) ∩ Ls j ∩ R.pts).ncard : ℝ))
    (hcore : usedBy G pre ⊆ core d a) :
    GeomFeasible h Ls qs ss a := by
  intro rects hrects
  set S := packetGame Ls qs rects with hS
  have hvalid : ∀ j : Fin (r + 1), ∀ cl : List (Pt d), (∀ c ∈ cl, c ∈ Ls j) → cl ≠ [] →
      G (pre ++ cl) ∈ Ls j := by
    intro j cl hcl hne
    obtain ⟨rest, hrest, hrestL⟩ := hpre j
    have hc : ∀ x ∈ rest ++ cl, x ∈ Ls j := by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hrestL x hx
      · exact hcl x hx
    have hlen := List.length_pos_iff.mpr hne
    have := hval j (rest ++ cl) hc ((rest ++ cl).length - 1) (by simp; omega)
    rw [List.take_of_length_le (by simp; omega)] at this
    rw [hrest]; simpa [List.append_assoc] using this
  refine ⟨genStrat S G pre, fun ms st hR => ?_⟩
  obtain ⟨hrun, hB, hC, hW, hO⟩ := gen_inv Ls qs rects G pre hanti hG hvalid hR
  have hrun' : (genRun S G pre ms).1 = (st, (genRun S G pre ms).1.2) := Prod.ext hrun rfl
  refine ⟨fun x _ => ?_, fun hstop R hR' => ?_⟩
  · show S.LegalReply _ (genRun S G pre (ms ++ [BMove.claim x])).2
    rw [genRun_append, hrun']
    simp only [genStep]
    split_ifs with hy
    · exact hy
    · trivial
  · set cl := (genRun S G pre ms).1.2 with hcl
    set i := st.level with hi
    obtain ⟨rest, hrest, hrestL⟩ := hpre i
    have hcont : ∀ x ∈ rest ++ cl, x ∈ Ls i := by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hrestL x hx
      · exact hC x hx
    have hRi := hrects i R hR'
    have hpi : pres i ++ (rest ++ cl) = pre ++ cl := by rw [← List.append_assoc, ← hrest]
    have hocc : Ls i ∩ R.pts ⊆ {x | x ∈ pres i ++ (rest ++ cl)} ∪
        outsOf G (pres i ++ (rest ++ cl)) := by
      rw [hpi]
      intro z hz
      have hzU : z ∈ packetSupport Ls rects := Set.mem_iUnion.2 ⟨i, Set.mem_iUnion₂.2 ⟨R, hR', hz⟩⟩
      rcases hstop (show z ∈ S.visible i from ⟨hzU, hz.1⟩) with hb | hw
      · rw [hB] at hb; left; exact List.mem_append_right _ hb
      · right; exact hW hw
    have hq := hden i (rest ++ cl) hcont R hRi.2 hocc
    rw [hpi] at hq
    refine hq.trans ?_
    have hfin : (st.white ∩ Ls i ∩ R.pts).Finite := (BasicAux.rect_pts_finite R).inter_of_right _
    have hsub : outsOf G (pre ++ cl) ∩ Ls i ∩ R.pts ⊆ st.white ∩ Ls i ∩ R.pts := by
      intro z hz
      refine ⟨⟨?_, hz.1.2⟩, hz.2⟩
      by_cases hzo : z ∈ outsOf G pre
      · exact absurd (hcore (Or.inr hzo)) (Set.disjoint_left.1 hRi.1 hz.2)
      · exact hO z hz.1.1 hzo (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion₂.2 ⟨R, hR', ⟨hz.1.2, hz.2⟩⟩⟩)
    exact_mod_cast Set.ncard_le_ncard hsub hfin

end NecInv


section NecTree
variable {d : ℕ}

/-- The committing prefix of a history: at each new language `M`, append the extension `E M xs`
to the current prefix `xs`. -/
def preOf {β : Type*} (E : β → List (Pt d) → List (Pt d)) (H : List β) : List (Pt d) :=
  H.foldl (fun xs M => xs ++ E M xs) []

theorem preOf_snoc {β : Type*} (E : β → List (Pt d) → List (Pt d)) (H : List β)
    (M : β) : preOf E (H ++ [M]) = preOf E H ++ E M (preOf E H) := by
  simp [preOf, List.foldl_append]

/-- A bound on the coordinates of all points used by the run on `l`. -/
noncomputable def bnd (G : Generator (Pt d)) (l : List (Pt d)) : ℝ :=
  ∑ p ∈ (SeparationAux.usedBy_finite G l).toFinset, ∑ i, |((p i : ℤ) : ℝ)|

theorem bnd_nonneg (G : Generator (Pt d)) (l : List (Pt d)) : 0 ≤ bnd G l :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem mem_core_of_used {G : Generator (Pt d)} {l : List (Pt d)} {p : Pt d}
    (hp : p ∈ usedBy G l) {a : ℝ} (ha : bnd G l ≤ a) : p ∈ core d a := by
  intro i
  have h1 : |((p i : ℤ) : ℝ)| ≤ ∑ j, |((p j : ℤ) : ℝ)| :=
    Finset.single_le_sum (f := fun j => |((p j : ℤ) : ℝ)|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
  have h2 : ∑ j, |((p j : ℤ) : ℝ)| ≤ bnd G l :=
    Finset.single_le_sum (f := fun p : Pt d => ∑ j, |((p j : ℤ) : ℝ)|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
      ((SeparationAux.usedBy_finite G l).mem_toFinset.2 hp)
  linarith

/-- Sum of a nonnegative quantity over the prefixes of a history, plus its length (a radius that
strictly increases along one-step extensions). -/
noncomputable def sumPref {β : Type*} (f : List β → ℝ) (H : List β) : ℝ :=
  (∑ n ∈ Finset.range (H.length + 1), f (H.take n)) + H.length

theorem sumPref_snoc {β : Type*} (f : List β → ℝ) (H : List β) (M : β) :
    sumPref f (H ++ [M]) = sumPref f H + f (H ++ [M]) + 1 := by
  unfold sumPref
  rw [show (H ++ [M]).length + 1 = H.length + 1 + 1 by simp, Finset.sum_range_succ]
  have hs : ∑ n ∈ Finset.range (H.length + 1), f ((H ++ [M]).take n) =
      ∑ n ∈ Finset.range (H.length + 1), f (H.take n) :=
    Finset.sum_congr rfl fun n hn => by
      rw [List.take_append_of_le_length (by simp at hn; omega)]
  rw [hs, List.take_of_length_le (by simp)]
  simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
  ring

theorem le_sumPref {β : Type*} {f : List β → ℝ} (hf : ∀ l, 0 ≤ f l) (H : List β) :
    f H ≤ sumPref f H ∧ 0 ≤ sumPref f H := by
  unfold sumPref
  have h1 := Finset.single_le_sum (fun n (_ : n ∈ Finset.range (H.length + 1)) => hf (H.take n))
    (Finset.self_mem_range_succ H.length)
  rw [List.take_of_length_le le_rfl] at h1
  have : (0 : ℝ) ≤ H.length := Nat.cast_nonneg _
  constructor <;> linarith [hf H]

/-- The admissibility of a history for the committing prefixes: each new language contains the
committing prefix of the history before it. -/
def AdmP (E : Set (Pt d) → List (Pt d) → List (Pt d)) (H : List (Set (Pt d))) : Prop :=
  ∀ i (hi : i + 1 < H.length), ∀ x ∈ preOf E (H.take (i + 1)), x ∈ H[i + 1]

theorem admP_take {E : Set (Pt d) → List (Pt d) → List (Pt d)} {H : List (Set (Pt d))}
    (hH : AdmP E H) (n : ℕ) : AdmP E (H.take n) := by
  intro i hi x hx
  simp only [List.length_take] at hi
  rw [List.take_take, show min (i + 1) n = i + 1 by omega] at hx
  rw [List.getElem_take]
  exact hH i (by omega) x hx

theorem admP_snoc {E : Set (Pt d) → List (Pt d) → List (Pt d)} {H : List (Set (Pt d))}
    {M : Set (Pt d)} (hH : AdmP E H) (hM : ∀ x ∈ preOf E H, x ∈ M) : AdmP E (H ++ [M]) := by
  intro i hi x hx
  simp only [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_or_ge (i + 1) H.length with h | h
  · rw [List.take_append_of_le_length (by omega)] at hx
    rw [List.getElem_append_left h]
    exact hH i h x hx
  · have hi' : i + 1 = H.length := by omega
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)] at hx
    rw [List.getElem_append_right (by omega)]
    simpa [hi'] using hM x hx

/-- Entries of a chain decrease. -/
theorem chain_anti {α : Type*} {X : Set (Set α)} {H : List (Set α)} (hc : IsChain X H) :
    ∀ i j (hi : i < H.length) (hj : j < H.length), i ≤ j → H[j] ⊆ H[i] := by
  intro i j hi hj hij
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    exact (List.isChain_iff_getElem.1 hc.2.2 (i + m) (by omega)).subset.trans (ih (by omega) (by omega))

end NecTree

/-- **Theorem 8.1(2)**, the decoration: a generator achieving `α` gives, for every `K`, an open
neighbourhood of `(K)` with a `q`-good decoration, for every quota `q` with `q = 0` or
`q < α` pointwise (protected sets = committing prefixes of Lemma 8.13). -/
theorem nec_deco {d : ℕ} {X : Set (Set (Pt d))} (hX : LangClass X)
    {g : ℝ → ℝ} (hg1 : ∀ x, 1 ≤ x → 1 ≤ g x)
    (q α : Set (Pt d) → ℝ) (hq : ∀ L, q L = 0 ∨ q L < α L)
    (G : Generator (Pt d)) (hG : G ∈ ValidGen X)
    (hGK : ∀ K ∈ X, Guarantees (dH (hLog g)) G K (α K)) {K : Set (Pt d)} (hK : K ∈ X) :
    ∃ (U : Set (History X)) (s a : List (Set (Pt d)) → ℝ),
      IsQGoodDecoration X (hLog g) q K hK U s a := by
  have hcomm : ∀ M, M ∈ X → ∀ xs : List (Pt d), (∀ x ∈ xs, x ∈ M) →
      ∃ ext : List (Pt d), ∃ s : ℝ, 1 ≤ s ∧ (∀ x ∈ ext, x ∈ M) ∧
        ∀ cont : List (Pt d), (∀ x ∈ cont, x ∈ M) →
          (∀ j < cont.length, G ((xs ++ ext ++ cont).take ((xs ++ ext).length + j + 1)) ∈ M) ∧
          ∀ R : Rect d, s * (hLog g) R.vol ≤ mass M R →
            (M ∩ R.pts ⊆ {x | x ∈ xs ++ ext ++ cont} ∪ outsOf G (xs ++ ext ++ cont)) →
            q M * (mass M R : ℝ) ≤ ((outsOf G (xs ++ ext ++ cont) ∩ M ∩ R.pts).ncard : ℝ) :=
    fun M hM xs hxs => hd_commitments hX hg1 G hG hM (hGK M hM) (hq M) xs hxs
  choose extF sF hsF hextF hcomF using hcomm
  let E : Set (Pt d) → List (Pt d) → List (Pt d) := fun M xs =>
    if h : M ∈ X ∧ ∀ x ∈ xs, x ∈ M then extF M h.1 xs h.2 else []
  let cutF : Set (Pt d) → List (Pt d) → ℝ := fun M xs =>
    if h : M ∈ X ∧ ∀ x ∈ xs, x ∈ M then sF M h.1 xs h.2 else 1
  have hE : ∀ M xs (h : M ∈ X ∧ ∀ x ∈ xs, x ∈ M), E M xs = extF M h.1 xs h.2 :=
    fun M xs h => dif_pos h
  have hcut : ∀ M xs (h : M ∈ X ∧ ∀ x ∈ xs, x ∈ M), cutF M xs = sF M h.1 xs h.2 :=
    fun M xs h => dif_pos h
  have hEsub : ∀ M xs, ∀ x ∈ E M xs, x ∈ M := by
    intro M xs x hx
    simp only [E] at hx
    split_ifs at hx with h
    · exact hextF _ _ _ _ x hx
    · simp at hx
  have hcut1 : ∀ M xs, 1 ≤ cutF M xs := by
    intro M xs
    simp only [cutF]
    split_ifs with h
    · exact hsF _ _ _ _
    · exact le_rfl
  let pre : List (Set (Pt d)) → List (Pt d) := preOf E
  let s : List (Set (Pt d)) → ℝ := fun H => cutF (H.getLastD ∅) (pre H.dropLast)
  let a : List (Set (Pt d)) → ℝ := sumPref (fun l => bnd G (pre l))
  let U : Set (History X) := {Γ | Γ.1.headD ∅ = K ∧ AdmP E Γ.1}
  have hvert : ∀ H : List (Set (Pt d)), IsChain X H → AdmP E H → ∀ j (hj : j < H.length),
      H[j] ∈ X ∧ ∀ x ∈ pre (H.take j), x ∈ H[j] := by
    intro H hc hA j hj
    refine ⟨hc.2.1 _ (List.getElem_mem _), ?_⟩
    rcases j with _ | j
    · simp [pre, preOf]
    · exact hA j hj
  have hpre_last : ∀ H : List (Set (Pt d)), IsChain X H → AdmP E H →
      ∀ x ∈ pre H, x ∈ H.getLastD ∅ := by
    intro H hc hA x hx
    have hlen := List.length_pos_iff.mpr hc.1
    have e : H = H.take (H.length - 1) ++ [H[H.length - 1]] := by
      rw [List.take_concat_get' H _ (by omega), List.take_of_length_le (by omega)]
    have hv := hvert H hc hA (H.length - 1) (by omega)
    rw [getLastD_eq_getLast _ _ hc.1, List.getLast_eq_getElem]
    have hx' : x ∈ pre (H.take (H.length - 1) ++ [H[H.length - 1]]) := by rw [← e]; exact hx
    simp only [pre] at hx'
    rw [preOf_snoc] at hx'
    rcases List.mem_append.1 hx' with hx' | hx'
    · exact hv.2 x hx'
    · exact hEsub _ _ x hx'
  have hrest : ∀ H : List (Set (Pt d)), IsChain X H → ∀ j (hj : j < H.length),
      ∃ rest, pre H = pre (H.take (j + 1)) ++ rest ∧ ∀ x ∈ rest, x ∈ H[j] := by
    intro H hc j hj
    have key : ∀ m, j + 1 + m ≤ H.length → ∃ rest, pre (H.take (j + 1 + m)) =
        pre (H.take (j + 1)) ++ rest ∧ ∀ x ∈ rest, x ∈ H[j] := by
      intro m
      induction m with
      | zero => intro _; exact ⟨[], by simp, by simp⟩
      | succ m ih =>
        intro hm
        obtain ⟨rest, hr, hrL⟩ := ih (by omega)
        refine ⟨rest ++ E H[j + 1 + m] (pre (H.take (j + 1 + m))), ?_, ?_⟩
        · rw [show j + 1 + (m + 1) = j + 1 + m + 1 by omega, ← List.take_concat_get' H _ (by omega)]
          simp only [pre] at hr ⊢
          rw [preOf_snoc, hr, List.append_assoc]
        · intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact hrL x hx
          · exact chain_anti hc j (j + 1 + m) hj (by omega) (by omega) (hEsub _ _ x hx)
    obtain ⟨rest, hr, hrL⟩ := key (H.length - (j + 1)) (by omega)
    rw [show j + 1 + (H.length - (j + 1)) = H.length by omega,
      List.take_of_length_le le_rfl] at hr
    exact ⟨rest, hr, hrL⟩
  have hpj : ∀ H : List (Set (Pt d)), IsChain X H → AdmP E H → ∀ j (hj : j < H.length),
      ∃ hv : H[j] ∈ X ∧ ∀ x ∈ pre (H.take j), x ∈ H[j],
        pre (H.take (j + 1)) = pre (H.take j) ++ extF H[j] hv.1 (pre (H.take j)) hv.2 ∧
        s (H.take (j + 1)) = sF H[j] hv.1 (pre (H.take j)) hv.2 := by
    intro H hc hA j hj
    have hv := hvert H hc hA j hj
    refine ⟨hv, ?_, ?_⟩
    · rw [← List.take_concat_get' H j hj]
      simp only [pre]
      rw [preOf_snoc, hE _ _ hv]
    · show cutF ((H.take (j + 1)).getLastD ∅) (pre (H.take (j + 1)).dropLast) = _
      rw [getLastD_take H ∅ j hj, ← List.take_concat_get' H j hj, List.dropLast_concat]
      exact hcut _ _ hv
  have hhead_ne : ∀ H : List (Set (Pt d)), H ≠ [] → ∀ M : Set (Pt d),
      (H ++ [M]).headD ∅ = H.headD ∅ := by
    intro H hH M
    obtain ⟨x, l, rfl⟩ := List.exists_cons_of_ne_nil hH
    simp
  have hhead_take : ∀ H : List (Set (Pt d)), ∀ n, 1 ≤ n → (H.take n).headD ∅ = H.headD ∅ := by
    intro H n hn
    cases H with
    | nil => simp
    | cons x l =>
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
      simp
  refine ⟨U, s, a, fun H hH => hH.1, ?_, ⟨rfl, fun i hi => by simp [History.single] at hi⟩,
    fun H hH n hn _ => ⟨(hhead_take H.1 n hn).trans hH.1, admP_take hH.2 n⟩,
    fun H _ => ⟨hcut1 _ _, (le_sumPref (fun l => bnd_nonneg G _) H.1).2⟩, ?_, ?_⟩
  · -- open
    rw [HistoriesAux.isOpen_iff]
    intro H hH
    refine ⟨{x | x ∈ pre H.1}, List.finite_toSet _, hpre_last H.1 H.2 hH.2, ?_⟩
    rintro Γ M ⟨-, -, hΓ⟩ hPM
    show Γ.1.headD ∅ = K ∧ AdmP E Γ.1
    rw [hΓ]
    exact ⟨(hhead_ne H.1 H.2.1 M).trans hH.1, admP_snoc hH.2 hPM⟩
  · -- radii increase
    rintro H _ Γ _ M ⟨-, -, hΓe⟩
    rw [hΓe]
    simp only [a]
    rw [sumPref_snoc]
    linarith [bnd_nonneg G (pre (H.1 ++ [M]))]
  · -- feasibility
    intro H hH
    unfold DecoratedGood
    have hlen := List.length_pos_iff.mpr H.2.1
    refine feasible_of_commit (listFn H.1 H.2.1) (fun i => q (listFn H.1 H.2.1 i)) G (pre H.1)
      (fun i => s (H.1.take (i.val + 1))) (a H.1) ?_ hG.1
      (fun j => pre (H.1.take (j.val + 1))) ?_ ?_ ?_ ?_
    · intro i j hij
      simp only [listFn, List.get_eq_getElem]
      exact chain_anti H.2 i.val j.val (by omega) (by omega) hij
    · intro j
      simp only [listFn, List.get_eq_getElem]
      exact hrest H.1 H.2 j.val (by omega)
    · intro j cont hcont k hk
      simp only [listFn, List.get_eq_getElem] at hcont ⊢
      obtain ⟨hv, hp, -⟩ := hpj H.1 H.2 hH.2 j.val (by omega)
      rw [hp]
      exact (hcomF _ hv.1 _ hv.2 cont hcont).1 k hk
    · intro j cont hcont R hR hocc
      simp only [listFn, List.get_eq_getElem] at hcont hR hocc ⊢
      obtain ⟨hv, hp, hs⟩ := hpj H.1 H.2 hH.2 j.val (by omega)
      rw [hs] at hR
      rw [hp] at hocc ⊢
      exact (hcomF _ hv.1 _ hv.2 cont hcont).2 R hR hocc
    · intro p hp
      exact mem_core_of_used hp (le_sumPref (fun l => bnd_nonneg G _) H.1).1


/-! ### Theorem 8.2, necessity: protected trees on accuracy copies from a generator -/

section CopyNec
variable {d : ℕ}

theorem copyQuota_cases (α : Set (Pt d) → ℝ) (L : Set (Pt d)) (n : ℕ) (hn : 1 ≤ n) :
    copyQuota α L n = 0 ∨ (0 ≤ copyQuota α L n ∧ copyQuota α L n < α L) := by
  unfold copyQuota
  have hpos : (0 : ℝ) < 1 / n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  by_cases h : α L - 1 / n ≤ 0
  · left; exact max_eq_right h
  · right
    push Not at h
    rw [max_eq_left h.le]
    constructor <;> linarith

/-- The admissible copy histories: rooted at `(K,k)`, copies of languages of `X` with indices
`≥ 1`, each step to a compatible copy (monotone relation) for the committing prefix so far. -/
def CopyOK (X : Set (Set (Pt d))) (E : Set (Pt d) × ℕ → List (Pt d) → List (Pt d))
    (K : Set (Pt d)) (k : ℕ) (C : List (Set (Pt d) × ℕ)) : Prop :=
  C.head? = some (K, k) ∧ (∀ c ∈ C, c.1 ∈ X ∧ 1 ≤ c.2) ∧
  ∀ i (hi : i + 1 < C.length), CompatibleCopy {x | x ∈ preOf E (C.take (i + 1))}
    C[i].1 C[i].2 C[i + 1].1 C[i + 1].2

theorem copyOK_take {X : Set (Set (Pt d))} {E : Set (Pt d) × ℕ → List (Pt d) → List (Pt d)}
    {K : Set (Pt d)} {k : ℕ} {C : List (Set (Pt d) × ℕ)} (hC : CopyOK X E K k C) {n : ℕ}
    (hn : 1 ≤ n) : CopyOK X E K k (C.take n) := by
  obtain ⟨hh, hm, hc⟩ := hC
  refine ⟨?_, fun c hc' => hm c (List.mem_of_mem_take hc'), ?_⟩
  · cases C with
    | nil => simp at hh
    | cons x l =>
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
      simpa using hh
  · intro i hi
    simp only [List.length_take] at hi
    have := hc i (by omega)
    rw [List.take_take, show min (i + 1) n = i + 1 by omega]
    simp only [List.getElem_take]
    exact this

theorem copyOK_snoc {X : Set (Set (Pt d))} {E : Set (Pt d) × ℕ → List (Pt d) → List (Pt d)}
    {K : Set (Pt d)} {k : ℕ} {C : List (Set (Pt d) × ℕ)} (hC : CopyOK X E K k C) (hne : C ≠ [])
    {c : Set (Pt d) × ℕ} (hcX : c.1 ∈ X) (hc1 : 1 ≤ c.2)
    (hcomp : CompatibleCopy {x | x ∈ preOf E C} (C.getLast hne).1 (C.getLast hne).2 c.1 c.2) :
    CopyOK X E K k (C ++ [c]) := by
  obtain ⟨hh, hm, hcc⟩ := hC
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, l, rfl⟩ := List.exists_cons_of_ne_nil hne
    simpa using hh
  · intro c' hc'
    rcases List.mem_append.1 hc' with h | h
    · exact hm c' h
    · rw [List.mem_singleton.1 h]; exact ⟨hcX, hc1⟩
  · intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    rcases Nat.lt_or_ge (i + 1) C.length with h | h
    · rw [List.take_append_of_le_length (by omega)]
      simp only [List.getElem_append_left h, List.getElem_append_left (show i < C.length by omega)]
      exact hcc i h
    · have hi' : i + 1 = C.length := by omega
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
      rw [List.getElem_append_left (show i < C.length by omega), List.getElem_append_right (by omega)]
      have hl : C.getLast hne = C[i] := by rw [List.getLast_eq_getElem]; congr 1; omega
      rw [← hl]
      simpa [hi'] using hcomp

/-- **Theorem 8.2, necessity** (for the monotone relation): a generator achieving `α` gives a
protected tree on copies rooted at every copy `(K,k)`. -/
theorem copy_tree_of_gen {X : Set (Set (Pt d))} (hX : LangClass X)
    {g : ℝ → ℝ} (hg1 : ∀ x, 1 ≤ x → 1 ≤ g x)
    (α : Set (Pt d) → ℝ) (G : Generator (Pt d)) (hG : G ∈ ValidGen X)
    (hGK : ∀ K ∈ X, Guarantees (dH (hLog g)) G K (α K)) {K : Set (Pt d)} (hK : K ∈ X)
    (k : ℕ) (hk : 1 ≤ k) : ∃ T, IsCopyProtectedTree X (hLog g) α K k T := by
  have hcomm : ∀ c : Set (Pt d) × ℕ, c.1 ∈ X → 1 ≤ c.2 → ∀ xs : List (Pt d),
      (∀ x ∈ xs, x ∈ c.1) →
      ∃ ext : List (Pt d), ∃ s : ℝ, 1 ≤ s ∧ (∀ x ∈ ext, x ∈ c.1) ∧
        ∀ cont : List (Pt d), (∀ x ∈ cont, x ∈ c.1) →
          (∀ j < cont.length, G ((xs ++ ext ++ cont).take ((xs ++ ext).length + j + 1)) ∈ c.1) ∧
          ∀ R : Rect d, s * (hLog g) R.vol ≤ mass c.1 R →
            (c.1 ∩ R.pts ⊆ {x | x ∈ xs ++ ext ++ cont} ∪ outsOf G (xs ++ ext ++ cont)) →
            copyQuota α c.1 c.2 * (mass c.1 R : ℝ) ≤
              ((outsOf G (xs ++ ext ++ cont) ∩ c.1 ∩ R.pts).ncard : ℝ) :=
    fun c hc hc1 xs hxs => hd_commitments hX hg1 G hG hc (hGK c.1 hc)
      ((copyQuota_cases α c.1 c.2 hc1).imp_right And.right) xs hxs
  choose extF sF hsF hextF hcomF using hcomm
  let Cond : Set (Pt d) × ℕ → List (Pt d) → Prop := fun c xs =>
    c.1 ∈ X ∧ 1 ≤ c.2 ∧ ∀ x ∈ xs, x ∈ c.1
  let E : Set (Pt d) × ℕ → List (Pt d) → List (Pt d) := fun c xs =>
    if h : Cond c xs then extF c h.1 h.2.1 xs h.2.2 else []
  let cutF : Set (Pt d) × ℕ → List (Pt d) → ℝ := fun c xs =>
    if h : Cond c xs then sF c h.1 h.2.1 xs h.2.2 else 1
  have hE : ∀ c xs (h : Cond c xs), E c xs = extF c h.1 h.2.1 xs h.2.2 := fun c xs h => dif_pos h
  have hcut : ∀ c xs (h : Cond c xs), cutF c xs = sF c h.1 h.2.1 xs h.2.2 :=
    fun c xs h => dif_pos h
  have hEsub : ∀ c xs, ∀ x ∈ E c xs, x ∈ c.1 := by
    intro c xs x hx
    simp only [E] at hx
    split_ifs at hx with h
    · exact hextF _ _ _ _ _ x hx
    · simp at hx
  have hcut1 : ∀ c xs, 1 ≤ cutF c xs := by
    intro c xs
    simp only [cutF]
    split_ifs with h
    · exact hsF _ _ _ _ _
    · exact le_rfl
  let dflt : Set (Pt d) × ℕ := (∅, 0)
  let pre : List (Set (Pt d) × ℕ) → List (Pt d) := preOf E
  let s : List (Set (Pt d) × ℕ) → ℝ := fun C => cutF (C.getLastD dflt) (pre C.dropLast)
  let a : List (Set (Pt d) × ℕ) → ℝ := sumPref (fun l => bnd G (pre l))
  let deco : List (Set (Pt d) × ℕ) → Deco d := fun C =>
    .mk (C.getLastD dflt).1 (C.getLastD dflt).2 (pre C).toFinset (s C) (a C)
  have hvert : ∀ C, CopyOK X E K k C → ∀ j (hj : j < C.length),
      Cond C[j] (pre (C.take j)) := by
    intro C hC j hj
    refine ⟨(hC.2.1 _ (List.getElem_mem _)).1, (hC.2.1 _ (List.getElem_mem _)).2, ?_⟩
    rcases j with _ | j
    · simp [pre, preOf]
    · exact (hC.2.2 j hj).2.1
  have hanti : ∀ C, CopyOK X E K k C → ∀ i j (hi : i < C.length) (hj : j < C.length), i ≤ j →
      C[j].1 ⊆ C[i].1 := by
    intro C hC i j hi hj hij
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hij
    induction m with
    | zero => exact le_rfl
    | succ m ih => exact (hC.2.2 (i + m) (by omega)).2.2.1.trans (ih (by omega) (by omega))
  have hpre_last : ∀ C, CopyOK X E K k C → C ≠ [] → ∀ x ∈ pre C, x ∈ (C.getLastD dflt).1 := by
    intro C hC hne x hx
    have hlen := List.length_pos_iff.mpr hne
    have e : C = C.take (C.length - 1) ++ [C[C.length - 1]] := by
      rw [List.take_concat_get' C _ (by omega), List.take_of_length_le (by omega)]
    have hv := hvert C hC (C.length - 1) (by omega)
    rw [getLastD_eq_getLast _ _ hne, List.getLast_eq_getElem]
    have hx' : x ∈ pre (C.take (C.length - 1) ++ [C[C.length - 1]]) := by rw [← e]; exact hx
    simp only [pre] at hx'
    rw [preOf_snoc] at hx'
    rcases List.mem_append.1 hx' with hx' | hx'
    · exact hv.2.2 x hx'
    · exact hEsub _ _ x hx'
  have hrest : ∀ C, CopyOK X E K k C → ∀ j (hj : j < C.length),
      ∃ rest, pre C = pre (C.take (j + 1)) ++ rest ∧ ∀ x ∈ rest, x ∈ C[j].1 := by
    intro C hC j hj
    have key : ∀ m, j + 1 + m ≤ C.length → ∃ rest, pre (C.take (j + 1 + m)) =
        pre (C.take (j + 1)) ++ rest ∧ ∀ x ∈ rest, x ∈ C[j].1 := by
      intro m
      induction m with
      | zero => intro _; exact ⟨[], by simp, by simp⟩
      | succ m ih =>
        intro hm
        obtain ⟨rest, hr, hrL⟩ := ih (by omega)
        refine ⟨rest ++ E C[j + 1 + m] (pre (C.take (j + 1 + m))), ?_, ?_⟩
        · rw [show j + 1 + (m + 1) = j + 1 + m + 1 by omega, ← List.take_concat_get' C _ (by omega)]
          simp only [pre] at hr ⊢
          rw [preOf_snoc, hr, List.append_assoc]
        · intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact hrL x hx
          · exact hanti C hC j (j + 1 + m) hj (by omega) (by omega) (hEsub _ _ x hx)
    obtain ⟨rest, hr, hrL⟩ := key (C.length - (j + 1)) (by omega)
    rw [show j + 1 + (C.length - (j + 1)) = C.length by omega,
      List.take_of_length_le le_rfl] at hr
    exact ⟨rest, hr, hrL⟩
  have hpj : ∀ C, CopyOK X E K k C → ∀ j (hj : j < C.length),
      ∃ hv : Cond C[j] (pre (C.take j)),
        pre (C.take (j + 1)) = pre (C.take j) ++ extF C[j] hv.1 hv.2.1 (pre (C.take j)) hv.2.2 ∧
        s (C.take (j + 1)) = sF C[j] hv.1 hv.2.1 (pre (C.take j)) hv.2.2 := by
    intro C hC j hj
    have hv := hvert C hC j hj
    refine ⟨hv, ?_, ?_⟩
    · rw [← List.take_concat_get' C j hj]
      simp only [pre]
      rw [preOf_snoc, hE _ _ hv]
    · show cutF ((C.take (j + 1)).getLastD dflt) (pre (C.take (j + 1)).dropLast) = _
      rw [getLastD_take C dflt j hj, ← List.take_concat_get' C j hj, List.dropLast_concat]
      exact hcut _ _ hv
  have hdeco_L : ∀ C : List (Set (Pt d) × ℕ), ∀ j (hj : j < C.length),
      (deco (C.take (j + 1))).L = C[j].1 := by
    intro C j hj
    show ((C.take (j + 1)).getLastD dflt).1 = _
    rw [getLastD_take C dflt j hj]
  have hdeco_k : ∀ C : List (Set (Pt d) × ℕ), ∀ j (hj : j < C.length),
      (deco (C.take (j + 1))).k = C[j].2 := by
    intro C j hj
    show ((C.take (j + 1)).getLastD dflt).2 = _
    rw [getLastD_take C dflt j hj]
  have hdeco_P : ∀ C : List (Set (Pt d) × ℕ), (↑(deco C).P : Set (Pt d)) = {x | x ∈ pre C} := by
    intro C
    show (↑(pre C).toFinset : Set (Pt d)) = _
    ext x; simp
  have hdeco_s : ∀ C : List (Set (Pt d) × ℕ), (deco C).s = s C := fun _ => rfl
  have hdeco_a : ∀ C : List (Set (Pt d) × ℕ), (deco C).a = a C := fun _ => rfl
  have ha_snoc : ∀ C c, a C < a (C ++ [c]) := by
    intro C c
    simp only [a]
    rw [sumPref_snoc]
    linarith [bnd_nonneg G (pre (C ++ [c]))]
  have hroot : CopyOK X E K k [(K, k)] :=
    ⟨rfl, by simp [hK, hk], fun i hi => by simp at hi⟩
  let paths : Set (List (Deco d)) := {p | ∃ C, CopyOK X E K k C ∧ p = pathG deco C}
  have hrootp : [deco [(K, k)]] ∈ paths := ⟨[(K, k)], hroot, by simp [pathG]⟩
  have hhead : ∀ p ∈ paths, p.head? = some (deco [(K, k)]) := by
    rintro p ⟨C, hC, rfl⟩
    obtain ⟨c, l, rfl⟩ : ∃ c l, C = c :: l := by
      cases C with
      | nil => simp [CopyOK] at hC
      | cons c l => exact ⟨c, l, rfl⟩
    have hc : c = (K, k) := by simpa using hC.1
    subst hc
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by simp [pathG_length]),
      pathG_getElem]
    simp
  have hpre : ∀ p ∈ paths, ∀ n, 1 ≤ n → p.take n ∈ paths := by
    rintro p ⟨C, hC, rfl⟩ n hn
    exact ⟨C.take n, copyOK_take hC hn, pathG_take deco C n⟩
  have hcount : paths.Countable := by
    have hXc := hX.countable.to_subtype
    have hL : {C : List (Set (Pt d) × ℕ) | ∀ c ∈ C, c.1 ∈ X}.Countable := by
      refine (Set.countable_range (fun l : List (X × ℕ) => l.map fun c => (c.1.1, c.2))).mono ?_
      intro C hC
      refine ⟨C.attach.map fun c => (⟨c.1.1, hC c.1 c.2⟩, c.1.2), ?_⟩
      apply List.ext_getElem <;> simp
    refine (hL.image (pathG deco)).mono ?_
    rintro p ⟨C, hC, rfl⟩
    exact ⟨C, fun c hc => (hC.2.1 c hc).1, rfl⟩
  have hget : ∀ (C : List (Set (Pt d) × ℕ)) (hp : pathG deco C ≠ [])
      (i : Fin ((pathG deco C).length - 1 + 1)),
      (pathG deco C).get ⟨i.val, by have := List.length_pos_iff.mpr hp; omega⟩ =
        deco (C.take (i.val + 1)) := by
    intro C hp i
    rw [List.get_eq_getElem, pathG_getElem]
  refine ⟨DTree.mk paths (deco [(K, k)]) hrootp hhead hpre hcount, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · -- vertex data
    rintro p ⟨C, hC, rfl⟩ v hv
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    rw [pathG_getElem]
    rw [pathG_length] at hi
    have hC' := copyOK_take hC (n := i + 1) (by omega)
    have hm := hC.2.1 _ (List.getElem_mem hi)
    refine ⟨by rw [hdeco_L C i hi]; exact hm.1, ?_, hcut1 _ _,
      (le_sumPref (fun l => bnd_nonneg G (pre l)) _).2, by rw [hdeco_k C i hi]; exact hm.2⟩
    rw [hdeco_P]
    intro x hx
    have := hpre_last _ hC' (List.ne_nil_of_length_pos (by simp; omega)) x hx
    rw [hdeco_L C i hi]
    rwa [getLastD_take C dflt i hi] at this
  · -- edges
    rintro p v w ⟨C, hC, hp⟩
    have hlen : C.length = p.length + 2 := by
      have := congrArg List.length hp
      simp only [pathG_length, List.length_append, List.length_cons, List.length_nil] at this
      omega
    have hv : v = (pathG deco C)[p.length]'(by rw [pathG_length]; omega) := by simp [← hp]
    have hw : w = (pathG deco C)[p.length + 1]'(by rw [pathG_length]; omega) := by simp [← hp]
    rw [pathG_getElem] at hv hw
    subst hv hw
    rw [hdeco_P, hdeco_L C _ (by omega), hdeco_L C _ (by omega), hdeco_k C _ (by omega),
      hdeco_k C _ (by omega), hdeco_a, hdeco_a]
    refine ⟨hC.2.2 p.length (by omega), ?_⟩
    rw [← List.take_concat_get' C (p.length + 1) (by omega)]
    exact ha_snoc _ _
  · -- children
    rintro p ⟨C, hC, rfl⟩ hp M hM n hcomp
    rw [pathG_getLast] at hcomp
    have hCne : C ≠ [] := by intro h; subst h; simp [pathG] at hp
    refine ⟨deco (C ++ [(M, n)]), ?_, ?_, C ++ [(M, n)], ?_, (pathG_snoc deco C _).symm⟩
    · show ((C ++ [(M, n)]).getLastD dflt).1 = M; simp
    · show ((C ++ [(M, n)]).getLastD dflt).2 = n; simp
    · refine copyOK_snoc hC hCne hM hcomp.1 ?_
      have e : C.getLastD dflt = C.getLast hCne := getLastD_eq_getLast _ _ hCne
      rw [hdeco_P] at hcomp
      have h1 : (deco C).L = (C.getLast hCne).1 := by show (C.getLastD dflt).1 = _; rw [e]
      have h2 : (deco C).k = (C.getLast hCne).2 := by show (C.getLastD dflt).2 = _; rw [e]
      rw [h1, h2] at hcomp
      exact hcomp
  · -- feasibility
    rintro p ⟨C, hC, rfl⟩ hp
    have hlenC : (pathG deco C).length = C.length := pathG_length deco C
    have hCne : C ≠ [] := by intro h; subst h; simp [pathG] at hp
    rw [pathG_getLast]
    have hb : ∀ i : Fin ((pathG deco C).length - 1 + 1), i.val < C.length := fun i => by
      have := i.isLt; have := List.length_pos_iff.mpr hCne; omega
    refine feasible_of_commit (pathFn Deco.L (pathG deco C) hp)
      (fun i => copyQuota α (pathFn Deco.L (pathG deco C) hp i) (pathFn Deco.k (pathG deco C) hp i))
      G (pre C) (pathFn Deco.s (pathG deco C) hp) (a C) ?_ hG.1
      (fun j => pre (C.take (j.val + 1))) ?_ ?_ ?_ ?_
    · intro i j hij
      simp only [pathFn, List.get_eq_getElem, pathG_getElem]
      rw [hdeco_L C _ (hb j), hdeco_L C _ (hb i)]
      exact hanti C hC i.val j.val (hb i) (hb j) hij
    · intro j
      simp only [pathFn, List.get_eq_getElem, pathG_getElem]
      rw [hdeco_L C _ (hb j)]
      exact hrest C hC j.val (hb j)
    · intro j cont hcont kk hkk
      simp only [pathFn, List.get_eq_getElem, pathG_getElem] at hcont ⊢
      rw [hdeco_L C _ (hb j)] at hcont ⊢
      obtain ⟨hv, hpj', -⟩ := hpj C hC j.val (hb j)
      rw [hpj']
      exact (hcomF _ hv.1 hv.2.1 _ hv.2.2 cont hcont).1 kk hkk
    · intro j cont hcont R hR hocc
      simp only [pathFn, List.get_eq_getElem, pathG_getElem] at hcont hR hocc ⊢
      rw [hdeco_L C _ (hb j)] at hcont hR hocc ⊢
      rw [hdeco_k C _ (hb j)]
      obtain ⟨hv, hpj', hs⟩ := hpj C hC j.val (hb j)
      rw [hdeco_s, hs] at hR
      rw [hpj'] at hocc ⊢
      exact (hcomF _ hv.1 hv.2.1 _ hv.2.2 cont hcont).2 R hR hocc
    · intro x hx
      exact mem_core_of_used hx (le_sumPref (fun l => bnd_nonneg G (pre l)) C).1

end CopyNec

end CharAux


end BanachDensityHD
