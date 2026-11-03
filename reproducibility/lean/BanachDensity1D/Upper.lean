import BanachDensity1D.HistoryTopology

/-!
# The adversarial upper bound (Theorem 5.1), proof development

The adversary is built from finite input histories `h : List ℤ` (the inputs of the rounds
`0, …, |h| - 1`); the output of round `t` on `h` is `G (h.take (t + 1))` (`outL`).
The paper-named statement `thm_upper` is at the end of this file.
-/

namespace BanachDensity1D

open Set Filter Classical

namespace UpperAux

open ChainsAux (layerSum score_eq)

/-! ## Finite histories -/

/-- The output of round `t` on the finite input history `h`. -/
def outL (G : Generator) (h : List ℤ) (t : ℕ) : ℤ := G (h.take (t + 1))

/-- The outputs of the rounds `t < |h|`. -/
def outs (G : Generator) (h : List ℤ) : Set ℤ := {x | ∃ t < h.length, outL G h t = x}

/-- The inputs of `h`. -/
def ins (h : List ℤ) : Set ℤ := {x | x ∈ h}

/-- The points used (input or output) in the rounds `t < |h|`. -/
def used (G : Generator) (h : List ℤ) : Set ℤ := ins h ∪ outs G h

/-- The extension `h'` of `h` is *good* for `L`: every output of a round `|h| ≤ t < |h'|` lies
in `L`. -/
def Good (G : Generator) (L : Set ℤ) (h h' : List ℤ) : Prop :=
  ∀ t, h.length ≤ t → t < h'.length → outL G h' t ∈ L

/-- Outputs on a limit agree with outputs on its prefixes. -/
theorem out_eq_outL {G : Generator} {w : ℕ → ℤ} {h : List ℤ}
    (hw : ∀ i (hi : i < h.length), w i = h[i]) {t : ℕ} (ht : t < h.length) :
    G.out w t = outL G h t := by
  unfold Generator.out outL
  rw [BasicAux.inputsUpTo_eq hw ht]


/-- Availability on finite histories, from admissibility. -/
theorem avail_list {G : Generator} (hGa : G.Admissible) (h : List ℤ) {t : ℕ}
    (ht : t < h.length) :
    (∀ i (hi : i ≤ t), h[i]'(by omega) ≠ outL G h t) ∧ ∀ s < t, outL G h s ≠ outL G h t := by
  let w : ℕ → ℤ := fun i => h.getD i 0
  have hw : ∀ i (hi : i < h.length), w i = h[i] := fun i hi => List.getD_eq_getElem _ _ hi
  obtain ⟨h1, h2⟩ := hGa w t
  rw [out_eq_outL hw ht] at h1 h2
  refine ⟨fun i hi => ?_, fun s hs => ?_⟩
  · rw [← hw i (by omega)]; exact h1 i hi
  · rw [← out_eq_outL hw (by omega)]; exact h2 s hs

theorem outL_append (G : Generator) (h r : List ℤ) {t : ℕ} (ht : t < h.length) :
    outL G (h ++ r) t = outL G h t := by
  unfold outL
  rw [List.take_append_of_le_length (by omega)]

theorem outs_mono (G : Generator) (h r : List ℤ) : outs G h ⊆ outs G (h ++ r) := by
  rintro x ⟨t, ht, rfl⟩
  exact ⟨t, by simp only [List.length_append]; omega, outL_append G h r ht⟩

theorem used_mono (G : Generator) (h r : List ℤ) : used G h ⊆ used G (h ++ r) :=
  union_subset_union (fun _ hx => List.mem_append_left r hx) (outs_mono G h r)

theorem used_finite (G : Generator) (h : List ℤ) : (used G h).Finite := by
  refine (List.finite_toSet h).union (((Set.finite_lt_nat h.length).image (outL G h)).subset ?_)
  rintro x ⟨t, ht, rfl⟩
  exact ⟨t, ht, rfl⟩

/-- An output of a later round is not a point used earlier. -/
theorem outL_not_used {G : Generator} (hGa : G.Admissible) (h r : List ℤ) {t : ℕ}
    (ht : h.length ≤ t) (ht' : t < (h ++ r).length) : outL G (h ++ r) t ∉ used G h := by
  obtain ⟨h1, h2⟩ := avail_list hGa (h ++ r) ht'
  rintro (hx | ⟨s, hs, hsx⟩)
  · obtain ⟨i, hi, hix⟩ := List.getElem_of_mem (show outL G (h ++ r) t ∈ h from hx)
    apply h1 i (by omega)
    rw [List.getElem_append_left hi, hix]
  · apply h2 s (by omega)
    rw [outL_append G h r hs, hsx]

/-- An output of a later round is not a point used earlier (prefix version). -/
theorem outs_used_sub {G : Generator} (hGa : G.Admissible) (h r : List ℤ) {x : ℤ}
    (hx : x ∈ outs G (h ++ r)) (hxu : x ∈ used G h) : x ∈ outs G h := by
  obtain ⟨t, ht, rfl⟩ := hx
  by_cases hth : t < h.length
  · exact ⟨t, hth, (outL_append G h r hth).symm⟩
  · exact absurd hxu (outL_not_used hGa h r (by omega) ht)

/-! ## The race (Lemma 5.2) -/

/-- **The race** (Lemma 5.2). Starting from a history in which no point of the finite set `A`
was used, the adversary inputs unused points of `A` while there are any; at the end every point
of `A` is used and the generator has output at most `⌊|A|/2⌋` points of `A`. -/
theorem race {G : Generator} (hGa : G.Admissible) {A : Set ℤ} (hA : A.Finite) (h : List ℤ)
    (hd : Disjoint (used G h) A) :
    ∃ r : List ℤ, (∀ x ∈ r, x ∈ A) ∧ A ⊆ used G (h ++ r) ∧
      2 * (outs G (h ++ r) ∩ A).ncard ≤ A.ncard := by
  have hfinI : ∀ h : List ℤ, (ins h ∩ A).Finite := fun _ => hA.subset inter_subset_right
  have hfinO : ∀ h : List ℤ, (outs G h ∩ A).Finite := fun _ => hA.subset inter_subset_right
  suffices H : ∀ m, ∀ h : List ℤ, (A \ used G h).ncard = m →
      Disjoint (ins h ∩ A) (outs G h ∩ A) → (outs G h ∩ A).ncard ≤ (ins h ∩ A).ncard →
      ∃ r : List ℤ, (∀ x ∈ r, x ∈ A) ∧ A ⊆ used G (h ++ r) ∧
        2 * (outs G (h ++ r) ∩ A).ncard ≤ A.ncard by
    have hO : outs G h ∩ A = ∅ :=
      eq_empty_of_forall_notMem fun x hx => disjoint_left.1 hd (Or.inr hx.1) hx.2
    refine H _ h rfl ?_ ?_
    · rw [hO]; exact disjoint_empty _
    · rw [hO]; simp
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro h hm hdisj hle
  by_cases hfull : A ⊆ used G h
  · refine ⟨[], by simp, by simpa using hfull, ?_⟩
    simp only [List.append_nil]
    have hu : (ins h ∩ A) ∪ (outs G h ∩ A) ⊆ A :=
      union_subset inter_subset_right inter_subset_right
    have h1 := ncard_union_eq hdisj (hfinI h) (hfinO h)
    have h2 := ncard_le_ncard hu hA
    omega
  · obtain ⟨x, hxA, hxu⟩ := not_subset.1 hfull
    set h' := h ++ [x] with hh'
    set y := outL G h' h.length with hy
    have hy1 : y ∉ used G h := outL_not_used hGa h [x] le_rfl (by simp)
    have hy2 : y ≠ x := by
      have := (avail_list hGa h' (t := h.length) (by simp [hh'])).1 h.length le_rfl
      simpa [hh'] using this.symm
    have hins : ins h' ∩ A = insert x (ins h ∩ A) := by
      ext z
      simp only [ins, hh', mem_inter_iff, mem_ofPred_eq, List.mem_append, List.mem_singleton,
        mem_insert_iff]
      constructor
      · rintro ⟨hz | rfl, hzA⟩
        · exact Or.inr ⟨hz, hzA⟩
        · exact Or.inl rfl
      · rintro (rfl | ⟨hz, hzA⟩)
        · exact ⟨Or.inr rfl, hxA⟩
        · exact ⟨Or.inl hz, hzA⟩
    have houts : outs G h' ⊆ insert y (outs G h) := by
      rintro z ⟨t, ht, rfl⟩
      simp only [hh', List.length_append, List.length_singleton] at ht
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
      · exact Or.inr ⟨t, ht, (outL_append G h [x] ht).symm⟩
      · exact Or.inl rfl
    have hxI : x ∉ ins h ∩ A := fun hx => hxu (Or.inl hx.1)
    have hcardI : (ins h' ∩ A).ncard = (ins h ∩ A).ncard + 1 := by
      rw [hins, ncard_insert_of_notMem hxI (hfinI h)]
    have hcardO : (outs G h' ∩ A).ncard ≤ (outs G h ∩ A).ncard + 1 := by
      calc (outs G h' ∩ A).ncard ≤ (insert y (outs G h ∩ A)).ncard := by
            refine ncard_le_ncard ?_ ((hfinO h).insert y)
            rintro z ⟨hz, hzA⟩
            rcases houts hz with rfl | hz
            · exact mem_insert _ _
            · exact Or.inr ⟨hz, hzA⟩
        _ ≤ _ := ncard_insert_le _ _
    have hdisj' : Disjoint (ins h' ∩ A) (outs G h' ∩ A) := by
      rw [disjoint_left]
      rintro z hzI ⟨hzO, hzA⟩
      rw [hins] at hzI
      rcases houts hzO with rfl | hzO'
      · rcases hzI with h1 | h1
        · exact hy2 h1
        · exact hy1 (Or.inl h1.1)
      · rcases hzI with rfl | h1
        · exact hxu (Or.inr hzO')
        · exact disjoint_left.1 hdisj h1 ⟨hzO', hzA⟩
    have hlt : (A \ used G h').ncard < m := by
      rw [← hm]
      refine ncard_lt_ncard ?_ (hA.sdiff)
      refine (ssubset_iff_of_subset (sdiff_subset_sdiff_right (used_mono G h [x]))).2
        ⟨x, ⟨hxA, hxu⟩, fun hx => hx.2 (Or.inl (show x ∈ h ++ [x] by simp))⟩
    obtain ⟨r, hr, hAu, hcount⟩ := ihm _ hlt h' rfl hdisj' (by omega)
    refine ⟨x :: r, ?_, ?_, ?_⟩
    · intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hxA
      · exact hr z hz
    · simpa [hh'] using hAu
    · simpa [hh'] using hcount

/-! ## Limits of increasing histories -/

/-- An increasing sequence of histories with unbounded lengths has a limit sequence. -/
theorem limit_exists (hs : ℕ → List ℤ) (hmono : ∀ k, ∃ r, hs (k + 1) = hs k ++ r)
    (hlen : ∀ k, k ≤ (hs k).length) :
    ∃ w : ℕ → ℤ, (∀ k i (hi : i < (hs k).length), w i = (hs k)[i]) ∧
      ∀ x, x ∈ range w ↔ ∃ k, x ∈ hs k := by
  have hpre : ∀ k m, k ≤ m → ∃ r, hs m = hs k ++ r := by
    intro k m hkm
    induction hkm with
    | refl => exact ⟨[], by simp⟩
    | step _ ih =>
      obtain ⟨r, hr⟩ := ih
      obtain ⟨r', hr'⟩ := hmono _
      exact ⟨r ++ r', by rw [hr', hr, List.append_assoc]⟩
  have hget : ∀ k m i (hi : i < (hs k).length) (hi' : i < (hs m).length), k ≤ m →
      (hs m)[i] = (hs k)[i] := by
    intro k m i hi hi' hkm
    obtain ⟨r, hr⟩ := hpre k m hkm
    have : (hs m)[i]? = (hs k)[i]? := by rw [hr, List.getElem?_append_left hi]
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi'] at this
    exact Option.some.inj this
  have hlen' : ∀ i, i < (hs (i + 1)).length := fun i => by have := hlen (i + 1); omega
  refine ⟨fun i => (hs (i + 1))[i]'(hlen' i), fun k i hi => ?_, fun x => ⟨?_, ?_⟩⟩
  · rcases le_total k (i + 1) with h | h
    · exact hget k (i + 1) i hi (hlen' i) h
    · exact (hget (i + 1) k i (hlen' i) hi h).symm
  · rintro ⟨i, rfl⟩
    exact ⟨i + 1, List.getElem_mem _⟩
  · rintro ⟨k, hk⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hk
    refine ⟨i, ?_⟩
    rcases le_total k (i + 1) with h | h
    · exact hget k (i + 1) i hi (hlen' i) h
    · exact (hget (i + 1) k i (hlen' i) hi h).symm

/-- Sealing: once a point is used, a later round cannot output it. -/
theorem sealed {G : Generator} (hGa : G.Admissible) {w : ℕ → ℤ} {h : List ℤ}
    (hw : ∀ i (hi : i < h.length), w i = h[i]) {x : ℤ} (hx : x ∈ G.outputSet w)
    (hxu : x ∈ used G h) : x ∈ outs G h := by
  obtain ⟨t, rfl⟩ := hx
  by_cases ht : t < h.length
  · exact ⟨t, ht, (out_eq_outL hw ht).symm⟩
  · exfalso
    obtain ⟨h1, h2⟩ := hGa w t
    rcases hxu with hx | ⟨s, hs, hsx⟩
    · obtain ⟨i, hi, hix⟩ := List.getElem_of_mem (show G.out w t ∈ h from hx)
      apply h1 i (by omega)
      rw [hw i hi, hix]
    · apply h2 s (by omega)
      rw [out_eq_outL hw hs, hsx]

/-! ## Bad attempts cannot repeat forever -/

/-- Attempts at a language `L ∈ X`. Let `Q h h'` be a property that is inherited by shorter
prefixes `h` (`hQ`: `Q (h ++ r) h'` implies `Q h h'`), and suppose that from any history `h` an
attempt starting by inputting `e k` (`e` an enumeration of `L`) and then adding only points `r` of
`L` yields `Q h (h ++ e k :: r)` whenever `h ⊆ L` and the attempt is good. Then from any start
`h₀ ⊆ L` there is a continuation `r ⊆ L` with `Q h₀ (h₀ ++ r)`. (Proof: run attempts one after
another from `h₀`; some attempt is good, because otherwise the inputs form a full enumeration of
`L` on which `G` outputs outside `L` infinitely often; then `hQ` carries its `Q` back to `h₀`.) -/
theorem attempts {X : Set (Set ℤ)} {G : Generator} (hG : G.EventuallyValidOn X) {L : Set ℤ}
    (hL : L ∈ X) (e : ℕ → ℤ) (he : range e = L) (Q : List ℤ → List ℤ → Prop)
    (hQ : ∀ h r h', Q (h ++ r) h' → Q h h')
    (hatt : ∀ k h, ∃ r, (∀ x ∈ r, x ∈ L) ∧
      ((∀ x ∈ h, x ∈ L) → Good G L h (h ++ e k :: r) → Q h (h ++ e k :: r)))
    (h₀ : List ℤ) (h₀L : ∀ x ∈ h₀, x ∈ L) :
    ∃ r, (∀ x ∈ r, x ∈ L) ∧ Q h₀ (h₀ ++ r) := by
  choose r hrL hrQ using hatt
  let hs : ℕ → List ℤ := fun k => Nat.rec h₀ (fun k h => h ++ e k :: r k h) k
  have hs_succ : ∀ k, hs (k + 1) = hs k ++ e k :: r k (hs k) := fun k => rfl
  have heL : ∀ k, e k ∈ L := fun k => by rw [← he]; exact mem_range_self k
  have hsdec : ∀ k, ∃ r', (∀ y ∈ r', y ∈ L) ∧ hs k = h₀ ++ r' := by
    intro k
    induction k with
    | zero => exact ⟨[], by simp, by simp [hs]⟩
    | succ k ih =>
      obtain ⟨r', hr'L, hr'⟩ := ih
      refine ⟨r' ++ e k :: r k (hs k), ?_, by rw [hs_succ, hr', List.append_assoc]⟩
      intro y hy
      simp only [List.mem_append, List.mem_cons] at hy
      rcases hy with hy | rfl | hy
      · exact hr'L y hy
      · exact heL k
      · exact hrL k _ y hy
  have hsL : ∀ k, ∀ y ∈ hs k, y ∈ L := by
    intro k y hy
    obtain ⟨r', hr'L, hr'⟩ := hsdec k
    rw [hr'] at hy
    rcases List.mem_append.1 hy with hy | hy
    · exact h₀L y hy
    · exact hr'L y hy
  by_cases hgood : ∃ k, Good G L (hs k) (hs (k + 1))
  · obtain ⟨k, hk⟩ := hgood
    have hQk := hrQ k (hs k) (hsL k) hk
    obtain ⟨r', hr'L, hr'⟩ := hsdec (k + 1)
    refine ⟨r', hr'L, ?_⟩
    rw [← hr']
    obtain ⟨r'', -, hr''⟩ := hsdec k
    rw [hs_succ]
    rw [hr''] at hQk ⊢
    exact hQ h₀ r'' _ hQk
  · exfalso
    have hlen : ∀ k, k ≤ (hs k).length := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [hs_succ]; simp only [List.length_append, List.length_cons]; omega
    obtain ⟨w, hw, hrange⟩ := limit_exists hs (fun k => ⟨_, hs_succ k⟩) hlen
    have hfull : IsFullEnumeration w L := by
      ext y
      rw [hrange]
      constructor
      · rintro ⟨k, hk⟩; exact hsL k y hk
      · intro hy
        rw [← he] at hy
        obtain ⟨k, rfl⟩ := hy
        exact ⟨k + 1, by rw [hs_succ]; simp⟩
    obtain ⟨t₀, ht₀⟩ := hG L hL w hfull
    have hk := hgood ⟨t₀, ?_⟩
    · exact hk
    intro t h1 h2
    have := (ht₀ t (by have := hlen t₀; omega)).1
    rwa [out_eq_outL (hw (t₀ + 1)) h2] at this

/-! ## The mega step -/

/-- The postcondition of a call of the mega step at the subtree `T`, with path prefix `Hpre`
(the languages above `T`), from the history `h` to the history `h'`. -/
def Post (G : Generator) (K : Set ℤ) (n : ℕ) (ε : ℝ) (T : LTree) (Hpre : List (Set ℤ))
    (h h' : List ℤ) : Prop :=
  ∃ P ∈ T.paths, ∃ a b : ℤ, n ≤ (K ∩ Icc a b).ncard ∧
    def_raw_pairing_score (Hpre ++ P) (K ∩ Icc a b) ≤ cn (Hpre ++ P) n + ε ∧
    Disjoint (used G h) (K ∩ Icc a b) ∧
    K ∩ Icc a b ∩ T.label ⊆ used G h' ∧
    used G h' ∩ (K ∩ Icc a b) ⊆ T.label ∧
    ((outs G h' ∩ (K ∩ Icc a b)).ncard : ℝ) ≤ (layerSum P (K ∩ Icc a b) : ℝ)

theorem Post_mono {G : Generator} {K : Set ℤ} {n : ℕ} {ε : ℝ} {T : LTree}
    {Hpre : List (Set ℤ)} (h r h' : List ℤ) (hp : Post G K n ε T Hpre (h ++ r) h') :
    Post G K n ε T Hpre h h' := by
  obtain ⟨P, hP, a, b, h1, h2, h3, h4⟩ := hp
  exact ⟨P, hP, a, b, h1, h2, h3.mono_left (used_mono G h r), h4⟩

/-- The candidate interval at a leaf: a far relative interval of `K` with score close to `c_n`. -/
theorem choose_J {K : Set ℤ} (hK : K.Infinite) {H : List (Set ℤ)} (hne : H ≠ [])
    (hc : H.IsChain (fun L M => M ⊂ L)) (hs : start H = K) (n R : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ a b : ℤ, n ≤ (K ∩ Icc a b).ncard ∧ Disjoint (K ∩ Icc a b) (Icc (-(R : ℤ)) R) ∧
      def_raw_pairing_score H (K ∩ Icc a b) ≤ cn H n + ε := by
  have hA : (start H).Infinite := hs ▸ hK
  obtain ⟨hT, -, -, -⟩ := ChainsAux.cn_tendsto hne hc hA n
  have hle : ChainsAux.cnSeq H n R ≤ cn H n := (ChainsAux.cnSeq_mono hA n).ge_of_tendsto hT R
  have : Nonempty (farIntervals H n R) := (ChainsAux.farIntervals_nonempty hA n R).to_subtype
  obtain ⟨⟨J, ⟨a, b, hJ⟩, hn, hd⟩, hJlt⟩ := exists_lt_of_ciInf_lt
    (show ChainsAux.cnSeq H n R < ChainsAux.cnSeq H n R + ε by linarith)
  rw [hs] at hJ
  subst hJ
  exact ⟨a, b, hn, hd, by linarith⟩

/-- The chain condition on the paths below a vertex. -/
def ChainOK (K : Set ℤ) (Hpre : List (Set ℤ)) (T : LTree) : Prop :=
  ∀ P ∈ T.paths, (Hpre ++ P).IsChain (fun L M => M ⊂ L) ∧ start (Hpre ++ P) = K

/-- An attempt at a leaf. -/
theorem leaf_attempt {G : Generator} (hGa : G.Admissible) {K : Set ℤ} (hK : K.Infinite)
    {n : ℕ} {ε : ℝ} (hε : 0 < ε) (L : Set ℤ) (Hpre : List (Set ℤ))
    (hpre : ChainOK K Hpre (LTree.leaf L)) (x : ℤ) (h : List ℤ) :
    ∃ r, (∀ y ∈ r, y ∈ L) ∧
      (Good G L h (h ++ x :: r) → Post G K n ε (LTree.leaf L) Hpre h (h ++ x :: r)) := by
  set h1 := h ++ [x] with hh1
  obtain ⟨R, hR⟩ := HistoryTopologyAux.finite_subset_Icc (used_finite G h1)
  have hpath : [L] ∈ (LTree.leaf L).paths := rfl
  obtain ⟨hc, hst⟩ := hpre [L] hpath
  obtain ⟨a, b, hn, hdisjR, hscore⟩ := choose_J hK (H := Hpre ++ [L]) (by simp) hc hst n R hε
  set J := K ∩ Icc a b with hJ
  have hJfin : J.Finite := (finite_Icc a b).subset inter_subset_right
  have hdisj1 : Disjoint (used G h1) J := hdisjR.symm.mono_left hR
  obtain ⟨r', hr'A, hAu, hcount⟩ :=
    race hGa (hJfin.subset inter_subset_right) h1 (hdisj1.mono_right (inter_subset_right (s := L)))
  refine ⟨r', fun y hy => (hr'A y hy).1, fun hgood => ?_⟩
  have heq : h ++ x :: r' = h1 ++ r' := by simp [hh1]
  rw [heq] at hgood ⊢
  have hinL : used G (h1 ++ r') ∩ J ⊆ L := by
    rintro y ⟨hyu, hyJ⟩
    rcases hyu with hyi | ⟨t, ht, rfl⟩
    · rcases List.mem_append.1 hyi with h' | h'
      · exact absurd hyJ (disjoint_left.1 hdisj1 (Or.inl h'))
      · exact (hr'A y h').1
    · by_cases ht1 : t < h1.length
      · rw [outL_append _ _ _ ht1] at hyJ
        exact absurd hyJ (disjoint_left.1 hdisj1 (Or.inr ⟨t, ht1, rfl⟩))
      · exact hgood t (by simp only [hh1, List.length_append] at ht1 ⊢; omega) ht
  refine ⟨[L], hpath, a, b, hn, hscore, hdisj1.mono_left (used_mono G h [x]), ?_, hinL, ?_⟩
  · rintro y ⟨hyJ, hyL⟩
    exact hAu ⟨hyL, hyJ⟩
  · have hsub : outs G (h1 ++ r') ∩ J ⊆ outs G (h1 ++ r') ∩ (L ∩ J) := by
      rintro y ⟨hyO, hyJ⟩
      exact ⟨hyO, hinL ⟨Or.inr hyO, hyJ⟩, hyJ⟩
    have h1' := ncard_le_ncard hsub
      (hJfin.subset (inter_subset_right.trans inter_subset_right))
    have h2 : (outs G (h1 ++ r') ∩ J).ncard ≤ (L ∩ J).ncard / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]; omega
    simp only [layerSum, layers, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    exact_mod_cast h2

/-- An attempt at an inner vertex, given the mega step at the children. -/
theorem node_attempt {X : Set (Set ℤ)} {G : Generator} (hGa : G.Admissible) {K : Set ℤ}
    {n : ℕ} {ε : ℝ} (L : Set ℤ) (c : ℕ → LTree) (hT : (LTree.node L c).Admissible X)
    (Hpre : List (Set ℤ)) (hpre : ChainOK K Hpre (LTree.node L c))
    (ih : ∀ i, ∀ Hpre h, (∀ x ∈ h, x ∈ (c i).label) → ChainOK K Hpre (c i) →
      ∃ r, (∀ x ∈ r, x ∈ (c i).label) ∧ Post G K n ε (c i) Hpre h (h ++ r))
    (x : ℤ) (hx : x ∈ L) (h : List ℤ) :
    ∃ r, (∀ y ∈ r, y ∈ L) ∧
      ((∀ y ∈ h, y ∈ L) → Good G L h (h ++ x :: r) →
        Post G K n ε (LTree.node L c) Hpre h (h ++ x :: r)) := by
  set h1 := h ++ [x] with hh1
  by_cases hh : ∀ y ∈ h, y ∈ L
  swap
  · exact ⟨[], by simp, fun h' => absurd h' hh⟩
  have hF : ins h1 ⊆ L := by
    intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact hh y hy
    · rw [List.mem_singleton.1 hy]; exact hx
  obtain ⟨i, hi⟩ := hT.2 (ins h1) (List.finite_toSet h1) hF
  obtain ⟨-, hilt, -⟩ := hT.1 i
  set M := (c i).label with hM
  have hpre' : ChainOK K (Hpre ++ [L]) (c i) := fun P hP => by
    have := hpre (L :: P) ⟨i, P, hP, rfl⟩
    simpa using this
  obtain ⟨r1, hr1, P, hP, a, b, hn, hscore, hdisj, hJu, huJ, hcount⟩ :=
    ih i (Hpre ++ [L]) h1 (fun y hy => hi hy) hpre'
  set J := K ∩ Icc a b with hJ
  have hJfin : J.Finite := (finite_Icc a b).subset inter_subset_right
  set h2 := h1 ++ r1 with hh2
  set A := (L \ M) ∩ J with hA
  have hdA : Disjoint (used G h2) A := by
    rw [disjoint_left]
    rintro y hyu ⟨⟨-, hyM⟩, hyJ⟩
    exact hyM (huJ ⟨hyu, hyJ⟩)
  obtain ⟨r2, hr2, hAu, hcA⟩ := race hGa (hJfin.subset inter_subset_right) h2 hdA
  refine ⟨r1 ++ r2, ?_, fun _ hgood => ?_⟩
  · intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact hilt.1 (hr1 y hy)
    · exact (hr2 y hy).1.1
  have heq : h ++ x :: (r1 ++ r2) = h2 ++ r2 := by simp [hh2, hh1]
  rw [heq] at hgood ⊢
  obtain ⟨Q, rfl⟩ := HistoryTopologyAux.paths_head hP
  have hinL : used G (h2 ++ r2) ∩ J ⊆ L := by
    rintro y ⟨hyu, hyJ⟩
    rcases hyu with hyi | ⟨t, ht, rfl⟩
    · rcases List.mem_append.1 hyi with h' | h'
      · exact hilt.1 (huJ ⟨Or.inl h', hyJ⟩)
      · exact (hr2 y h').1.1
    · by_cases ht2 : t < h2.length
      · rw [outL_append _ _ _ ht2] at hyJ ⊢
        exact hilt.1 (huJ ⟨Or.inr ⟨t, ht2, rfl⟩, hyJ⟩)
      · refine hgood t ?_ ht
        simp only [hh2, hh1, List.length_append, List.length_singleton] at ht2 ⊢
        omega
  refine ⟨L :: M :: Q, ⟨i, M :: Q, hP, rfl⟩, a, b, hn, by simpa using hscore,
    hdisj.mono_left (used_mono G h [x]), ?_, hinL, ?_⟩
  · rintro y ⟨hyJ, hyL⟩
    by_cases hyM : y ∈ M
    · exact used_mono G h2 r2 (hJu ⟨hyJ, hyM⟩)
    · exact hAu ⟨⟨hyL, hyM⟩, hyJ⟩
  · have hsub : outs G (h2 ++ r2) ∩ J ⊆ (outs G h2 ∩ J) ∪ (outs G (h2 ++ r2) ∩ A) := by
      rintro y ⟨hyO, hyJ⟩
      by_cases hyM : y ∈ M
      · exact Or.inl ⟨outs_used_sub hGa h2 r2 hyO (hJu ⟨hyJ, hyM⟩), hyJ⟩
      · exact Or.inr ⟨hyO, ⟨hinL ⟨Or.inr hyO, hyJ⟩, hyM⟩, hyJ⟩
    have h1' := (ncard_le_ncard hsub ((hJfin.subset inter_subset_right).union
      (hJfin.subset (inter_subset_right.trans inter_subset_right)))).trans (ncard_union_le _ _)
    have hcA' : 2 * (outs G (h2 ++ r2) ∩ A).ncard ≤ A.ncard := hcA
    have h2' : (outs G (h2 ++ r2) ∩ A).ncard ≤ A.ncard / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]; omega
    have hls : layerSum (L :: M :: Q) J = (((L \ M) ∩ J).ncard / 2 : ℕ) + layerSum (M :: Q) J := by
      simp [layerSum, layers]
    rw [hls]
    push_cast
    have : ((outs G (h2 ++ r2) ∩ J).ncard : ℝ) ≤
        (outs G h2 ∩ J).ncard + (outs G (h2 ++ r2) ∩ A).ncard := by exact_mod_cast h1'
    have : ((outs G (h2 ++ r2) ∩ A).ncard : ℝ) ≤ ((A.ncard / 2 : ℕ) : ℝ) := by exact_mod_cast h2'
    linarith

/-- An enumeration of a language of `X`. -/
theorem enum_of_mem {X : Set (Set ℤ)} (hX : LangClass X) {L : Set ℤ} (hL : L ∈ X) :
    ∃ e : ℕ → ℤ, range e = L := by
  obtain ⟨f, hf⟩ := (Set.to_countable L).exists_eq_range (hX.infinite L hL).nonempty
  exact ⟨f, hf.symm⟩

/-- **The `T`-mega step.** -/
theorem mega {X : Set (Set ℤ)} (hX : LangClass X) {G : Generator} (hGa : G.Admissible)
    (hG : G.EventuallyValidOn X) {K : Set ℤ} (hK : K.Infinite) {n : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ∀ T : LTree, T.Admissible X → T.label ∈ X → ∀ Hpre h, (∀ x ∈ h, x ∈ T.label) →
      ChainOK K Hpre T →
      ∃ r, (∀ x ∈ r, x ∈ T.label) ∧ Post G K n ε T Hpre h (h ++ r) := by
  intro T
  induction T with
  | leaf L =>
    intro _ hLX Hpre h hh hpre
    obtain ⟨e, he⟩ := enum_of_mem hX hLX
    refine attempts hG hLX e he (fun h h' => Post G K n ε (LTree.leaf L) Hpre h h')
      (fun h r h' hp => Post_mono h r h' hp) ?_ h hh
    intro k h
    obtain ⟨r, hr, hpost⟩ := leaf_attempt hGa hK hε L Hpre hpre (e k) h
    exact ⟨r, hr, fun _ hgood => hpost hgood⟩
  | node L c ih =>
    intro hT hLX Hpre h hh hpre
    obtain ⟨e, he⟩ := enum_of_mem hX hLX
    refine attempts hG hLX e he (fun h h' => Post G K n ε (LTree.node L c) Hpre h h')
      (fun h r h' hp => Post_mono h r h' hp) ?_ h hh
    intro k h
    exact node_attempt hGa L c hT Hpre hpre
      (fun i Hpre h hh hc => ih i (hT.1 i).2.2 (hT.1 i).1 Hpre h hh hc) (e k)
      (show e k ∈ L by rw [show L = range e from he.symm]; exact mem_range_self k) h

/-! ## Repeating the mega step -/

/-- One stage `s` of the construction, from a history inside `K`: a refill input `x`, then a
mega step on a near-optimal tree, giving an interval `K ∩ [a, b]` with at least `s` points, all
used, carrying at most `(b_s(K) + 2/(s+1)) |K ∩ [a,b]|` outputs. -/
theorem stage {X : Set (Set ℤ)} (hX : LangClass X) {G : Generator} (hGa : G.Admissible)
    (hG : G.EventuallyValidOn X) {K : Set ℤ} (hK : K ∈ X) (s : ℕ) (x : ℤ) (hx : x ∈ K)
    (h : List ℤ) :
    ∃ r, (∀ y ∈ r, y ∈ K) ∧ ((∀ y ∈ h, y ∈ K) → ∃ a b : ℤ, s ≤ (K ∩ Icc a b).ncard ∧
      K ∩ Icc a b ⊆ used G (h ++ x :: r) ∧
      ((outs G (h ++ x :: r) ∩ (K ∩ Icc a b)).ncard : ℝ) ≤
        (bn X K s + 2 / (s + 1)) * (K ∩ Icc a b).ncard) := by
  have hKi : K.Infinite := hX.infinite K hK
  by_cases hh : ∀ y ∈ h, y ∈ K
  swap
  · exact ⟨[], by simp, fun h' => absurd h' hh⟩
  have hε : (0 : ℝ) < 1 / (s + 1) := by positivity
  have hT0 : def_aot X K (LTree.leaf K) := ⟨rfl, trivial⟩
  have : Nonempty {T : LTree // def_aot X K T} := ⟨⟨_, hT0⟩⟩
  obtain ⟨⟨T, hT⟩, hTlt⟩ := exists_lt_of_ciInf_lt
    (show bn X K s < bn X K s + 1 / (s + 1) by linarith)
  have hKT : T.label.Infinite := by rw [hT.1]; exact hKi
  have hhx : ∀ y ∈ h ++ [x], y ∈ T.label := by
    intro y hy
    rw [hT.1]
    simp only [List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · exact hh y hy
    · exact hx
  have hc : ChainOK K [] T := by
    intro P hP
    obtain ⟨h1, h2⟩ := ChainsAux.path_isChain hK hT hP
    exact ⟨h1.2.2, h2⟩
  obtain ⟨r, hr, P, hP, a, b, hn, hscore, -, hJu, -, hcount⟩ :=
    mega hX hGa hG hKi (n := s) hε T hT.2 (hT.1 ▸ hK) [] (h ++ [x]) hhx hc
  refine ⟨r, fun y hy => hT.1 ▸ hr y hy, fun _ => ⟨a, b, hn, ?_, ?_⟩⟩
  · intro y hy
    have : y ∈ K ∩ Icc a b ∩ T.label := ⟨hy, hT.1 ▸ hy.1⟩
    simpa using hJu this
  · simp only [List.nil_append] at hscore hcount
    simp only [List.append_assoc, List.singleton_append] at hcount
    set J := K ∩ Icc a b
    have hcnle : cn P s ≤ ⨆ H : T.paths, cn H.1 s :=
      le_ciSup (ChainsAux.pathSup_bdd hT.2 hKT s) ⟨P, hP⟩
    have hJfin : J.Finite := (finite_Icc a b).subset inter_subset_right
    rcases Nat.eq_zero_or_pos J.ncard with h0 | hpos
    · have : (outs G (h ++ x :: r) ∩ J).ncard = 0 := by
        have := ncard_le_ncard (inter_subset_right (s := outs G (h ++ x :: r))) hJfin
        omega
      rw [this, h0]; simp
    · have hJpos : (0 : ℝ) < J.ncard := by exact_mod_cast hpos
      have hp : def_raw_pairing_score P J * J.ncard = layerSum P J := by
        rw [score_eq]
        field_simp
      have : def_raw_pairing_score P J ≤ bn X K s + 2 / (s + 1) := by
        have h2 : (2 : ℝ) / (s + 1) = 1 / (s + 1) + 1 / (s + 1) := by ring
        linarith
      calc ((outs G (h ++ x :: r) ∩ J).ncard : ℝ) ≤ layerSum P J := hcount
        _ = def_raw_pairing_score P J * J.ncard := hp.symm
        _ ≤ _ := mul_le_mul_of_nonneg_right this hJpos.le

end UpperAux

/-- **Theorem 5.1** (`thm:upper`). Let `𝒜` be a generator that is eventually valid on every full
enumeration of every language in `X`. Then for every `K ∈ X` there is an adversary enumeration
of `K` such that the output set `O` of `𝒜` satisfies `δ_B(O, K) ≤ b(K)`. -/
theorem thm_upper {X : Set (Set ℤ)} (hX : LangClass X) (G : Generator)
    (hGa : G.Admissible) (hG : G.EventuallyValidOn X) {K : Set ℤ} (hK : K ∈ X) :
    ∃ w, IsFullEnumeration w K ∧ outputDensity (G.outputSet w) K ≤ bK X K := by
  have hKi : K.Infinite := hX.infinite K hK
  obtain ⟨e, he⟩ := UpperAux.enum_of_mem hX hK
  have heK : ∀ s, e s ∈ K := fun s => he ▸ mem_range_self s
  choose r hrK hr using fun s h => UpperAux.stage hX hGa hG hK s (e s) (heK s) h
  let hs : ℕ → List ℤ := fun s => Nat.rec [] (fun s h => h ++ e s :: r s h) s
  have hs_succ : ∀ s, hs (s + 1) = hs s ++ e s :: r s (hs s) := fun s => rfl
  have hsK : ∀ s, ∀ y ∈ hs s, y ∈ K := by
    intro s
    induction s with
    | zero => simp [hs]
    | succ s ih =>
      intro y hy
      rw [hs_succ] at hy
      simp only [List.mem_append, List.mem_cons] at hy
      rcases hy with hy | rfl | hy
      · exact ih y hy
      · exact heK s
      · exact hrK s _ y hy
  have hlen : ∀ s, s ≤ (hs s).length := by
    intro s
    induction s with
    | zero => simp
    | succ s ih => rw [hs_succ]; simp; omega
  obtain ⟨w, hw, hrange⟩ := UpperAux.limit_exists hs (fun s => ⟨_, hs_succ s⟩) hlen
  refine ⟨w, ?_, ?_⟩
  · ext y
    rw [hrange]
    constructor
    · rintro ⟨k, hk⟩; exact hsK k y hk
    · intro hy
      rw [← he] at hy
      obtain ⟨s, rfl⟩ := hy
      exact ⟨s + 1, by rw [hs_succ]; simp⟩
  -- the density bound
  set O := G.outputSet w
  have hstage : ∀ s, ∃ a b : ℤ, s ≤ (K ∩ Icc a b).ncard ∧
      (((O ∩ K) ∩ Icc a b).ncard : ℝ) ≤ (bK X K + 2 / (s + 1)) * (K ∩ Icc a b).ncard := by
    intro s
    obtain ⟨a, b, hn, hJu, hcount⟩ := hr s (hs s) (hsK s)
    refine ⟨a, b, hn, ?_⟩
    have hJfin : (K ∩ Icc a b).Finite := (finite_Icc a b).subset inter_subset_right
    have hsub : (O ∩ K) ∩ Icc a b ⊆ UpperAux.outs G (hs s ++ e s :: r s (hs s)) ∩ (K ∩ Icc a b) := by
      rintro y ⟨⟨hyO, hyK⟩, hyI⟩
      refine ⟨UpperAux.sealed hGa (hw (s + 1)) hyO (hJu ⟨hyK, hyI⟩), hyK, hyI⟩
    have h1 := ncard_le_ncard hsub (hJfin.subset inter_subset_right)
    have hbn : bn X K s ≤ bK X K :=
      (ChainsAux.bn_mono hKi).ge_of_tendsto (ChainsAux.bK_tendsto hKi).1 s
    calc (((O ∩ K) ∩ Icc a b).ncard : ℝ) ≤ _ := by exact_mod_cast h1
      _ ≤ _ := hcount
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hbK0 : 0 ≤ bK X K := (ChainsAux.bK_tendsto hKi).2.1
  unfold outputDensity def_banach_intro
  refine ciSup_le fun m => ?_
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  obtain ⟨s₀, hs₀⟩ := exists_nat_gt (2 / δ)
  set s := max (max m 1) s₀
  obtain ⟨a, b, hn, hle⟩ := hstage s
  have hms : m ≤ s := le_trans (le_max_left _ _) (le_max_left _ _)
  have h1s : 1 ≤ s := le_trans (le_max_right _ _) (le_max_left _ _)
  have hJpos : (0 : ℝ) < (K ∩ Icc a b).ncard := by exact_mod_cast (h1s.trans hn)
  have hinf := ciInf_le (BasicAux.banachInf_bddBelow (O ∩ K) K m)
    (⟨(a, b), hms.trans hn⟩ : {R : ℤ × ℤ // m ≤ (K ∩ Icc R.1 R.2).ncard})
  have hratio : (((O ∩ K) ∩ Icc a b).ncard : ℝ) / (K ∩ Icc a b).ncard ≤ bK X K + 2 / (s + 1) :=
    (div_le_iff₀ hJpos).2 hle
  have hsδ : 2 / ((s : ℝ) + 1) < δ := by
    have : (s₀ : ℝ) ≤ s := by exact_mod_cast le_max_right _ _
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hs₀
    nlinarith
  calc _ ≤ _ := hinf
    _ ≤ bK X K + 2 / (s + 1) := hratio
    _ < bK X K + δ := by linarith

end BanachDensity1D
