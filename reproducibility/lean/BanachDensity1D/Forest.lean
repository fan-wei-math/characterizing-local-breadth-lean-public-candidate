import BanachDensity1D.Construction

/-!
# Lemmas 6.13, 6.14 and 6.20: invariants of the protected forest

Kleinberg–Wei, Part *Dimension one*, Section 6. The statements were moved here from
`Construction.lean` unchanged (a pure move), so that their proofs can use the lemmas proved
before them.
-/

namespace BanachDensity1D

open Set Filter Classical

namespace ForestAux

/-- Ancestors have smaller or equal index. -/
lemma anc_le (R : Requirements) (C : Choices) : ∀ v, ∀ a ∈ (vdata R C v).anc, a ≤ v := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro a ha
    rcases ConstructionAux.vdata_cases R C v with ⟨-, h, -⟩ | ⟨p, -, hpv, -, -, -, h, -⟩
    · rw [h] at ha; simp at ha; omega
    · rw [h] at ha
      rcases List.mem_append.1 ha with ha | ha
      · exact (ih p hpv a ha).trans hpv.le
      · simp at ha; omega

/-- `v ⪯ v`. -/
lemma self_mem_anc (R : Requirements) (C : Choices) (v : ℕ) : v ∈ (vdata R C v).anc := by
  rcases ConstructionAux.vdata_cases R C v with ⟨-, h, -⟩ | ⟨p, -, -, -, -, -, h, -⟩ <;> simp [h]

/-- The ancestor path ends at the vertex. -/
lemma anc_getLast (R : Requirements) (C : Choices) (v : ℕ) : (vdata R C v).anc.getLast? = some v := by
  rcases ConstructionAux.vdata_cases R C v with ⟨-, h, -⟩ | ⟨p, -, -, -, -, -, h, -⟩ <;> simp [h]

/-- `dropWhile` up to a member of the first part of an append. -/
lemma dropWhile_append_mem {l : List ℕ} {a : ℕ} (m : List ℕ) (ha : a ∈ l) :
    (l ++ m).dropWhile (· ≠ a) = l.dropWhile (· ≠ a) ++ m := by
  induction l with
  | nil => simp at ha
  | cons b t ih =>
    by_cases hb : b = a
    · subst hb; simp
    · have : a ∈ t := by simp at ha; tauto
      rw [List.cons_append, List.dropWhile_cons_of_pos (by simpa using hb),
        List.dropWhile_cons_of_pos (by simpa using hb)]
      exact ih this

/-- `dropWhile` up to the appended last entry. -/
lemma dropWhile_append_not_mem {l : List ℕ} {a : ℕ} (ha : a ∉ l) :
    (l ++ [a]).dropWhile (· ≠ a) = [a] := by
  induction l with
  | nil => simp
  | cons b t ih =>
    have hb : b ≠ a := fun h => ha (by simp [h])
    have : a ∉ t := fun h => ha (by simp [h])
    rw [List.cons_append, List.dropWhile_cons_of_pos (by simpa using hb)]
    exact ih this

/-- `dropWhile` up to a member keeps the last entry. -/
lemma getLast?_dropWhile {l : List ℕ} {a : ℕ} (ha : a ∈ l) :
    (l.dropWhile (· ≠ a)).getLast? = l.getLast? := by
  induction l with
  | nil => simp at ha
  | cons b t ih =>
    by_cases hb : b = a
    · subst hb; simp
    · have : a ∈ t := by simp at ha; tauto
      have hne : t ≠ [] := List.ne_nil_of_mem this
      rw [List.dropWhile_cons_of_pos (by simpa using hb), ih this]
      obtain ⟨c, t', rfl⟩ := List.exists_cons_of_ne_nil hne
      simp [List.getLast?_cons_cons]

/-- `compress` of a list with one more entry. -/
lemma compress_snoc : ∀ (l : List (Set ℤ)) (x : Set ℤ),
    compress (l ++ [x]) = if l.getLast? = some x then compress l else compress l ++ [x]
  | [], x => by simp [compress]
  | [a], x => by
    by_cases h : a = x
    · subst h; simp [compress]
    · simp [compress, h]
  | a :: b :: t, x => by
    have ih := compress_snoc (b :: t) x
    have hl : (a :: b :: t).getLast? = (b :: t).getLast? := by simp [List.getLast?_cons_cons]
    rw [hl]
    simp only [List.cons_append] at ih ⊢
    by_cases hab : a = b
    · simp only [compress, hab, ite_true]; exact ih
    · simp only [compress, hab, ite_false, ih]
      split_ifs <;> simp

/-- The chain from `a ⪯ p` to the child `v` of `p`. -/
lemma pathChain_child (R : Requirements) (C : Choices) {v p a : ℕ}
    (hanc : (vdata R C v).anc = (vdata R C p).anc ++ [v]) (ha : a ∈ (vdata R C p).anc) :
    pathChain R C a v = if R.lab p = R.lab v then pathChain R C a p
      else pathChain R C a p ++ [R.lab v] := by
  unfold pathChain
  rw [hanc, dropWhile_append_mem _ ha, List.map_append, List.map_singleton, compress_snoc,
    List.getLast?_map, getLast?_dropWhile ha, anc_getLast]
  simp

/-- `H̄[v,v] = (L_v)`. -/
lemma pathChain_self (R : Requirements) (C : Choices) (v : ℕ) :
    pathChain R C v v = [R.lab v] := by
  unfold pathChain
  rcases ConstructionAux.vdata_cases R C v with ⟨-, h, -⟩ | ⟨p, -, hpv, -, -, -, h, -⟩
  · rw [h]; simp [compress]
  · rw [h, dropWhile_append_not_mem fun hv => by have := anc_le R C p v hv; omega]
    simp [compress]

/-- The total protected set `P_v`, with the boards written through `boardOf`. -/
lemma P_eq (R : Requirements) (C : Choices) (v : ℕ) : (vdata R C v).P =
    ⋃ a ∈ {a | a ∈ (vdata R C v).anc ∧ 0 < R.s a},
      (C.prot a (pathChain R C a v) ∪ ⋃ x : ℤ, {y | y ∈ R.lab v ∩ boardOf R C a x ∧
        def_raw_pairing_score (pathChain R C a v) (R.lab a ∩ boardOf R C a x) < R.s a}) := by
  have h0 : (vdata R C v).P = ⋃ a ∈ {a | a ∈ (vdata R C v).anc ∧ 0 < R.s a},
      (C.prot a (pathChain R C a v) ∪ ⋃ x : ℤ, {y | y ∈ R.lab v ∩ cutBoard
        (if a = v then (vdata R C v).cuts else ((buildForest R C v).getD a default).cuts) x ∧
        def_raw_pairing_score (pathChain R C a v) (R.lab a ∩ cutBoard
        (if a = v then (vdata R C v).cuts else ((buildForest R C v).getD a default).cuts) x)
          < R.s a}) := rfl
  rw [h0]
  refine iUnion₂_congr fun a ha => ?_
  have hc : (if a = v then (vdata R C v).cuts else ((buildForest R C v).getD a default).cuts) =
      (vdata R C a).cuts := by
    split_ifs with h
    · subst h; rfl
    · rw [ConstructionAux.buildForest_getD R C v a (lt_of_le_of_ne (anc_le R C v a ha.1) h)]
  rw [hc]
  rfl

/-- `Prot_a(H̄[a,v]) ⊆ P_v` for `a ⪯ v`, `s_a > 0`. -/
lemma prot_sub_P {R : Requirements} {C : Choices} {a v : ℕ} (ha : a ∈ (vdata R C v).anc)
    (hs : 0 < R.s a) : C.prot a (pathChain R C a v) ⊆ (vdata R C v).P := by
  rw [P_eq]
  intro y hy
  exact mem_biUnion (x := a) ⟨ha, hs⟩ (Or.inl hy)

/-- The trace `L_v ∩ I` of a bad `a`-board `I` lies in `P_v`. -/
lemma bad_sub_P {R : Requirements} {C : Choices} {a v : ℕ} (ha : a ∈ (vdata R C v).anc)
    (hs : 0 < R.s a) {x : ℤ}
    (hbad : def_raw_pairing_score (pathChain R C a v) (R.lab a ∩ boardOf R C a x) < R.s a) :
    R.lab v ∩ boardOf R C a x ⊆ (vdata R C v).P := by
  rw [P_eq]
  intro y hy
  exact mem_biUnion (x := a) ⟨ha, hs⟩ (Or.inr (mem_iUnion.2 ⟨x, hy, hbad⟩))

/-- Labels decrease along ancestry. -/
lemma lab_anc_sub (R : Requirements) (C : Choices) : ∀ v, ∀ a ∈ (vdata R C v).anc,
    R.lab v ⊆ R.lab a := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro a ha
    rcases ConstructionAux.vdata_cases R C v with ⟨-, h, -⟩ | ⟨p, -, hpv, -, hsub, -, h, -⟩
    · rw [h] at ha; simp at ha; subst ha; exact le_rfl
    · rw [h] at ha
      rcases List.mem_append.1 ha with ha | ha
      · exact hsub.trans (ih p hpv a ha)
      · simp at ha; subst ha; exact le_rfl

/-- Boards are order-convex. -/
lemma cutBoard_convex {C : Set ℤ} {x y₁ y₂ y : ℤ} (h₁ : y₁ ∈ cutBoard C x)
    (h₂ : y₂ ∈ cutBoard C x) (hy₁ : y₁ ≤ y) (hy₂ : y ≤ y₂) : y ∈ cutBoard C x := by
  intro c hc ⟨k1, k2⟩
  have e1 := h₁ c hc
  have e2 := h₂ c hc
  omega

/-- A finite nonempty trace of a board is a relative interval. -/
lemma relInterval_of_board {L C : Set ℤ} {x : ℤ} (hfin : (L ∩ cutBoard C x).Finite)
    (hne : (L ∩ cutBoard C x).Nonempty) : IsRelInterval L (L ∩ cutBoard C x) := by
  set S := L ∩ cutBoard C x
  have hb : BddBelow S := hfin.bddBelow
  have ha : BddAbove S := hfin.bddAbove
  have hm : sInf S ∈ S := Int.csInf_mem hne hb
  have hM : sSup S ∈ S := Int.csSup_mem hne ha
  refine ⟨sInf S, sSup S, ?_⟩
  ext y
  constructor
  · intro hy
    exact ⟨hy.1, csInf_le hb hy, le_csSup ha hy⟩
  · rintro ⟨hyL, h1, h2⟩
    exact ⟨hyL, cutBoard_convex hm.2 hM.2 h1 h2⟩

/-- A safe chain has pairing score above the threshold (test with the one-vertex tree). -/
lemma safe_cn {X : Set (Set ℤ)} {n : ℕ} {q : ℝ} {H : List (Set ℤ)} (h : Safe X n q H) :
    q < cn H n := by
  by_contra hle
  push Not at hle
  refine h ⟨LTree.leaf (chainEnd H), ⟨rfl, trivial⟩, fun P hP => ?_⟩
  have hP' : P = [chainEnd H] := hP
  subst hP'
  simpa [appendPath] using hle

/-- `getLast?` of a nonempty list is its `chainEnd`. -/
lemma getLast?_eq_chainEnd {H : List (Set ℤ)} (h : H ≠ []) : H.getLast? = some (chainEnd H) := by
  rw [List.getLast?_eq_some_getLast h, chainEnd, List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast h]
  rfl

/-- Appending does not change the start of a nonempty list. -/
lemma start_snoc {H : List (Set ℤ)} (h : H ≠ []) (x : Set ℤ) : start (H ++ [x]) = start H := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil h
  rfl

/-- The hypotheses on the vertices used by the forest invariants (both vertex systems satisfy
them). `DensityAux.GoodSystem` extends this structure. -/
structure Good (X : Set (Set ℤ)) (R : Requirements) : Prop where
  lab_mem : ∀ v, R.isV v → R.lab v ∈ X
  N_pos : ∀ v, R.isV v → 1 ≤ R.N v
  N_safe : ∀ v, R.isV v → 0 < R.s v → R.s v < bn X (R.lab v) (R.N v)

/-- Under `Good`, `s ≤ 1/2` at every vertex: `N_safe` gives `s_v < b_N(L_v)` when `s_v > 0`, and
`b_N ≤ 1/2`. -/
lemma Good.s_le_half {X : Set (Set ℤ)} (hX : LangClass X) {R : Requirements} (hR : Good X R) :
    ∀ v, R.isV v → R.s v ≤ 1 / 2 := by
  intro v hv
  by_cases h : 0 < R.s v
  · have h1 := hR.N_safe v hv h
    have h2 := (ChainsAux.bn_bounds (X := X) (hX.infinite _ (hR.lab_mem v hv)) (R.N v)).2
    linarith
  · push Not at h; linarith

/-- The forest-path invariant: every `H̄[a,v]` is a chain of `X` from `L_a` to `L_v`, safe for
`(L_a, N_a, s_a)` when `s_a > 0`. -/
lemma path_inv {X : Set (Set ℤ)} (hX : LangClass X) {R : Requirements} (hR : Good X R)
    {C : Choices} (hC : C.Valid X R) : ∀ v, R.isV v → ∀ a ∈ (vdata R C v).anc,
    IsChain X (pathChain R C a v) ∧ start (pathChain R C a v) = R.lab a ∧
      chainEnd (pathChain R C a v) = R.lab v ∧
      (0 < R.s a → Safe X (R.N a) (R.s a) (pathChain R C a v)) := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hv a ha
    have hvX := hR.lab_mem v hv
    have hvs := hR.N_safe v hv
    by_cases hav : a = v
    · subst hav
      rw [pathChain_self]
      exact ⟨⟨by simp, by simpa using hvX, by simp⟩, rfl, rfl,
        fun hs => HistoryTopologyAux.single_safe (hX.infinite _ hvX) (hvs hs)⟩
    rcases ConstructionAux.vdata_cases R C v with ⟨-, h, -⟩ | ⟨p, -, hpv, hpV, hsub, hP, h, -⟩
    · rw [h] at ha; simp at ha; exact absurd ha hav
    have hap : a ∈ (vdata R C p).anc := by
      rw [h] at ha
      rcases List.mem_append.1 ha with ha | ha
      · exact ha
      · simp at ha; exact absurd ha hav
    obtain ⟨hch, hst, hend, hsafe⟩ := ih p hpv hpV a hap
    rw [pathChain_child R C h hap]
    split_ifs with hpl
    · exact ⟨hch, hst, hend.trans hpl, hsafe⟩
    · have hss : R.lab v ⊂ chainEnd (pathChain R C a p) := by
        rw [hend]; exact ssubset_iff_subset_ne.2 ⟨hsub, fun h' => hpl h'.symm⟩
      refine ⟨⟨by simp, ?_, ?_⟩, by rw [start_snoc hch.1, hst], ConstructionAux.chainEnd_snoc _ _,
        fun hs => ?_⟩
      · intro L hL
        rcases List.mem_append.1 hL with hL | hL
        · exact hch.2.1 L hL
        · simp at hL; subst hL; exact hvX
      · refine hch.2.2.append (by simp) ?_
        intro x hx y hy
        rw [getLast?_eq_chainEnd hch.1] at hx
        simp at hx hy
        subst hx hy
        exact hss
      · obtain ⟨-, -, hext⟩ := hC.prot_spec a _ hs (hsafe hs)
        exact hext _ hvX ((prot_sub_P hap hs).trans hP) hss

/-- Lemma 6.12 along the forest: every `v`-board meets `L_v` in finitely many, at least `N_v`
and at most `B_v` points. It needs only that labels lie in `X` and `N ≥ 1` at every vertex (the
fields `lab_mem` and `N_pos` of `Good`); it is the single copy of this induction, used by the
forest invariants here, by `CaptureAux` and by `DensityAux`. -/
lemma board_spec {X : Set (Set ℤ)} (hX : LangClass X) {R : Requirements}
    (hlab : ∀ v, R.isV v → R.lab v ∈ X) (hN : ∀ v, R.isV v → 1 ≤ R.N v)
    {C : Choices} (hC : C.Valid X R) : ∀ v, R.isV v → ∀ x,
    (R.lab v ∩ boardOf R C v x).Finite ∧ R.N v ≤ (R.lab v ∩ boardOf R C v x).ncard ∧
      (R.lab v ∩ boardOf R C v x).ncard ≤ (vdata R C v).B := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hv x
    have hvN := hN v hv
    have hinf := hX.infinite _ (hlab v hv)
    unfold boardOf
    rcases ConstructionAux.vdata_cases R C v with ⟨-, -, hc, hB⟩ | ⟨p, -, hpv, hpV, hsub, -, -, hc, hB⟩
    · rw [hc, hB]
      have h := hC.root_spec v hinf hvN x
      refine ⟨Set.finite_of_ncard_pos (by omega), by omega, by omega⟩
    · rw [hc, hB]
      exact (hC.child_spec v p _ _ hsub hinf hvN fun y => ⟨(ih p hpv hpV y).1,
        (ih p hpv hpV y).2.2⟩).2 x

/-- `P_v` is finite and contained in `L_v`. -/
lemma P_spec {X : Set (Set ℤ)} (hX : LangClass X) {R : Requirements} (hR : Good X R)
    {C : Choices} (hC : C.Valid X R) {v : ℕ} (hv : R.isV v) :
    (vdata R C v).P.Finite ∧ (vdata R C v).P ⊆ R.lab v := by
  rw [P_eq]
  constructor
  · refine Finite.biUnion ((vdata R C v).anc.finite_toSet.subset fun a ha => ha.1) ?_
    rintro a ⟨ha, hs⟩
    obtain ⟨hch, hst, -, hsafe⟩ := path_inv hX hR hC v hv a ha
    have haV := ConstructionAux.isV_of_anc R C v hv a ha
    refine (hC.prot_spec a _ hs (hsafe hs)).1.union ?_
    obtain ⟨R0, hR0⟩ := claim_cn_eventual_interval_bound hX hch (safe_cn (hsafe hs))
    refine ((finite_Icc (-(R0 : ℤ)) R0).biUnion fun z _ =>
      (board_spec hX hR.lab_mem hR.N_pos hC a haV z).1).subset ?_
    intro y hy
    obtain ⟨x, ⟨hyv, hyb⟩, hbad⟩ := mem_iUnion.1 hy
    obtain ⟨hfin, hN, -⟩ := board_spec hX hR.lab_mem hR.N_pos hC a haV x
    have hmeet : ¬ Disjoint (R.lab a ∩ boardOf R C a x) (Icc (-(R0 : ℤ)) R0) := by
      intro hd
      have hne : (R.lab a ∩ boardOf R C a x).Nonempty :=
        Set.nonempty_of_ncard_ne_zero (by have := hR.N_pos a haV; omega)
      have := hR0 _ (by rw [hst]; exact relInterval_of_board hfin hne) hN hd
      linarith
    obtain ⟨z, ⟨-, hzb⟩, hzI⟩ := Set.not_disjoint_iff.1 hmeet
    exact mem_biUnion hzI ⟨lab_anc_sub R C v a ha hyv, (Set.ext_iff.1 (ConstructionAux.cutBoard_eq_of_mem hzb) y).2 hyb⟩
  · refine iUnion₂_subset fun a ⟨ha, hs⟩ => union_subset ?_ ?_
    · obtain ⟨-, -, hend, hsafe⟩ := path_inv hX hR hC v hv a ha
      have := (hC.prot_spec a _ hs (hsafe hs)).2.1
      rwa [hend] at this
    · exact iUnion_subset fun x y hy => hy.1.1

/-- The fixed-`ε` system satisfies `Good`. -/
lemma good_of_fixedEps {X : Set (Set ℤ)} {ε : ℝ} {R : Requirements}
    (hR : IsFixedEpsSystem X ε R) : Good X R :=
  ⟨hR.lab_mem, hR.N_pos, hR.N_safe⟩

/-- The layer sum of a chain extended by one language: the last layer `L` is split into
`L \ M` and `M`. -/
lemma layers_snoc (J M : Set ℤ) : ∀ l : List (Set ℤ), l ≠ [] →
    ((layers (l ++ [M])).map fun E => (((E ∩ J).ncard / 2 : ℕ) : ℝ)).sum +
        (((chainEnd l ∩ J).ncard / 2 : ℕ) : ℝ) =
      ((layers l).map fun E => (((E ∩ J).ncard / 2 : ℕ) : ℝ)).sum +
        ((((chainEnd l \ M) ∩ J).ncard / 2 : ℕ) : ℝ) + (((M ∩ J).ncard / 2 : ℕ) : ℝ)
  | [], h => absurd rfl h
  | [L], _ => by
    simp only [List.cons_append, List.nil_append, layers, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    have : chainEnd [L] = L := rfl
    rw [this]
    ring
  | L :: L' :: t, _ => by
    have ih := layers_snoc J M (L' :: t) (by simp)
    have he : chainEnd (L :: L' :: t) = chainEnd (L' :: t) := by
      simp [chainEnd, List.getLastD_eq_getLast?, List.getLast?_cons_cons]
    rw [he]
    simp only [List.cons_append, layers, List.map_cons, List.sum_cons] at ih ⊢
    linarith

/-- The uniform board bound along forest paths (induction over the path, Lemma 6.14):
`p(H̄[a,w], L_a ∩ I) ≥ s_a - 1/N_a` for every `a`-board `I`, when `s_a > 0`. -/
lemma uniform_aux {X : Set (Set ℤ)} (hX : LangClass X) {R : Requirements} (hR : Good X R)
    {C : Choices} (hC : C.Valid X R) {a : ℕ}
    (haV : R.isV a) (hs : 0 < R.s a) (x : ℤ) : ∀ w, a ∈ (vdata R C w).anc →
    R.s a - 1 / R.N a ≤
      def_raw_pairing_score (pathChain R C a w) (R.lab a ∩ boardOf R C a x) := by
  set J := R.lab a ∩ boardOf R C a x with hJ
  obtain ⟨hJfin, hJN, -⟩ := board_spec hX hR.lab_mem hR.N_pos hC a haV x
  rw [← hJ] at hJfin hJN
  have hN1 : 1 ≤ R.N a := hR.N_pos a haV
  have hNr : (1 : ℝ) ≤ R.N a := by exact_mod_cast hN1
  have hdN : (R.N a : ℝ) ≤ J.ncard := by exact_mod_cast hJN
  have hd0 : (0 : ℝ) < J.ncard := by linarith
  have hdinv : 1 / (J.ncard : ℝ) ≤ 1 / R.N a := one_div_le_one_div_of_le (by linarith) hdN
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro haw
    by_cases haw' : a = w
    · subst haw'
      rw [pathChain_self]
      unfold def_raw_pairing_score
      have hLJ : R.lab a ∩ J = J := by rw [hJ, ← inter_assoc, inter_self]
      simp only [layers, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hLJ]
      rw [one_div_mul_eq_div, le_div_iff₀ hd0]
      have hfl : (J.ncard : ℝ) ≤ 2 * ((J.ncard / 2 : ℕ) : ℝ) + 1 := by
        have : J.ncard ≤ 2 * (J.ncard / 2) + 1 := by omega
        exact_mod_cast this
      have h1 : R.s a * J.ncard ≤ 1 / 2 * J.ncard :=
        mul_le_mul_of_nonneg_right (hR.s_le_half hX a haV) hd0.le
      have h2 : 1 ≤ 1 / (R.N a : ℝ) * J.ncard := by
        rw [one_div_mul_eq_div, le_div_iff₀ (by linarith)]; linarith
      nlinarith
    rcases ConstructionAux.vdata_cases R C w with ⟨-, h, -⟩ | ⟨p, -, hpw, hpV, hsub, hP, h, -⟩
    · rw [h] at haw; simp at haw; exact absurd haw haw'
    have hap : a ∈ (vdata R C p).anc := by
      rw [h] at haw
      rcases List.mem_append.1 haw with haw | haw
      · exact haw
      · simp at haw; exact absurd haw haw'
    have ihp := ih p hpw hap
    rw [pathChain_child R C h hap]
    split_ifs with hpl
    · exact ihp
    obtain ⟨hch, -, hend, -⟩ := path_inv hX hR hC p hpV a hap
    have hsnoc := layers_snoc J (R.lab w) _ hch.1
    rw [hend] at hsnoc
    have hsplit : ((R.lab p \ R.lab w) ∩ J).ncard + (R.lab w ∩ J).ncard = (R.lab p ∩ J).ncard := by
      rw [show (R.lab p \ R.lab w) ∩ J = (R.lab p ∩ J) \ (R.lab w ∩ J) by ext; simp; tauto]
      exact ncard_sdiff_add_ncard_of_subset (inter_subset_inter_left _ hsub)
        (hJfin.subset inter_subset_right)
    unfold def_raw_pairing_score at ihp ⊢
    set S := ((layers (pathChain R C a p)).map fun E => (((E ∩ J).ncard / 2 : ℕ) : ℝ)).sum
    set S' := ((layers (pathChain R C a p ++ [R.lab w])).map
      fun E => (((E ∩ J).ncard / 2 : ℕ) : ℝ)).sum
    by_cases hold : def_raw_pairing_score (pathChain R C a p) J < R.s a
    · have hbad := (bad_sub_P hap hs hold).trans hP
      have h0 : (R.lab p \ R.lab w) ∩ J = ∅ := by
        ext y; simp only [mem_inter_iff, Set.mem_sdiff, mem_empty_iff_false, iff_false, not_and]
        intro hyp hyJ
        exact hyp.2 (hbad ⟨hyp.1, hyJ.2⟩)
      have h1 : R.lab w ∩ J = R.lab p ∩ J := by
        ext y; simp only [mem_inter_iff]
        exact ⟨fun h => ⟨hsub h.1, h.2⟩, fun h => ⟨hbad ⟨h.1, h.2.2⟩, h.2⟩⟩
      rw [h0, h1] at hsnoc
      simp only [ncard_empty, Nat.zero_div, Nat.cast_zero, add_zero] at hsnoc
      have : S' = S := by linarith
      rw [this]; exact ihp
    · push Not at hold
      unfold def_raw_pairing_score at hold
      have hfl : (((R.lab p ∩ J).ncard / 2 : ℕ) : ℝ) ≤
          ((((R.lab p \ R.lab w) ∩ J).ncard / 2 : ℕ) : ℝ) +
            (((R.lab w ∩ J).ncard / 2 : ℕ) : ℝ) + 1 := by
        have : (R.lab p ∩ J).ncard / 2 ≤
            ((R.lab p \ R.lab w) ∩ J).ncard / 2 + (R.lab w ∩ J).ncard / 2 + 1 := by omega
        exact_mod_cast this
      have hS : S - 1 ≤ S' := by linarith
      rw [one_div_mul_eq_div] at hold ⊢
      calc R.s a - 1 / R.N a ≤ S / J.ncard - 1 / J.ncard := by linarith
        _ = (S - 1) / J.ncard := by ring
        _ ≤ S' / J.ncard := div_le_div_of_nonneg_right hS hd0.le

/-- The formal-copy system satisfies `Good`. -/
lemma good_of_copy {X : Set (Set ℤ)} {R : Requirements} {copy : ℕ → ℕ}
    (hR : IsCopySystem X R copy) : Good X R :=
  ⟨fun v _ => hR.lab_mem v, fun v _ => hR.N_pos v, fun v _ => hR.N_safe v⟩

/-- Copies of one language are ordered by index as by copy number. -/
lemma copy_lt {X : Set (Set ℤ)} {R : Requirements} {copy : ℕ → ℕ}
    (hR : IsCopySystem X R copy) : ∀ k x y, R.lab x = R.lab y → copy y = copy x + k + 1 → x < y
  | 0, x, y, hl, hc => hR.order x y hl hc
  | k + 1, x, y, hl, hc => by
    obtain ⟨z, hz, hzc⟩ := hR.surj (R.lab x) (hR.lab_mem x) (copy x + k + 1) (by omega)
    exact (copy_lt hR k x z hz.symm hzc).trans (hR.order z y (hz.trans hl) (by omega))

/-- One step of the parent scan replacing the retained vertex. -/
lemma foldl_step (R : Requirements) {p u : ℕ} (t : List ℕ) (h : R.lab u ⊆ R.lab p) :
    (u :: t).foldl (fun p u' => if R.lab u' ⊆ R.lab p then u' else p) p =
      t.foldl (fun p u' => if R.lab u' ⊆ R.lab p then u' else p) u := by
  simp [h]

/-- The parent scan keeps `u` when no later label lies inside `L_u`
(`ConstructionAux.foldl_inv` with `P := (· = u)`). -/
lemma foldl_stay (R : Requirements) {u : ℕ} (t : List ℕ) (h : ∀ e ∈ t, ¬ R.lab e ⊆ R.lab u) :
    t.foldl (fun p u' => if R.lab u' ⊆ R.lab p then u' else p) u = u :=
  ConstructionAux.foldl_inv R (· = u) t u rfl fun p e he hp => by
    subst hp; exact ite_eq_right (h e he)

/-- The parent scan returns `u` if `u` is a possible parent contained in the labels of all
possible parents, and no later possible parent has its label inside `L_u`. -/
lemma scanParent_eq (R : Requirements) {l : List ℕ} {u : ℕ} (hu : u ∈ l)
    (hall : ∀ e ∈ l, R.lab u ⊆ R.lab e) (hsort : l.Pairwise (· < ·))
    (hlater : ∀ e ∈ l, u < e → ¬ R.lab e ⊆ R.lab u) : scanParent R l = some u := by
  obtain ⟨t1, t2, rfl⟩ := List.append_of_mem hu
  have ht2 : ∀ e ∈ t2, ¬ R.lab e ⊆ R.lab u := by
    intro e he
    refine hlater e (by simp [he]) ?_
    rw [List.pairwise_append] at hsort
    exact List.rel_of_pairwise_cons hsort.2.1 he
  cases t1 with
  | nil => simp only [List.nil_append, scanParent, foldl_stay R t2 ht2]
  | cons b t1 =>
    simp only [List.cons_append, scanParent, List.foldl_append, Option.some.injEq]
    have hm := ConstructionAux.foldl_mem R t1 b
    rw [foldl_step R t2 (hall _ (by
      rcases List.mem_cons.1 hm with h | h
      · rw [h]; simp
      · simp [h])), foldl_stay R t2 ht2]

/-- Lemma 6.13 for any vertex system satisfying `Good`. -/
lemma forest_invariant_gen {X : Set (Set ℤ)} (hX : LangClass X) {R : Requirements}
    (hR : Good X R) {C : Choices} (hC : C.Valid X R) {v : ℕ} (hv : R.isV v) :
    {a | IsAnc R C a v}.Finite ∧ (vdata R C v).P.Finite ∧ (vdata R C v).P ⊆ R.lab v ∧
    ∀ a, IsAnc R C a v → 0 < R.s a → Safe X (R.N a) (R.s a) (pathChain R C a v) :=
  ⟨(vdata R C v).anc.finite_toSet, (P_spec hX hR hC hv).1, (P_spec hX hR hC hv).2,
    fun a ha hs => (path_inv hX hR hC v hv a ha).2.2.2 hs⟩

/-- Lemma 6.14 for any vertex system satisfying `Good`: the
board bound `max 0 (s_a - 1/N_a) ≤ p(H[a,v], L_a ∩ I)` (the first conjunct of Lemma 6.14). -/
lemma uniform_board_gen {X : Set (Set ℤ)} (hX : LangClass X) {R : Requirements}
    (hR : Good X R) {C : Choices} (hC : C.Valid X R)
    {a v : ℕ} (hv : R.isV v) (hav : IsAnc R C a v) (x : ℤ) :
    max 0 (R.s a - 1 / R.N a) ≤
        def_raw_pairing_score (pathChain R C a v) (R.lab a ∩ boardOf R C a x) := by
  have haV := ConstructionAux.isV_of_anc R C v hv a hav
  refine max_le (ChainsAux.raw_score_nonneg _ _) ?_
  by_cases hs : 0 < R.s a
  · exact uniform_aux hX hR hC haV hs x v hav
  · have : (0 : ℝ) ≤ 1 / R.N a := by positivity
    linarith [ChainsAux.raw_score_nonneg (pathChain R C a v) (R.lab a ∩ boardOf R C a x)]

/-- The fixed-`ε` system has `q ≤ max 0 (s - 1/N)` at every vertex (used by Lemma 6.14 and by
`DensityAux.goodSystem_fixed`). -/
lemma fixedEps_q_le {X : Set (Set ℤ)} {ε : ℝ} {R : Requirements} (hR : IsFixedEpsSystem X ε R) :
    ∀ v, R.isV v → R.q v ≤ max 0 (R.s v - 1 / R.N v) := by
  intro v hv
  rw [hR.q_def v hv, hR.s_def v hv]
  have h1 := hR.N_small v hv
  refine max_le ?_ (le_max_left _ _)
  refine le_trans ?_ (le_max_right _ _)
  have := le_max_left (bK X (R.lab v) - ε / 2) 0
  linarith

end ForestAux

/-- **Lemma 6.13** (`lem:forest-invariant`). The construction is well defined: every vertex has
finitely many ancestors and a finite `P_v ⊆ L_v`, and for every `a ⪯ v` with `s_a > 0` the chain
`H[a,v]` is safe for `(L_a, N_a, s_a)`. The hypothesis `hε : 0 < ε` mirrors the paper's fixed
`ε > 0` of Section 6.4; the Lean proof does not use it. -/
theorem lem_forest_invariant {X : Set (Set ℤ)} (hX : LangClass X) {ε : ℝ} (hε : 0 < ε)
    {R : Requirements} (hR : IsFixedEpsSystem X ε R) {C : Choices} (hC : C.Valid X R)
    {v : ℕ} (hv : R.isV v) :
    {a | IsAnc R C a v}.Finite ∧ (vdata R C v).P.Finite ∧ (vdata R C v).P ⊆ R.lab v ∧
    ∀ a, IsAnc R C a v → 0 < R.s a → Safe X (R.N a) (R.s a) (pathChain R C a v) :=
  ForestAux.forest_invariant_gen hX (ForestAux.good_of_fixedEps hR) hC hv

/-- **Lemma 6.14** (`lem:uniform-board`, uniform board bound). For every `a ⪯ v` and every
`a`-board `I`, `p(H[a,v], L_a ∩ I) ≥ max{0, s_a - 1/N_a} ≥ q_a`. The hypothesis `hε : 0 < ε`
mirrors the paper's fixed `ε > 0` of Section 6.4; the Lean proof does not use it. -/
theorem lem_uniform_board {X : Set (Set ℤ)} (hX : LangClass X) {ε : ℝ} (hε : 0 < ε)
    {R : Requirements} (hR : IsFixedEpsSystem X ε R) {C : Choices} (hC : C.Valid X R)
    {a v : ℕ} (hv : R.isV v) (hav : IsAnc R C a v) (x : ℤ) :
    max 0 (R.s a - 1 / R.N a) ≤
        def_raw_pairing_score (pathChain R C a v) (R.lab a ∩ boardOf R C a x) ∧
      R.q a ≤ max 0 (R.s a - 1 / R.N a) := by
  exact ⟨ForestAux.uniform_board_gen hX (ForestAux.good_of_fixedEps hR) hC hv hav x,
    ForestAux.fixedEps_q_le hR a (ConstructionAux.isV_of_anc R C v hv a hav)⟩

/-- **Lemma 6.20** (`lem:copies-chain`). For `m > 1` the parent of the formal vertex `(L, m)` is
`(L, m - 1)`; consequently, all formal copies of `L` lie on one ancestor–descendant chain: of
any two vertices with the same label, one is an ancestor of the other. -/
theorem lem_copies_chain {X : Set (Set ℤ)} (hX : LangClass X) {R : Requirements}
    {copy : ℕ → ℕ} (hR : IsCopySystem X R copy) {C : Choices} (hC : C.Valid X R) :
    (∀ u v, R.lab u = R.lab v → copy v = copy u + 1 → (vdata R C v).parent = some u) ∧
    ∀ u v, R.lab u = R.lab v → IsAnc R C u v ∨ IsAnc R C v u := by
  have hG := ForestAux.good_of_copy hR
  have part1 : ∀ u v, R.lab u = R.lab v → copy v = copy u + 1 → (vdata R C v).parent = some u := by
    intro u v hl hc
    have huv : u < v := hR.order u v hl hc
    show scanParent R (possibleParents R (buildForest R C v) v) = some u
    refine ForestAux.scanParent_eq R ?_ ?_ ?_ ?_
    · simp only [possibleParents, List.mem_filter, List.mem_range, decide_eq_true_eq]
      rw [ConstructionAux.buildForest_getD R C v u huv]
      exact ⟨huv, hR.all u, hl ▸ le_rfl, hl ▸ (ForestAux.P_spec hX hG hC (hR.all u)).2⟩
    · intro e he
      simp only [possibleParents, List.mem_filter, List.mem_range, decide_eq_true_eq] at he
      rw [hl]; exact he.2.2.1
    · exact (List.pairwise_lt_range).filter _
    · intro e he hue hsub
      simp only [possibleParents, List.mem_filter, List.mem_range, decide_eq_true_eq] at he
      have hle : R.lab e = R.lab u := le_antisymm hsub (hl ▸ he.2.2.1)
      rcases lt_trichotomy (copy e) (copy u) with h1 | h1 | h1
      · have := ForestAux.copy_lt hR (copy u - copy e - 1) e u hle (by omega); omega
      · have := hR.inj e u hle h1; omega
      · rcases lt_or_eq_of_le (show copy v ≤ copy e by omega) with h2 | h2
        · have := ForestAux.copy_lt hR (copy e - copy v - 1) v e (hle.trans hl).symm (by omega); omega
        · have := hR.inj e v (hle.trans hl) h2.symm; omega
  refine ⟨part1, ?_⟩
  have key : ∀ k u v, R.lab u = R.lab v → copy v = copy u + k → IsAnc R C u v := by
    intro k
    induction k with
    | zero =>
      intro u v hl hc
      rw [hR.inj u v hl (by omega)]
      exact ForestAux.self_mem_anc R C v
    | succ k ih =>
      intro u v hl hc
      obtain ⟨z, hz, hzc⟩ := hR.surj (R.lab u) (hR.lab_mem u) (copy u + k)
        (by have := hR.copy_pos u; omega)
      have hzu := ih u z hz.symm hzc
      have hpar := part1 z v (hz.trans hl) (by omega)
      unfold IsAnc
      rcases ConstructionAux.vdata_cases R C v with ⟨h, -⟩ | ⟨p, h, -, -, -, -, hanc, -⟩
      · rw [h] at hpar; exact absurd hpar (by simp)
      · rw [h] at hpar
        cases hpar
        rw [hanc]
        exact List.mem_append_left _ hzu
  intro u v hl
  rcases le_total (copy u) (copy v) with h | h
  · exact Or.inl (key (copy v - copy u) u v hl (by omega))
  · exact Or.inr (key (copy u - copy v) v u hl.symm (by omega))

namespace ForestAux

/-- Lemma 6.13 for the formal-copy system (Section 6.8.3, tex l.3818–3843). -/
theorem forest_invariant_copy {X : Set (Set ℤ)} (hX : LangClass X) {R : Requirements}
    {copy : ℕ → ℕ} (hR : IsCopySystem X R copy) {C : Choices} (hC : C.Valid X R) (v : ℕ) :
    {a | IsAnc R C a v}.Finite ∧ (vdata R C v).P.Finite ∧ (vdata R C v).P ⊆ R.lab v ∧
    ∀ a, IsAnc R C a v → 0 < R.s a → Safe X (R.N a) (R.s a) (pathChain R C a v) :=
  forest_invariant_gen hX (good_of_copy hR) hC (hR.all v)

end ForestAux

end BanachDensity1D
