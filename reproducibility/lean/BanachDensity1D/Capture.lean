import BanachDensity1D.Forest

/-!
# Lemmas 6.15, 6.16, 6.17 and 6.21: history inclusion, capture and validity

Kleinberg–Wei, Part *Dimension one*, Section 6. The statements were moved here from
`Construction.lean` unchanged (a pure move), so that their proofs can use the lemmas proved
before them.
-/

namespace BanachDensity1D

open Set Filter Classical

namespace CaptureAux

variable {R : Requirements} {C : Choices}

/-- The parent of `v` is the result of the parent scan over its possible parents. -/
lemma parent_eq (R : Requirements) (C : Choices) (v : ℕ) :
    (vdata R C v).parent = scanParent R (possibleParents R (buildForest R C v) v) := rfl

/-- A root's ancestor path is `[v]`, its cuts are the root cuts and `B_v = N_v` (from
`ConstructionAux.vdata_cases`). -/
lemma of_none {v : ℕ} (h : (vdata R C v).parent = none) :
    (vdata R C v).anc = [v] ∧ (vdata R C v).cuts = C.rootCuts v ∧ (vdata R C v).B = R.N v := by
  rcases ConstructionAux.vdata_cases R C v with ⟨-, h1, h2, h3⟩ | ⟨p, hp, -⟩
  · exact ⟨h1, h2, h3⟩
  · rw [hp] at h; cases h

/-- The data of a vertex with parent `u` (from `ConstructionAux.vdata_cases`). -/
lemma of_some {v u : ℕ} (h : (vdata R C v).parent = some u) :
    u < v ∧ R.isV u ∧ R.lab v ⊆ R.lab u ∧ (vdata R C u).P ⊆ R.lab v ∧
      (vdata R C v).anc = (vdata R C u).anc ++ [v] ∧
      (vdata R C v).cuts = C.childCuts v u (vdata R C u).cuts (vdata R C u).B ∧
      (vdata R C v).B = R.N v + (vdata R C u).B - 1 := by
  rcases ConstructionAux.vdata_cases R C v with ⟨h0, -⟩ | ⟨p, hp, hrest⟩
  · rw [h0] at h; cases h
  · rw [hp] at h
    obtain rfl := Option.some_inj.1 h
    exact hrest

/-- Unfolding ancestry one step. -/
lemma isAnc_cases {a v : ℕ} (h : IsAnc R C a v) :
    a = v ∨ ∃ u, (vdata R C v).parent = some u ∧ IsAnc R C a u := by
  unfold IsAnc at h
  rcases hp : (vdata R C v).parent with _ | u
  · rw [(of_none hp).1] at h; simp at h; exact Or.inl h
  · rw [(of_some hp).2.2.2.2.1] at h
    rcases List.mem_append.1 h with h | h
    · exact Or.inr ⟨u, rfl, h⟩
    · simp at h; exact Or.inl h

/-- An ancestor of the parent is an ancestor. -/
lemma isAnc_of_parent {a u v : ℕ} (hp : (vdata R C v).parent = some u) (h : IsAnc R C a u) :
    IsAnc R C a v := by
  unfold IsAnc; rw [(of_some hp).2.2.2.2.1]; exact List.mem_append_left _ h

/-- Ancestors have smaller-or-equal index and larger-or-equal label (from `ForestAux.anc_le`
and `ForestAux.lab_anc_sub`). -/
lemma isAnc_le (v a : ℕ) (h : IsAnc R C a v) : a ≤ v ∧ R.lab v ⊆ R.lab a :=
  ⟨ForestAux.anc_le R C v a h, ForestAux.lab_anc_sub R C v a h⟩

/-- Ancestry is transitive. -/
lemma isAnc_trans : ∀ c a b, IsAnc R C a b → IsAnc R C b c → IsAnc R C a c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro a b hab hbc
    rcases isAnc_cases hbc with rfl | ⟨u, hp, hu⟩
    · exact hab
    · exact isAnc_of_parent hp (ih u (of_some hp).1 a b hab hu)

/-- The ancestors of a vertex form a chain ordered by index. -/
lemma isAnc_of_le : ∀ v a b, IsAnc R C a v → IsAnc R C b v → a ≤ b → IsAnc R C a b := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro a b ha hb hab
    rcases isAnc_cases hb with rfl | ⟨u, hp, hu⟩
    · exact ha
    · rcases isAnc_cases ha with rfl | ⟨u', hp', hu'⟩
      · have h1 := (isAnc_le u b hu).1
        have h2 := (of_some hp).1
        omega
      · rw [hp] at hp'
        cases hp'
        exact ih u (of_some hp).1 a b hu' hu hab

section boards

variable {X : Set (Set ℤ)} (hX : LangClass X) (hlab : ∀ v, R.isV v → R.lab v ∈ X)
  (hN : ∀ v, R.isV v → 1 ≤ R.N v) (hC : C.Valid X R)
include hX hlab hN hC

/-- Descendant partitions coarsen ancestor partitions. -/
lemma cuts_sub : ∀ v, R.isV v → ∀ a, IsAnc R C a v → (vdata R C v).cuts ⊆ (vdata R C a).cuts := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hv a ha
    rcases isAnc_cases ha with rfl | ⟨u, hp, hu⟩
    · exact subset_rfl
    · obtain ⟨huv, huV, hsub, -, -, hc, -⟩ := of_some hp
      rw [hc]
      exact (hC.child_spec v u _ _ hsub (hX.infinite _ (hlab v hv)) (hN v hv)
        (fun y => ⟨(ForestAux.board_spec hX hlab hN hC u huV y).1,
          (ForestAux.board_spec hX hlab hN hC u huV y).2.2⟩)).1.trans (ih u huv huV a hu)

/-- `I_a(x) ⊆ I_v(x)` for `a ⪯ v`. -/
lemma board_sub {a v : ℕ} (hv : R.isV v) (ha : IsAnc R C a v) (x : ℤ) :
    boardOf R C a x ⊆ boardOf R C v x :=
  ConstructionAux.cutBoard_mono (cuts_sub hX hlab hN hC v hv a ha) x

end boards

/-- The LCA of a set `S` containing `y₀`, all of whose members descend from `v`: it is a common
ancestor, it is at least `v`, and it is the largest common ancestor. -/
lemma lca_spec {S : Set ℕ} {y₀ v : ℕ} (hy₀ : y₀ ∈ S) (hv : ∀ y ∈ S, IsAnc R C v y) :
    (∀ y ∈ S, IsAnc R C (lca R C S) y) ∧ IsAnc R C v (lca R C S) ∧
      ∀ a, (∀ y ∈ S, IsAnc R C a y) → a ≤ lca R C S := by
  have hbdd : BddAbove {a | ∀ y ∈ S, IsAnc R C a y} :=
    ⟨y₀, fun a ha => (isAnc_le _ _ (ha y₀ hy₀)).1⟩
  have hmem : lca R C S ∈ {a | ∀ y ∈ S, IsAnc R C a y} := Nat.sSup_mem ⟨v, hv⟩ hbdd
  refine ⟨hmem, isAnc_of_le y₀ v _ (hv y₀ hy₀) (hmem y₀ hy₀) (le_csSup hbdd hv),
    fun a ha => le_csSup hbdd ha⟩

/-- `getD` at the last index is `getLastD`. -/
lemma getD_last (ws : List ℤ) (hws : ws ≠ []) : ws.getD (ws.length - 1) 0 = ws.getLastD 0 := by
  obtain ⟨l, a, rfl⟩ := List.eq_nil_or_concat ws |>.resolve_left hws
  simp [List.getD_eq_getElem?_getD]

/-- The current guess belongs to the current history of every active vertex. -/
lemma mem_history {ws : List ℤ} (hws : ws ≠ []) {Q v : ℕ} (hQ : guess R ws = some Q)
    (hv : IsAnc R C v Q) :
    Q ∈ recordHistory R C ws v (boardOf R C v (ws.getLastD 0)) := by
  have hlen := List.length_pos_of_ne_nil hws
  refine ⟨ws.length - 1, by omega, ?_, hv, ?_⟩
  · rw [List.take_of_length_le (by omega)]; exact hQ
  · rw [getD_last ws hws]; exact ConstructionAux.mem_cutBoard_self _ _

/-- Members of a history descend from its vertex. -/
lemma history_anc {ws : List ℤ} {v : ℕ} {I : Set ℤ} {y : ℕ}
    (hy : y ∈ recordHistory R C ws v I) : IsAnc R C v y := by
  obtain ⟨_, _, _, h, _⟩ := hy
  exact h

/-! ### The parent scan and capture -/

/-- The parent scan over an increasing list containing `z`, all of whose earlier members
contain `L_z`, ends at some `p ≥ z` with `L_p ⊆ L_z` (because the scan retains `z` when it reaches
it; that intermediate fact is part of the proof, not of the statement). -/
lemma scan_ge (R : Requirements) (l : List ℕ) (hl : l.Pairwise (· < ·)) (z : ℕ) (hz : z ∈ l)
    (hlt : ∀ u ∈ l, u < z → R.lab z ⊆ R.lab u) :
    ∃ p, scanParent R l = some p ∧ z ≤ p ∧ R.lab p ⊆ R.lab z := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hz
  rw [List.pairwise_append, List.pairwise_cons] at hl
  obtain ⟨-, ⟨ht, -⟩, hst⟩ := hl
  have key : ∀ q, z ≤ q ∧ R.lab q ⊆ R.lab z →
      z ≤ t.foldl (fun p u' => if R.lab u' ⊆ R.lab p then u' else p) q ∧
      R.lab (t.foldl (fun p u' => if R.lab u' ⊆ R.lab p then u' else p) q) ⊆ R.lab z := by
    intro q hq
    refine ConstructionAux.foldl_inv R (fun p => z ≤ p ∧ R.lab p ⊆ R.lab z) t q hq ?_
    intro p u hu hp
    split_ifs with h
    · exact ⟨(ht u hu).le, h.trans hp.2⟩
    · exact hp
  rcases s with _ | ⟨a, s'⟩
  · exact ⟨_, rfl, key z ⟨le_rfl, subset_rfl⟩⟩
  · refine ⟨(t.foldl (fun p u' => if R.lab u' ⊆ R.lab p then u' else p)
      ((fun p u' => if R.lab u' ⊆ R.lab p then u' else p)
        (s'.foldl (fun p u' => if R.lab u' ⊆ R.lab p then u' else p) a) z)), ?_, ?_⟩
    · simp only [List.cons_append, scanParent, List.foldl_append, List.foldl_cons]
    have hm := ConstructionAux.foldl_mem R s' a
    have hlt' : s'.foldl (fun p u' => if R.lab u' ⊆ R.lab p then u' else p) a < z :=
      hst _ hm z List.mem_cons_self
    simp only
    rw [if_pos (hlt _ (List.mem_append_left _ hm) hlt')]
    exact key z ⟨le_rfl, subset_rfl⟩

/-- The capture argument of Lemmas 6.16 / 6.21: if `P_z ⊆ S` and every earlier vertex whose
label contains `S` contains `L_z`, then every `v ≥ z` with `S ⊆ L_v ⊆ L_z` descends from `z`. -/
lemma capture_core {z : ℕ} (hz : R.isV z) {S : Set ℤ} (hPz : (vdata R C z).P ⊆ S)
    (hearly : ∀ u < z, R.isV u → S ⊆ R.lab u → R.lab z ⊆ R.lab u) :
    ∀ v, z ≤ v → S ⊆ R.lab v → R.lab v ⊆ R.lab z → IsAnc R C z v := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hzv hSv hvz
    rcases eq_or_lt_of_le hzv with rfl | hlt
    · exact ForestAux.self_mem_anc R C z
    · have hmem : z ∈ possibleParents R (buildForest R C v) v := by
        simp only [possibleParents, List.mem_filter, List.mem_range, decide_eq_true_eq]
        rw [ConstructionAux.buildForest_getD R C v z hlt]
        exact ⟨hlt, hz, hvz, hPz.trans hSv⟩
      have hpw : (possibleParents R (buildForest R C v) v).Pairwise (· < ·) :=
        List.pairwise_lt_range.filter _
      obtain ⟨p, hp, hzp, hpz⟩ := scan_ge R _ hpw z hmem (by
        intro u hu huz
        simp only [possibleParents, List.mem_filter, List.mem_range, decide_eq_true_eq] at hu
        exact hearly u huz hu.2.1 (hSv.trans hu.2.2.1))
      rw [← parent_eq] at hp
      obtain ⟨hpv, -, hvp, -⟩ := of_some hp
      exact isAnc_of_parent hp (ih p hpv hzp (hSv.trans hvp) hpz)

/-- The inputs so far are points of the enumerated language. -/
lemma inputs_sub {w : ℕ → ℤ} {K : Set ℤ} (hw : IsFullEnumeration w K) (t : ℕ) :
    {x | x ∈ inputsUpTo w t} ⊆ K := by
  intro x hx
  simp only [inputsUpTo, mem_ofPred_eq, List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  rw [← hw]; exact ⟨i, rfl⟩

/-- A finite subset of the enumerated language has appeared after some finite time. -/
lemma eventually_sub {w : ℕ → ℤ} {K : Set ℤ} (hw : IsFullEnumeration w K) {A : Set ℤ}
    (hA : A.Finite) (hAK : A ⊆ K) : ∃ T, ∀ t ≥ T, A ⊆ {x | x ∈ inputsUpTo w t} := by
  let idx : ℤ → ℕ := fun a => if h : ∃ i, w i = a then h.choose else 0
  obtain ⟨M, hM⟩ := (hA.image idx).bddAbove
  refine ⟨M, fun t ht a ha => ?_⟩
  have hex : ∃ i, w i = a := by rw [← mem_range, hw]; exact hAK ha
  have hle : idx a ≤ M := hM ⟨a, ha, rfl⟩
  have hidx : w (idx a) = a := by simp only [idx, dif_pos hex]; exact hex.choose_spec
  rw [← hidx]
  exact ConstructionAux.mem_inputsUpTo w (by omega)

/-- Capture (Lemmas 6.16 and 6.21) for any vertex `z` whose total protected set `P_z` is a
finite subset of `L_z`. -/
theorem capture_of_P {z : ℕ} (hz : R.isV z) {w : ℕ → ℤ} (hw : IsFullEnumeration w (R.lab z))
    (hPf : (vdata R C z).P.Finite) (hPz : (vdata R C z).P ⊆ R.lab z) :
    ∃ t₀, ∀ t ≥ t₀, ∃ Q, guess R (inputsUpTo w t) = some Q ∧ IsAnc R C z Q := by
  set K := R.lab z with hK
  let wit : ℕ → ℤ := fun u => if h : ∃ k ∈ K, k ∉ R.lab u then h.choose else 0
  have hwit : ∀ u, ¬ K ⊆ R.lab u → wit u ∈ K ∧ wit u ∉ R.lab u := by
    intro u hu
    have hex : ∃ k ∈ K, k ∉ R.lab u := by
      by_contra hne; push Not at hne; exact hu hne
    simp only [wit, dif_pos hex]
    exact hex.choose_spec
  set A : Set ℤ := (vdata R C z).P ∪ wit '' {u | u < z ∧ ¬ K ⊆ R.lab u} with hA
  have hAf : A.Finite :=
    hPf.union (((finite_Iio z).subset fun u hu => hu.1).image wit)
  have hAK : A ⊆ K := by
    rintro a (ha | ⟨u, hu, rfl⟩)
    · exact hPz ha
    · exact (hwit u hu.2).1
  obtain ⟨T, hT⟩ := eventually_sub hw hAf hAK
  refine ⟨max T z, fun t ht => ?_⟩
  set S : Set ℤ := {x | x ∈ inputsUpTo w t} with hS
  have hAS : A ⊆ S := hT t (le_of_max_le_left ht)
  have hSK : S ⊆ K := inputs_sub hw t
  have hearly : ∀ u < z, R.isV u → S ⊆ R.lab u → R.lab z ⊆ R.lab u := by
    intro u hu _ hSu
    by_contra hne
    exact (hwit u hne).2 (hSu (hAS (Or.inr ⟨u, ⟨hu, hne⟩, rfl⟩)))
  have hcrit : Critical R S z := ⟨⟨hz, hSK⟩, fun u hu hcu => hearly u hu hcu.1 hcu.2⟩
  have hlen : (inputsUpTo w t).length = t + 1 := by simp [inputsUpTo]
  have hzt : z ≤ t := le_of_max_le_right ht
  have hex : ∃ v < (inputsUpTo w t).length, Critical R {x | x ∈ inputsUpTo w t} v :=
    ⟨z, by omega, hcrit⟩
  have hg : guess R (inputsUpTo w t) =
      some (Nat.findGreatest (Critical R S) ((inputsUpTo w t).length - 1)) := by
    unfold guess; rw [if_pos hex]
  refine ⟨_, hg, ?_⟩
  set Q := Nat.findGreatest (Critical R S) ((inputsUpTo w t).length - 1)
  have hzQ : z ≤ Q := Nat.le_findGreatest (by omega) hcrit
  have hcQ : Critical R S Q := ConstructionAux.guess_critical hg
  have hQK : R.lab Q ⊆ R.lab z := by
    rcases eq_or_lt_of_le hzQ with h | h
    · rw [h]
    · exact hcQ.2 z h hcrit.1
  exact capture_core hz (subset_union_left.trans hAS) hearly Q hzQ hcQ.1.2 hQK

/-! ### Validity -/

lemma inputsUpTo_getD (w : ℕ → ℤ) {r t : ℕ} (h : r ≤ t) : (inputsUpTo w t).getD r 0 = w r := by
  rw [List.getD_eq_getElem?_getD]
  have hr : r < (inputsUpTo w t).length := by simp only [inputsUpTo, List.length_ofFn]; omega
  rw [List.getElem?_eq_getElem hr]
  simp only [inputsUpTo, List.getElem_ofFn, Option.getD_some]

lemma inputsUpTo_getLastD (w : ℕ → ℤ) (t : ℕ) : (inputsUpTo w t).getLastD 0 = w t := by
  rw [← getD_last _ (ConstructionAux.inputsUpTo_ne_nil w t)]
  have : (inputsUpTo w t).length - 1 = t := by simp [inputsUpTo]
  rw [this, inputsUpTo_getD w le_rfl]

/-- Validity (Lemma 6.17) from a capture time: only finitely many outputs lie outside `K = L_z`.
(Proof sketch: the proof shows that after `t₀` an output outside `K` lies in the finite set of
traces `L_v ∩ I_v(w_r)` of the boards of early rounds `r < t₀` at the vertices `v` active on
them; that localisation is not part of the statement.) -/
theorem validity_of_capture {X : Set (Set ℤ)} (hX : LangClass X)
    (hlab : ∀ v, R.isV v → R.lab v ∈ X) (hN : ∀ v, R.isV v → 1 ≤ R.N v) (hC : C.Valid X R)
    {z : ℕ} {w : ℕ → ℤ} {t₀ : ℕ}
    (ht₀ : ∀ t ≥ t₀, ∃ Q, guess R (inputsUpTo w t) = some Q ∧ IsAnc R C z Q) :
    (algGen R C).AlmostAllIn w (R.lab z) := by
  set F : Set ℤ := ⋃ r ∈ Iio t₀, ⋃ Q ∈ {Q | guess R (inputsUpTo w r) = some Q},
    ⋃ v ∈ {v | IsAnc R C v Q}, R.lab v ∩ boardOf R C v (w r) with hF
  have hFf : F.Finite := by
    refine (finite_Iio t₀).biUnion fun r _ => ?_
    refine Set.Subsingleton.finite (fun Q₁ h₁ Q₂ h₂ => ?_) |>.biUnion fun Q hQ => ?_
    · have h₁' : guess R (inputsUpTo w r) = some Q₁ := h₁
      have h₂' : guess R (inputsUpTo w r) = some Q₂ := h₂
      rw [h₁'] at h₂'; exact Option.some_inj.1 h₂'
    · refine ((vdata R C Q).anc.finite_toSet).biUnion fun v hv => ?_
      have hQV : R.isV Q := ConstructionAux.guess_isV hQ
      exact (ForestAux.board_spec hX hlab hN hC v (ConstructionAux.isV_of_anc R C Q hQV v hv) (w r)).1
  have hkey : ∀ t ≥ t₀, (algGen R C).out w t ∈ R.lab z ∨ (algGen R C).out w t ∈ F := by
    intro t ht
    obtain ⟨Q, hQ, hzQ⟩ := ht₀ t ht
    have hQV : R.isV Q := ConstructionAux.guess_isV hQ
    have hQz : R.lab Q ⊆ R.lab z := (isAnc_le Q z hzQ).2
    have hws := ConstructionAux.inputsUpTo_ne_nil w t
    rw [ConstructionAux.algGen_out]
    set ws := inputsUpTo w t
    set prev := algOutputs R C ws.dropLast
    set used : Set ℤ := {x | x ∈ ws ∨ x ∈ prev} with hused
    have hUfin : used.Finite :=
      (ws.finite_toSet.union prev.finite_toSet).subset fun x hx => hx
    unfold algStep
    rw [hQ]
    simp only
    rcases hf : (vdata R C Q).anc.find? (fun v => decide ((pod R C ws v \ {x | x ∈ ws ∨ x ∈ prev}).Nonempty)) with _ | v
    · left
      simp only
      have hne : (R.lab Q \ used).Nonempty :=
        ((hX.infinite _ (hlab Q hQV)).sdiff hUfin).nonempty
      exact hQz (hC.pick_spec _ _ hne).1
    · simp only
      have hvQ : IsAnc R C v Q := List.mem_of_find?_eq_some hf
      have hne' := List.find?_some hf
      simp only [decide_eq_true_eq] at hne'
      have hne : (pod R C ws v \ used).Nonempty := hne'
      have ho := (hC.pick_spec _ _ hne).1
      set o := C.pick (pod R C ws v) used
      set x := ws.getLastD 0 with hx
      have hxt : x = w t := inputsUpTo_getLastD w t
      set Hs := recordHistory R C ws v (boardOf R C v x) with hHs
      have hQH : Q ∈ Hs := mem_history hws hQ hvQ
      obtain ⟨hZ, hvZ, hmax⟩ := lca_spec hQH (fun y hy => history_anc hy)
      have ho1 : o ∈ boardOf R C v x := ho.1
      have ho2 : o ∈ R.lab (lca R C Hs) := ho.2
      by_cases hzZ : IsAnc R C z (lca R C Hs)
      · left; exact (isAnc_le _ _ hzZ).2 ho2
      · right
        have hall : ¬ ∀ y ∈ Hs, IsAnc R C z y := by
          intro h
          exact hzZ (isAnc_of_le Q z _ hzQ (hZ Q hQH) (hmax z h))
        push Not at hall
        obtain ⟨y, ⟨r, hr, hgy, hvy, hry⟩, hzy⟩ := hall
        have hrt : r ≤ t := by simp [ws, inputsUpTo] at hr; omega
        rw [BasicAux.inputsUpTo_take w hrt] at hgy
        rw [inputsUpTo_getD w hrt] at hry
        have hrt₀ : r < t₀ := by
          by_contra hge
          push Not at hge
          obtain ⟨y', hy', hzy'⟩ := ht₀ r hge
          rw [hgy] at hy'; cases hy'; exact hzy hzy'
        simp only [hF, mem_iUnion, mem_Iio, mem_ofPred_eq]
        refine ⟨r, hrt₀, y, hgy, v, hvy, (isAnc_le _ _ hvZ).2 ho2, ?_⟩
        exact (Set.ext_iff.1 (ConstructionAux.cutBoard_eq_of_mem hry) o).2 ho1
  have hinj : Function.Injective ((algGen R C).out w) := by
    have hadm := ConstructionAux.algGen_admissible hX hlab hC
    intro s t hst
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hadm w t).2 s h hst
    · exact (hadm w s).2 t h hst.symm
  refine ((finite_Iio t₀).union (hFf.preimage hinj.injOn)).subset fun t ht => ?_
  by_cases h : t < t₀
  · exact Or.inl h
  · rcases hkey t (not_lt.1 h) with h' | h'
    · exact absurd h' ht
    · exact Or.inr h'

end CaptureAux

/-- **Lemma 6.15** (`lem:memory`, history inclusion). On the round with inputs `ws`, with guess
`Q_t`, let `u ⪯ v` be active (ancestors of `Q_t`). If the updated record on `I_u(w_t)` lies in
the subtree rooted at `v`, then `L_{Z_{u, I_u(w_t)}} ⊆ L_{Z_{v, I_v(w_t)}}`. The hypothesis
`hε : 0 < ε` mirrors the paper's fixed `ε > 0` of Section 6.4; the Lean proof does not use it.
This is a standalone restatement of the paper's lemma: the density proof (`DensityAux.pod_sub`)
repeats the argument and does not use `lem_memory`. -/
theorem lem_memory {X : Set (Set ℤ)} (hX : LangClass X) {ε : ℝ} (hε : 0 < ε)
    {R : Requirements} (hR : IsFixedEpsSystem X ε R) {C : Choices} (hC : C.Valid X R)
    {ws : List ℤ} (hws : ws ≠ []) {Q u v : ℕ} (hQ : guess R ws = some Q)
    (huv : IsAnc R C u v) (hvQ : IsAnc R C v Q)
    (hZ : IsAnc R C v (record R C ws u (boardOf R C u (ws.getLastD 0)))) :
    R.lab (record R C ws u (boardOf R C u (ws.getLastD 0))) ⊆
      R.lab (record R C ws v (boardOf R C v (ws.getLastD 0))) := by
  have hQV : R.isV Q := ConstructionAux.guess_isV hQ
  have hvV : R.isV v := ConstructionAux.isV_of_anc R C Q hQV v hvQ
  set x := ws.getLastD 0
  have hQu : Q ∈ recordHistory R C ws u (boardOf R C u x) :=
    CaptureAux.mem_history hws hQ (CaptureAux.isAnc_trans Q u v huv hvQ)
  have hQv : Q ∈ recordHistory R C ws v (boardOf R C v x) := CaptureAux.mem_history hws hQ hvQ
  obtain ⟨hZu, -, hmaxu⟩ := CaptureAux.lca_spec hQu (fun y hy => CaptureAux.history_anc hy)
  obtain ⟨hZv, -, -⟩ := CaptureAux.lca_spec hQv (fun y hy => CaptureAux.history_anc hy)
  have hsub : recordHistory R C ws u (boardOf R C u x) ⊆
      recordHistory R C ws v (boardOf R C v x) := by
    rintro y hy
    obtain ⟨r, hr, hg, -, hin⟩ := id hy
    exact ⟨r, hr, hg, CaptureAux.isAnc_trans y v _ hZ (hZu y hy),
      CaptureAux.board_sub hX hR.lab_mem hR.N_pos hC hvV huv x hin⟩
  have hle := hmaxu _ (fun y hy => hZv y (hsub hy))
  have hanc := CaptureAux.isAnc_of_le Q _ _ (hZv Q hQv) (hZu Q hQu) hle
  exact (CaptureAux.isAnc_le _ _ hanc).2

/-- **Lemma 6.16** (`lem:capture`). Fix a full enumeration of `K = L_z`. There is a finite `t₀`
such that for every `t ≥ t₀` the guess `Q_t` is defined and lies in the subtree rooted at `z`.
The hypothesis `hε : 0 < ε` mirrors the paper's fixed `ε > 0` of Section 6.4; the Lean proof
does not use it (it is only passed on to `lem_forest_invariant`, where it is idle). -/
theorem lem_capture {X : Set (Set ℤ)} (hX : LangClass X) {ε : ℝ} (hε : 0 < ε)
    {R : Requirements} (hR : IsFixedEpsSystem X ε R) {C : Choices} (hC : C.Valid X R)
    {z : ℕ} (hz : R.isV z) {w : ℕ → ℤ} (hw : IsFullEnumeration w (R.lab z)) :
    ∃ t₀, ∀ t ≥ t₀, ∃ Q, guess R (inputsUpTo w t) = some Q ∧ IsAnc R C z Q := by
  obtain ⟨-, hPf, hPz, -⟩ := lem_forest_invariant hX hε hR hC hz
  exact CaptureAux.capture_of_P hz hw hPf hPz

/-- **Lemma 6.17** (`lem:validity`). On a full enumeration of `K = L_z`, the generator produces
only finitely many outputs outside `K`. The hypothesis `hε : 0 < ε` mirrors the paper's fixed
`ε > 0` of Section 6.4; the Lean proof does not use it (it is only passed on to `lem_capture`,
where it is idle). -/
theorem lem_validity {X : Set (Set ℤ)} (hX : LangClass X) {ε : ℝ} (hε : 0 < ε)
    {R : Requirements} (hR : IsFixedEpsSystem X ε R) {C : Choices} (hC : C.Valid X R)
    {z : ℕ} (hz : R.isV z) {w : ℕ → ℤ} (hw : IsFullEnumeration w (R.lab z)) :
    (algGen R C).AlmostAllIn w (R.lab z) := by
  obtain ⟨t₀, ht₀⟩ := lem_capture hX hε hR hC hz hw
  exact CaptureAux.validity_of_capture hX hR.lab_mem hR.N_pos hC ht₀

/-- **Lemma 6.21** (`lem:capture-fixed-copy`). Fix a full enumeration of `K` and `m ≥ 1`, and let
`z_m = (K, m)`. After some finite time every current guess `Q_t` is defined and lies in the
subtree rooted at `z_m`. -/
theorem lem_capture_fixed_copy {X : Set (Set ℤ)} (hX : LangClass X) {R : Requirements}
    {copy : ℕ → ℕ} (hR : IsCopySystem X R copy) {C : Choices} (hC : C.Valid X R)
    {z : ℕ} {w : ℕ → ℤ} (hw : IsFullEnumeration w (R.lab z)) :
    ∃ t₀, ∀ t ≥ t₀, ∃ Q, guess R (inputsUpTo w t) = some Q ∧ IsAnc R C z Q := by
  -- `P_z ⊆ L_z` by Lemma 6.20 (the next copy of `L_z` is a child of `z`, so `z` was a possible
  -- parent of it), and `P_z` is finite (`ForestAux.forest_invariant_copy`)
  obtain ⟨v, hv, hcv⟩ := hR.surj (R.lab z) (hR.lab_mem z) (copy z + 1) (by omega)
  have hp := (lem_copies_chain hX hR hC).1 z v hv.symm hcv
  have hPz : (vdata R C z).P ⊆ R.lab z := hv ▸ (CaptureAux.of_some hp).2.2.2.1
  exact CaptureAux.capture_of_P (hR.all z) hw (ForestAux.forest_invariant_copy hX hR hC z).2.1
    hPz

/-- For the formal-copy system (Section 6.8.6), all but finitely many outputs lie in `L_z`
(eventual validity together with `ConstructionAux.algGen_admissible`): Lemma 6.21 for the target
vertex `z` gives a capture time, and the validity argument of Lemma 6.17 applies verbatim. -/
theorem CaptureAux.validity_copy {X : Set (Set ℤ)} (hX : LangClass X) {R : Requirements}
    {copy : ℕ → ℕ} (hR : IsCopySystem X R copy) {C : Choices} (hC : C.Valid X R) {z : ℕ}
    {w : ℕ → ℤ} (hw : IsFullEnumeration w (R.lab z)) : (algGen R C).AlmostAllIn w (R.lab z) := by
  obtain ⟨t₀, ht₀⟩ := lem_capture_fixed_copy hX hR hC hw
  exact CaptureAux.validity_of_capture hX (fun v _ => hR.lab_mem v) (fun v _ => hR.N_pos v) hC ht₀

end BanachDensity1D
