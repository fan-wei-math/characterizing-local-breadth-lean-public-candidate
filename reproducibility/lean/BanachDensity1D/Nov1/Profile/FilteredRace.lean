import BanachDensity1D.Upper

/-! # The existing layer race with a prescribed family of witness windows.

Only the leaf window selection is generalized: the original race, freshness,
sealing, full-enumeration limit and eventual-validity attempt lemmas are reused.
This is needed to retain filter eligibility rather than using an ordinary-density upper bound.
-/

namespace BanachDensity1D.ProfileAux.FilteredRace
open Set Filter ChainsAux UpperAux

abbrev WindowPredicate := List (Set ℤ) → ℤ → ℤ → Prop

def Future (K : Set ℤ) (W : WindowPredicate) (Hpre : List (Set ℤ)) (T : LTree) : Prop :=
  ∀ P ∈ T.paths, ∀ U : Set ℤ, U.Finite → ∃ a b : ℤ,
    W (Hpre ++ P) a b ∧ Disjoint U (K ∩ Icc a b)

def Post (W : WindowPredicate) (G : Generator) (K : Set ℤ) (T : LTree)
    (Hpre : List (Set ℤ)) (h h' : List ℤ) : Prop :=
  ∃ P ∈ T.paths, ∃ a b : ℤ, W (Hpre ++ P) a b ∧
    Disjoint (used G h) (K ∩ Icc a b) ∧
    K ∩ Icc a b ∩ T.label ⊆ used G h' ∧
    used G h' ∩ (K ∩ Icc a b) ⊆ T.label ∧
    ((outs G h' ∩ (K ∩ Icc a b)).ncard : ℝ) ≤ (layerSum P (K ∩ Icc a b) : ℝ)

lemma Post_mono {W : WindowPredicate} {G : Generator} {K : Set ℤ} {T : LTree}
    {Hpre : List (Set ℤ)} (h r h' : List ℤ) (hp : Post W G K T Hpre (h ++ r) h') :
    Post W G K T Hpre h h' := by
  obtain ⟨P, hP, a, b, hW, hd, rest⟩ := hp
  exact ⟨P, hP, a, b, hW, hd.mono_left (used_mono G h r), rest⟩

lemma future_child {K : Set ℤ} {W : WindowPredicate} {Hpre : List (Set ℤ)}
    {L : Set ℤ} {c : ℕ → LTree} (hf : Future K W Hpre (.node L c)) (i : ℕ) :
    Future K W (Hpre ++ [L]) (c i) := by
  intro P hP U hU
  have h := hf (L :: P) ⟨i, P, hP, rfl⟩ U hU
  simpa only [List.append_assoc, List.singleton_append] using h

lemma leaf_attempt {W : WindowPredicate} {G : Generator} (hGa : G.Admissible)
    {K : Set ℤ} (L : Set ℤ) (Hpre : List (Set ℤ))
    (hfuture : Future K W Hpre (.leaf L)) (x : ℤ) (h : List ℤ) :
    ∃ r, (∀ y ∈ r, y ∈ L) ∧
      (Good G L h (h ++ x :: r) → Post W G K (.leaf L) Hpre h (h ++ x :: r)) := by
  set h1 := h ++ [x] with hh1
  have hpath : [L] ∈ (LTree.leaf L).paths := rfl
  obtain ⟨a, b, hwindow, hdisj1⟩ := hfuture [L] hpath (used G h1) (used_finite G h1)
  set J := K ∩ Icc a b with hJ
  have hJfin : J.Finite := (finite_Icc a b).subset inter_subset_right
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
  refine ⟨[L], hpath, a, b, hwindow, hdisj1.mono_left (used_mono G h [x]), ?_, hinL, ?_⟩
  · rintro y ⟨hyJ, hyL⟩
    exact hAu ⟨hyL, hyJ⟩
  · have hsub : outs G (h1 ++ r') ∩ J ⊆ outs G (h1 ++ r') ∩ (L ∩ J) := by
      rintro y ⟨hyO, hyJ⟩
      exact ⟨hyO, hinL ⟨Or.inr hyO, hyJ⟩, hyJ⟩
    have h1' := ncard_le_ncard hsub
      (hJfin.subset (inter_subset_right.trans inter_subset_right))
    have h2 : (outs G (h1 ++ r') ∩ J).ncard ≤ (L ∩ J).ncard / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]; omega
    simp only [layerSum, layers, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact_mod_cast h2

lemma node_attempt {W : WindowPredicate} {X : Set (Set ℤ)} {G : Generator}
    (hGa : G.Admissible) {K : Set ℤ} (L : Set ℤ) (c : ℕ → LTree)
    (hT : (LTree.node L c).Admissible X) (Hpre : List (Set ℤ))
    (ih : ∀ i, ∀ h, (∀ x ∈ h, x ∈ (c i).label) →
      ∃ r, (∀ x ∈ r, x ∈ (c i).label) ∧
        Post W G K (c i) (Hpre ++ [L]) h (h ++ r))
    (x : ℤ) (hx : x ∈ L) (h : List ℤ) :
    ∃ r, (∀ y ∈ r, y ∈ L) ∧
      ((∀ y ∈ h, y ∈ L) → Good G L h (h ++ x :: r) →
        Post W G K (LTree.node L c) Hpre h (h ++ x :: r)) := by
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
  obtain ⟨r1, hr1, P, hP, a, b, hwindow, hdisj, hJu, huJ, hcount⟩ :=
    ih i h1 (fun y hy => hi hy)
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
  refine ⟨L :: M :: Q, ⟨i, M :: Q, hP, rfl⟩, a, b, by simpa using hwindow,
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


/-- The original eventual-validity attempt mechanism, with the new window selector. -/
theorem mega {W : WindowPredicate} {X : Set (Set ℤ)} (hX : LangClass X)
    {G : Generator} (hGa : G.Admissible) (hG : G.EventuallyValidOn X) {K : Set ℤ} :
    ∀ T : LTree, T.Admissible X → T.label ∈ X → ∀ Hpre h,
      (∀ x ∈ h, x ∈ T.label) → Future K W Hpre T →
      ∃ r, (∀ x ∈ r, x ∈ T.label) ∧ Post W G K T Hpre h (h ++ r) := by
  intro T
  induction T with
  | leaf L =>
    intro _ hLX Hpre h hh hfuture
    obtain ⟨e, he⟩ := enum_of_mem hX hLX
    refine attempts hG hLX e he (fun h h' => Post W G K (.leaf L) Hpre h h')
      (fun h r h' hp => Post_mono h r h' hp) ?_ h hh
    intro k h
    obtain ⟨r, hr, hpost⟩ := leaf_attempt hGa L Hpre hfuture (e k) h
    exact ⟨r, hr, fun _ hgood => hpost hgood⟩
  | node L c ih =>
    intro hT hLX Hpre h hh hfuture
    obtain ⟨e, he⟩ := enum_of_mem hX hLX
    refine attempts hG hLX e he (fun h h' => Post W G K (.node L c) Hpre h h')
      (fun h r h' hp => Post_mono h r h' hp) ?_ h hh
    intro k h
    exact node_attempt hGa L c hT Hpre
      (fun i h hh => ih i (hT.1 i).2.2 (hT.1 i).1 (Hpre ++ [L]) h hh (future_child hfuture i))
      (e k) (show e k ∈ L by rw [show L = range e from he.symm]; exact mem_range_self k) h

end BanachDensity1D.ProfileAux.FilteredRace
