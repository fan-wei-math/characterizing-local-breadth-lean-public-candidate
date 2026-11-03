import BanachDensityHD.CharacterizationProofs
import BanachDensityHD.CharacterizationSuff

/-!
# Section 8.3–8.5: sufficiency, part 2

The static protected forest (§8.3.2): tree occurrences assigned to the vertices through the parent
scan, for the fixed-quota forest (strict scan, one vertex per language) and for the forest of
accuracy copies (nonstrict scan). The final lemmas give the sufficiency halves of Theorems 8.1 and
8.2 from the statement of the sewing lemma (Lemma 8.11), taken as a hypothesis.
-/

namespace BanachDensityHD

open Set Filter
open scoped Classical

namespace SuffAux

variable {d : ℕ}

open TreesAux (d0 dat dat_eq)

/-! ## Tree occurrences of the forest vertices -/

/-- The tree in which a path lives (indexed by its root's label and accuracy). -/
noncomputable def rt (Tf : Set (Pt d) → ℕ → DTree d) (l : List (Deco d)) : DTree d :=
  Tf (l.headD d0).L (l.headD d0).k

/-- The child occurrence labelled `(M, n)` of the path `l` (when it exists). -/
noncomputable def child (Tf : Set (Pt d) → ℕ → DTree d) (l : List (Deco d)) (M : Set (Pt d))
    (n : ℕ) : Deco d :=
  if h : ∃ w : Deco d, w.L = M ∧ w.k = n ∧ l ++ [w] ∈ (rt Tf l).paths then Classical.choose h
  else d0

/-- One step of the assignment of occurrences (§8.3.2): a root gets the root of the tree of its
copy, a non-root the child, labelled by its copy, of the occurrence of its parent. -/
noncomputable def occStep (strict : Bool) (lab : ℕ → Set (Pt d)) (acc : ℕ → ℕ)
    (Tf : Set (Pt d) → ℕ → DTree d) (j : ℕ) (f : ℕ → List (Deco d)) : List (Deco d) :=
  match scanParent strict lab (Pof f) j with
  | none => [(Tf (lab j) (acc j)).root]
  | some p => f p ++ [child Tf (f p) (lab j) (acc j)]

/-- The occurrences of the vertices. -/
noncomputable def occOf (strict : Bool) (lab : ℕ → Set (Pt d)) (acc : ℕ → ℕ)
    (Tf : Set (Pt d) → ℕ → DTree d) (j : ℕ) : List (Deco d) :=
  occStep strict lab acc Tf j (fun i => if i < j then occOf strict lab acc Tf i else [])
termination_by j
decreasing_by assumption

theorem scanParent_congr {strict : Bool} {lab P P' : ℕ → Set (Pt d)} {j : ℕ}
    (h : ∀ i < j, P i = P' i) : scanParent strict lab P j = scanParent strict lab P' j := by
  unfold scanParent
  refine List.foldl_ext _ _ _ fun a b hb => ?_
  have hb' : b < j := List.mem_range.1 hb
  have e : PossibleParent strict lab P b j ↔ PossibleParent strict lab P' b j := by
    unfold PossibleParent; rw [h b hb']
  by_cases hc : PossibleParent strict lab P b j
  · rw [if_pos hc, if_pos (e.1 hc)]
  · rw [if_neg hc, if_neg (fun h' => hc (e.2 h'))]

theorem occStep_congr {strict : Bool} {lab : ℕ → Set (Pt d)} {acc : ℕ → ℕ}
    {Tf : Set (Pt d) → ℕ → DTree d} {j : ℕ} {f g : ℕ → List (Deco d)} (h : ∀ i < j, f i = g i) :
    occStep strict lab acc Tf j f = occStep strict lab acc Tf j g := by
  unfold occStep
  have hs : scanParent strict lab (Pof f) j = scanParent strict lab (Pof g) j :=
    scanParent_congr fun i hi => by simp only [Pof, h i hi]
  rw [hs]
  rcases hp : scanParent strict lab (Pof g) j with _ | p
  · rfl
  · have := (scanParent_spec hp).1
    simp only [h p this]

theorem occOf_eq (strict : Bool) (lab : ℕ → Set (Pt d)) (acc : ℕ → ℕ)
    (Tf : Set (Pt d) → ℕ → DTree d) (j : ℕ) :
    occOf strict lab acc Tf j = occStep strict lab acc Tf j (occOf strict lab acc Tf) := by
  rw [occOf]
  exact occStep_congr fun i hi => by simp [hi]

/-- The hypotheses on a family of supplied trees, indexed by copies `(L, k)`. -/
structure TreeFam (strict : Bool) (N : ℕ∞) (lab : ℕ → Set (Pt d)) (acc : ℕ → ℕ)
    (Tf : Set (Pt d) → ℕ → DTree d) (h : ℕ → ℝ) (qd : Deco d → ℝ) : Prop where
  root : ∀ j : ℕ, (j : ℕ∞) < N →
    (Tf (lab j) (acc j)).root.L = lab j ∧ (Tf (lab j) (acc j)).root.k = acc j
  child : ∀ r j p : ℕ, (r : ℕ∞) < N → (j : ℕ∞) < N → p < j →
    (if strict then lab j ⊂ lab p else lab j ⊆ lab p) →
    ∀ l ∈ (Tf (lab r) (acc r)).paths, (lastOf l).L = lab p → (lastOf l).k = acc p →
      ↑(lastOf l).P ⊆ lab j →
      ∃ w : Deco d, w.L = lab j ∧ w.k = acc j ∧ l ++ [w] ∈ (Tf (lab r) (acc r)).paths
  path : ∀ r : ℕ, (r : ℕ∞) < N → ∀ l ∈ (Tf (lab r) (acc r)).paths, PathOK h qd l
  deco : ∀ r : ℕ, (r : ℕ∞) < N → ∀ l ∈ (Tf (lab r) (acc r)).paths, ∀ v ∈ l,
    ↑v.P ⊆ v.L ∧ 0 ≤ v.s
  inf : ∀ j : ℕ, (j : ℕ∞) < N → (lab j).Infinite
  inj : strict = true → ∀ i j : ℕ, (i : ℕ∞) < N → (j : ℕ∞) < N → lab i = lab j → i = j

/-- The forest datum of a tree family. -/
noncomputable def cfgOf (strict : Bool) (N : ℕ∞) (lab : ℕ → Set (Pt d)) (acc : ℕ → ℕ)
    (Tf : Set (Pt d) → ℕ → DTree d) (qd : Deco d → ℝ) (h : ℕ → ℝ) (Pb : Set (Rect d)) : Cfg d :=
  ⟨strict, N, lab, occOf strict lab acc Tf, qd, h, Pb⟩

section Occ
variable {strict : Bool} {N : ℕ∞} {lab : ℕ → Set (Pt d)} {acc : ℕ → ℕ}
  {Tf : Set (Pt d) → ℕ → DTree d} {h : ℕ → ℝ} {qd : Deco d → ℝ}

theorem paths_ne {T : DTree d} {l : List (Deco d)} (hl : l ∈ T.paths) : l ≠ [] := by
  intro he
  have := TreesAux.dtree_head T l hl
  rw [he] at this
  cases this

/-- The occurrence invariant: every vertex's occurrence is a path of the tree `Tf (lab r) (acc r)` of
some vertex `r < N`, ending with the vertex's copy. -/
theorem occ_inv (hT : TreeFam strict N lab acc Tf h qd) :
    ∀ j : ℕ, (j : ℕ∞) < N → ∃ r : ℕ, (r : ℕ∞) < N ∧
      occOf strict lab acc Tf j ∈ (Tf (lab r) (acc r)).paths ∧
      (lastOf (occOf strict lab acc Tf j)).L = lab j ∧
      (lastOf (occOf strict lab acc Tf j)).k = acc j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rw [occOf_eq]
    unfold occStep
    rcases hp : scanParent strict lab (Pof (occOf strict lab acc Tf)) j with _ | p
    · simp only
      obtain ⟨h1, h2⟩ := hT.root j hj
      exact ⟨j, hj, TreesAux.dtree_root_mem _, by simp [lastOf, h1], by simp [lastOf, h2]⟩
    · simp only
      have hpp := scanParent_spec hp
      have hpj : p < j := hpp.1
      have hpN : (p : ℕ∞) < N := lt_of_le_of_lt (by exact_mod_cast hpj.le) hj
      obtain ⟨r, hr, hin, hL, hk⟩ := ih p hpj hpN
      have hrt : rt Tf (occOf strict lab acc Tf p) = Tf (lab r) (acc r) := by
        have hh := TreesAux.dtree_head _ _ hin
        unfold rt
        rw [List.headD_eq_head?_getD, hh]
        simp only [Option.getD_some]
        rw [(hT.root r hr).1, (hT.root r hr).2]
      have hex := hT.child r j p hr hj hpj hpp.2.1 _ hin hL hk hpp.2.2
      have hex' : ∃ w : Deco d, w.L = lab j ∧ w.k = acc j ∧
          occOf strict lab acc Tf p ++ [w] ∈ (rt Tf (occOf strict lab acc Tf p)).paths := by
        rw [hrt]; exact hex
      have hc : child Tf (occOf strict lab acc Tf p) (lab j) (acc j) = Classical.choose hex' := by
        unfold child; rw [dif_pos hex']
      obtain ⟨c1, c2, c3⟩ := Classical.choose_spec hex'
      refine ⟨r, hr, ?_, ?_, ?_⟩
      · rw [hc, ← hrt]; exact c3
      · rw [lastOf_append, hc]; exact c1
      · rw [lastOf_append, hc]; exact c2

/-- Antitone labels from consecutive steps. -/
theorem anti_of_step (l : List (Deco d))
    (hstep : ∀ i, i + 1 < l.length → (dat l (i + 1)).L ⊆ (dat l i).L) :
    Antitone (fun i : Fin (l.length - 1 + 1) => (dat l i).L) := by
  have key : ∀ n i, i + n < l.length → (dat l (i + n)).L ⊆ (dat l i).L := by
    intro n
    induction n with
    | zero => intro i _; exact subset_rfl
    | succ n ih =>
      intro i hi
      exact (hstep (i + n) (by omega)).trans (ih i (by omega))
  intro a b hab
  simp only
  rcases Nat.eq_zero_or_pos l.length with h0 | hpos
  · have ha : a.val = 0 := by have := a.isLt; omega
    have hb : b.val = 0 := by have := b.isLt; omega
    rw [ha, hb]
  · have := key (b.val - a.val) a.val (by have := b.isLt; omega)
    rwa [show a.val + (b.val - a.val) = b.val by have : a.val ≤ b.val := hab; omega] at this

/-- Consecutive decorations of a tree path are an edge of the tree. -/
theorem tree_edge {T : DTree d} {l : List (Deco d)} (hl : l ∈ T.paths) (i : ℕ)
    (hi : i + 1 < l.length) : l.take i ++ [dat l i, dat l (i + 1)] ∈ T.paths := by
  have h := TreesAux.dtree_prefix T l hl (i + 1 + 1) (by omega)
  have e : l.take (i + 1 + 1) = l.take i ++ [dat l i, dat l (i + 1)] := by
    rw [← List.take_concat_get' l (i + 1) hi,
      ← List.take_concat_get' l i (by omega), dat_eq (q := l) (j := i) (by omega), dat_eq hi]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  rwa [e] at h

/-- The pathFn of the library is `dat`. -/
theorem pathFn_eq {β : Type*} (f : Deco d → β) (l : List (Deco d)) (hl : l ≠ []) :
    pathFn f l hl = fun i : Fin (l.length - 1 + 1) => f (dat l i) := by
  funext i
  simp only [pathFn]
  rw [dat_eq (q := l) (j := i.val) (by have := i.isLt; have := List.length_pos_iff.mpr hl; omega)]
  rfl

/-- **The forest datum of a tree family is good.** -/
theorem cfgOf_good (hT : TreeFam strict N lab acc Tf h qd) (Pb : Set (Rect d)) :
    (cfgOf strict N lab acc Tf qd h Pb).Good := by
  have hinv := occ_inv hT
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun j hj p hp => ?_, fun i hi p hp hpre => ?_,
    fun i hi => ?_, hT.inf, hT.inj⟩
  · obtain ⟨r, -, hin, -⟩ := hinv i hi
    exact paths_ne hin
  · exact (hinv i hi).choose_spec.2.2.1
  · refine ⟨child Tf (occOf strict lab acc Tf p) (lab j) (acc j), ?_⟩
    show occOf strict lab acc Tf j = _
    rw [occOf_eq]
    unfold occStep
    have hp' : scanParent strict lab (Pof (occOf strict lab acc Tf)) j = some p := hp
    rw [hp']
    rfl
  · obtain ⟨r, hr, hin, -⟩ := hinv i hi
    obtain ⟨n, rfl⟩ : ∃ n, p = (occOf strict lab acc Tf i).take n :=
      ⟨p.length, List.prefix_iff_eq_take.1 hpre⟩
    have hn : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; simp at hp
      · exact h0
    exact hT.path r hr _ (TreesAux.dtree_prefix _ _ hin n hn)
  · obtain ⟨r, hr, hin, hL, -⟩ := hinv i hi
    have hne := paths_ne hin
    have hmem : lastOf (occOf strict lab acc Tf i) ∈ occOf strict lab acc Tf i := by
      rw [lastOf, CharAux.getLastD_eq_getLast _ _ hne]
      exact List.getLast_mem hne
    have := (hT.deco r hr _ hin _ hmem).1
    show ↑(lastOf (occOf strict lab acc Tf i)).P ⊆ lab i
    rw [← hL]; exact this

/-- The last decoration of an occurrence has a nonnegative cutoff. -/
theorem last_s_nonneg (hT : TreeFam strict N lab acc Tf h qd) {i : ℕ} (hi : (i : ℕ∞) < N) :
    0 ≤ (lastOf (occOf strict lab acc Tf i)).s := by
  obtain ⟨r, hr, hin, -⟩ := occ_inv hT i hi
  have hne := paths_ne hin
  have hmem : lastOf (occOf strict lab acc Tf i) ∈ occOf strict lab acc Tf i := by
    rw [lastOf, CharAux.getLastD_eq_getLast _ _ hne]
    exact List.getLast_mem hne
  exact (hT.deco r hr _ hin _ hmem).2

end Occ

/-! ## The sewing hypothesis and the threshold -/

/-- The statement of Lemma 8.11 (`lem_sewing`), as a hypothesis in its intended domain `d ≥ 2`.
The definition is total in `d` but is false at `d = 0`: the unique board point contributes
`log 3 > 0` while the coefficient is zero. `lem_sewing` proves the admissible-dimensional cases. 
-/
def SewingStatement (d : ℕ) : Prop :=
  ∃ Pb : Set (Rect d),
    (∀ C ∈ Pb, ∀ C' ∈ Pb, C ≠ C' → Disjoint C.pts C'.pts) ∧ (∀ x : Pt d, ∃ C ∈ Pb, x ∈ C.pts) ∧
    ∀ R : Rect d, {C ∈ Pb | (C.pts ∩ R.pts).Nonempty}.Finite ∧
      (∑ᶠ C ∈ {C ∈ Pb | (C.pts ∩ R.pts).Nonempty}, Real.log (2 + (C.pts ∩ R.pts).ncard)) ≤
        (12 * d ^ 2 + 4 * d) * Real.log (2 + R.vol) ∧
      ∀ g : ℝ → ℝ, (∀ x, 1 ≤ x → 1 ≤ g x) → MonotoneOn g (Ici 1) →
        (∑ᶠ C ∈ {C ∈ Pb | (C.pts ∩ R.pts).Nonempty}, hLog g (C.pts ∩ R.pts).ncard) ≤
          (12 * d ^ 2 + 4 * d) * hLog g R.vol

theorem sew_of_statement {g : ℝ → ℝ} (hg1 : ∀ x, 1 ≤ x → 1 ≤ g x) (hgm : MonotoneOn g (Ici 1))
    (hsew : SewingStatement d) :
    ∃ Pb : Set (Rect d), Sew Pb (hLog g) (12 * d ^ 2 + 4 * d) := by
  obtain ⟨Pb, h1, h2, h3⟩ := hsew
  exact ⟨Pb, ⟨h1, h2, fun R => (h3 R).1, fun R => (h3 R).2.2 g hg1 hgm⟩⟩

theorem hLog_ge {g : ℝ → ℝ} (hg1 : ∀ x, 1 ≤ x → 1 ≤ g x) (n : ℕ) (hn : 1 ≤ n) :
    Real.log 3 ≤ hLog g n := by
  unfold hLog
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hg := hg1 n h1
  have hl : Real.log 3 ≤ Real.log (2 + n) := Real.log_le_log (by norm_num) (by linarith)
  have hl0 : 0 ≤ Real.log (2 + n) := Real.log_nonneg (by linarith)
  nlinarith


/-! ## The fixed-quota forest (Theorem 8.1(1)) -/

/-- An injective enumeration of a `LangClass` family by vertices `i < N`. The hypothesis
includes countability, nonemptiness and infinitude of each member; no generalization to
arbitrary countable nonempty families is asserted by this declaration. -/
theorem enum_inj {X : Set (Set (Pt d))} (hX : LangClass X) :
    ∃ (N : ℕ∞) (lab : ℕ → Set (Pt d)),
      (∀ i j : ℕ, (i : ℕ∞) < N → (j : ℕ∞) < N → lab i = lab j → i = j) ∧
      ∀ L, L ∈ X ↔ ∃ i : ℕ, (i : ℕ∞) < N ∧ lab i = L := by
  by_cases hfin : X.Finite
  · set l := hfin.toFinset.toList with hl
    have hnd : l.Nodup := Finset.nodup_toList _
    refine ⟨l.length, fun i => l.getD i ∅, ?_, ?_⟩
    · intro i j hi hj he
      have hi' : i < l.length := by exact_mod_cast hi
      have hj' : j < l.length := by exact_mod_cast hj
      simp only [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hj'] at he
      exact (hnd.getElem_inj_iff).1 he
    · intro L
      constructor
      · intro hL
        have hmem : L ∈ l := by rw [hl, Finset.mem_toList]; exact hfin.mem_toFinset.2 hL
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
        exact ⟨i, by exact_mod_cast hi, List.getD_eq_getElem _ _ hi⟩
      · rintro ⟨i, hi, rfl⟩
        have hi' : i < l.length := by exact_mod_cast hi
        simp only [List.getD_eq_getElem _ _ hi']
        have hmem : l[i] ∈ hfin.toFinset.toList := List.getElem_mem hi'
        exact hfin.mem_toFinset.1 (Finset.mem_toList.1 hmem)
  · have h1 : Infinite X := Set.infinite_coe_iff.2 hfin
    have h2 : Countable X := hX.countable.to_subtype
    obtain ⟨D⟩ := nonempty_denumerable_iff.2 ⟨h2, h1⟩
    let e : ℕ ≃ X := (Denumerable.eqv X).symm
    refine ⟨⊤, fun i => (e i).1, fun i j _ _ he => e.injective (Subtype.ext he), fun L => ⟨?_, ?_⟩⟩
    · intro hL
      exact ⟨e.symm ⟨L, hL⟩, ENat.coe_lt_top _, by simp⟩
    · rintro ⟨i, -, rfl⟩
      exact (e i).2

/-- The tree family of the fixed-quota forest. -/
theorem fixed_treeFam {X : Set (Set (Pt d))} (hX : LangClass X) {h : ℕ → ℝ}
    {q : Set (Pt d) → ℝ} (Tf : Set (Pt d) → ℕ → DTree d)
    (hTf : ∀ K ∈ X, ∀ k, IsProtectedTree X h q K (Tf K k)) {N : ℕ∞} {lab : ℕ → Set (Pt d)}
    (hinj : ∀ i j : ℕ, (i : ℕ∞) < N → (j : ℕ∞) < N → lab i = lab j → i = j)
    (hlab : ∀ j : ℕ, (j : ℕ∞) < N → lab j ∈ X) :
    TreeFam true N lab (fun _ => 1) Tf h (fun v => q v.L) := by
  refine ⟨fun j hj => ?_, fun r j p hr hj hpj hrel l hl hL hk hP => ?_, fun r hr l hl => ?_,
    fun r hr l hl v hv => ?_, fun j hj => hX.infinite _ (hlab j hj), fun _ => hinj⟩
  · have hT := hTf (lab j) (hlab j hj) 1
    exact ⟨hT.1, (hT.2.1 _ (TreesAux.dtree_root_mem _) _ (List.mem_singleton_self _)).2.2.2.2⟩
  · have hT := hTf (lab r) (hlab r hr) 1
    have hne := paths_ne hl
    simp only [if_true] at hrel
    have hlast : l.getLast hne = lastOf l := (CharAux.getLastD_eq_getLast _ _ hne).symm
    obtain ⟨w, hwL, hw⟩ := hT.2.2.2.1 l hl hne (lab j) (hlab j hj) (by rw [hlast]; exact hP)
      (by rw [hlast, hL]; exact hrel)
    refine ⟨w, hwL, ?_, hw⟩
    exact (hT.2.1 _ hw w (List.mem_append_right _ (List.mem_singleton_self _))).2.2.2.2
  · have hT := hTf (lab r) (hlab r hr) 1
    have hne := paths_ne hl
    refine ⟨hne, anti_of_step l fun i hi => ?_, ?_⟩
    · exact (hT.2.2.1 _ _ _ (tree_edge hl i hi)).1.subset
    · have := hT.2.2.2.2 l hl hne
      simp only [pathFn_eq] at this
      rw [← CharAux.getLastD_eq_getLast _ d0 hne] at this
      exact this
  · have := (hTf (lab r) (hlab r hr) 1).2.1 l hl v hv
    exact ⟨this.2.1, by linarith [this.2.2.1]⟩

/-- **Theorem 8.1(1), sufficiency, from the sewing lemma.** -/
theorem fixed_quota_suff_of_sewing {d : ℕ} (hd : 2 ≤ d) {X : Set (Set (Pt d))}
    (hX : LangClass X) {g : ℝ → ℝ} (hg1 : ∀ x, 1 ≤ x → 1 ≤ g x) (hgm : MonotoneOn g (Ici 1))
    (q : Set (Pt d) → ℝ) (hq : ∀ K ∈ X, q K ∈ Icc (0 : ℝ) 1)
    (htree : ∀ K ∈ X, ∃ T, IsProtectedTree X (hLog g) q K T) (hsew : SewingStatement d) :
    ∃ G ∈ ValidGen X, ∀ K ∈ X, Guarantees (dH (hLog g)) G K (q K) := by
  obtain ⟨Pb, hs⟩ := sew_of_statement hg1 hgm hsew
  obtain ⟨N, lab, hinj, hrange⟩ := enum_inj hX
  have hlab : ∀ j : ℕ, (j : ℕ∞) < N → lab j ∈ X := fun j hj => (hrange _).2 ⟨j, hj, rfl⟩
  obtain ⟨K0, hK0⟩ := hX.nonempty
  let Tf : Set (Pt d) → ℕ → DTree d := fun K _ =>
    if hK : K ∈ X then Classical.choose (htree K hK) else Classical.choose (htree K0 hK0)
  have hTf : ∀ K ∈ X, ∀ k, IsProtectedTree X (hLog g) q K (Tf K k) := by
    intro K hK k
    simp only [Tf, dif_pos hK]
    exact Classical.choose_spec (htree K hK)
  have hTF := fixed_treeFam hX Tf hTf hinj hlab
  set c := cfgOf true N lab (fun _ => 1) Tf (fun v => q v.L) (hLog g) Pb with hcdef
  have hc : c.Good := cfgOf_good hTF Pb
  have hd1 : 1 ≤ d := by omega
  have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have key : ∀ z : ℕ, (z : ℕ∞) < N → ∀ w, IsFullEnumeration w (lab z) →
      c.gen.EventuallyValid w (lab z) ∧ q (lab z) ≤ deltaH (hLog g) (c.gen.outputSet w) (lab z) := by
    intro z hz w hw
    obtain ⟨r, -, -, hL, -⟩ := occ_inv hTF z hz
    have hqz : c.qd (lastOf (c.occ z)) = q (lab z) := by
      show q (lastOf (occOf true lab (fun _ => 1) Tf z)).L = _
      rw [hL]
    have hqI := hq (lab z) (hlab z hz)
    have := Cfg.gen_works hd1 hc hs h3 (hLog_ge hg1) hz hw (by rw [hqz]; exact hqI.2)
      (last_s_nonneg hTF hz)
    rw [hqz] at this
    exact this
  refine ⟨c.gen, ⟨c.gen_fresh hd1 hc, fun K hK w hw => ?_⟩, fun K hK w hw => ?_⟩
  · obtain ⟨z, hz, rfl⟩ := (hrange K).1 hK
    exact (key z hz w hw).1
  · obtain ⟨z, hz, rfl⟩ := (hrange K).1 hK
    exact EReal.coe_le_coe_iff.2 (key z hz w hw).2

/-! ## The forest of accuracy copies (Theorem 8.2) -/

/-- The tree family of the copy forest for an arbitrary labeling `lab`: vertex `j` is
the copy `(lab j, j + 1)`. The later enumeration application specializes `lab` using
`e (unpair j).1`; that specialization is not assumed here. -/
theorem copy_treeFam {X : Set (Set (Pt d))} (hX : LangClass X) {h : ℕ → ℝ}
    {α : Set (Pt d) → ℝ} (Tf : Set (Pt d) → ℕ → DTree d)
    (hTf : ∀ K ∈ X, ∀ k, 1 ≤ k → IsCopyProtectedTree X h α K k (Tf K k)) {lab : ℕ → Set (Pt d)}
    (hlab : ∀ j, lab j ∈ X) :
    TreeFam false ⊤ lab (fun j => j + 1) Tf h (fun v => copyQuota α v.L v.k) := by
  refine ⟨fun j _ => ?_, fun r j p _ _ hpj hrel l hl hL hk hP => ?_, fun r _ l hl => ?_,
    fun r _ l hl v hv => ?_, fun j _ => hX.infinite _ (hlab j), fun h => absurd h (by simp)⟩
  · have hT := hTf (lab j) (hlab j) (j + 1) (by omega)
    exact ⟨hT.1, hT.2.1⟩
  · have hT := hTf (lab r) (hlab r) (r + 1) (by omega)
    have hne := paths_ne hl
    simp only [Bool.false_eq_true, if_false] at hrel
    have hlast : l.getLast hne = lastOf l := (CharAux.getLastD_eq_getLast _ _ hne).symm
    have hcomp : CompatibleCopy (↑(l.getLast hne).P) (l.getLast hne).L (l.getLast hne).k
        (lab j) (j + 1) := by
      rw [hlast, hL, hk]
      refine ⟨by omega, hP, hrel, ?_⟩
      by_cases he : lab j = lab p
      · exact Or.inr ⟨he, by omega⟩
      · exact Or.inl (ssubset_of_subset_of_ne hrel he)
    exact hT.2.2.2.2.1 l hl hne (lab j) (hlab j) (j + 1) hcomp
  · have hT := hTf (lab r) (hlab r) (r + 1) (by omega)
    have hne := paths_ne hl
    refine ⟨hne, anti_of_step l fun i hi => ?_, ?_⟩
    · exact (hT.2.2.2.1 _ _ _ (tree_edge hl i hi)).1.2.2.1
    · have := hT.2.2.2.2.2 l hl hne
      simp only [pathFn_eq] at this
      rw [← CharAux.getLastD_eq_getLast _ d0 hne] at this
      exact this
  · have := (hTf (lab r) (hlab r) (r + 1) (by omega)).2.2.1 l hl v hv
    exact ⟨this.2.1, by linarith [this.2.2.1]⟩

/-- **Theorem 8.2, sufficiency (monotone copy relation), from the sewing lemma.** -/
theorem main_suff_of_sewing {d : ℕ} (hd : 2 ≤ d) {X : Set (Set (Pt d))} (hX : LangClass X)
    {g : ℝ → ℝ} (hg1 : ∀ x, 1 ≤ x → 1 ≤ g x) (hgm : MonotoneOn g (Ici 1))
    (α : Set (Pt d) → ℝ) (hα : ∀ K ∈ X, α K ∈ Icc (0 : ℝ) 1)
    (htree : ∀ K ∈ X, ∀ k : ℕ, 1 ≤ k → ∃ T, IsCopyProtectedTree X (hLog g) α K k T)
    (hsew : SewingStatement d) : Achievable (hLog g) X α := by
  obtain ⟨Pb, hs⟩ := sew_of_statement hg1 hgm hsew
  obtain ⟨e, he⟩ := hX.countable.exists_eq_range hX.nonempty
  let lab : ℕ → Set (Pt d) := fun j => e (Nat.unpair j).1
  have hlab : ∀ j, lab j ∈ X := fun j => by rw [he]; exact ⟨_, rfl⟩
  obtain ⟨K0, hK0⟩ := hX.nonempty
  let Tf : Set (Pt d) → ℕ → DTree d := fun K k =>
    if hK : K ∈ X ∧ 1 ≤ k then Classical.choose (htree K hK.1 k hK.2)
    else Classical.choose (htree K0 hK0 1 le_rfl)
  have hTf : ∀ K ∈ X, ∀ k, 1 ≤ k → IsCopyProtectedTree X (hLog g) α K k (Tf K k) := by
    intro K hK k hk
    simp only [Tf, dif_pos (And.intro hK hk)]
    exact Classical.choose_spec (htree K hK k hk)
  have hTF := copy_treeFam hX Tf hTf hlab
  set c := cfgOf false ⊤ lab (fun j => j + 1) Tf (fun v => copyQuota α v.L v.k) (hLog g) Pb
    with hcdef
  have hc : c.Good := cfgOf_good hTF Pb
  have hd1 : 1 ≤ d := by omega
  have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have key : ∀ z : ℕ, ∀ w, IsFullEnumeration w (lab z) →
      c.gen.EventuallyValid w (lab z) ∧
        copyQuota α (lab z) (z + 1) ≤ deltaH (hLog g) (c.gen.outputSet w) (lab z) := by
    intro z w hw
    have hz : (z : ℕ∞) < ⊤ := ENat.coe_lt_top z
    obtain ⟨r, -, -, hL, hk⟩ := occ_inv hTF z hz
    have hqz : c.qd (lastOf (c.occ z)) = copyQuota α (lab z) (z + 1) := by
      show copyQuota α (lastOf (occOf false lab (fun j => j + 1) Tf z)).L
        (lastOf (occOf false lab (fun j => j + 1) Tf z)).k = _
      rw [hL, hk]
    have hαz := hα (lab z) (hlab z)
    have hq1 : copyQuota α (lab z) (z + 1) ≤ 1 := by
      refine max_le ?_ zero_le_one
      have : (0 : ℝ) ≤ 1 / ((z + 1 : ℕ) : ℝ) := by positivity
      linarith [hαz.2]
    have := Cfg.gen_works hd1 hc hs h3 (hLog_ge hg1) hz hw (by rw [hqz]; exact hq1)
      (last_s_nonneg hTF hz)
    rw [hqz] at this
    exact this
  refine ⟨c.gen, ⟨c.gen_fresh hd1 hc, fun K hK w hw => ?_⟩, fun K hK w hw => ?_⟩
  · rw [he] at hK
    obtain ⟨a, rfl⟩ := hK
    have hlz : lab (Nat.pair a 0) = e a := by simp [lab]
    rw [← hlz] at hw ⊢
    exact (key _ w hw).1
  · rw [he] at hK
    obtain ⟨a, rfl⟩ := hK
    refine EReal.coe_le_coe_iff.2 ?_
    have hall : ∀ n : ℕ, α (e a) - 1 / ((n : ℝ) + 1) ≤
        deltaH (hLog g) (c.gen.outputSet w) (e a) := by
      intro n
      have hlz : lab (Nat.pair a n) = e a := by simp [lab]
      have h1 := (key (Nat.pair a n) w (by rw [hlz]; exact hw)).2
      rw [hlz] at h1
      have h2 : α (e a) - 1 / ((Nat.pair a n + 1 : ℕ) : ℝ) ≤ copyQuota α (e a) (Nat.pair a n + 1) :=
        le_max_left _ _
      have h3 : 1 / ((Nat.pair a n + 1 : ℕ) : ℝ) ≤ 1 / ((n : ℝ) + 1) := by
        have hle : (n : ℝ) + 1 ≤ ((Nat.pair a n + 1 : ℕ) : ℝ) := by
          push_cast
          have := Nat.right_le_pair a n
          exact_mod_cast Nat.add_le_add_right this 1
        exact one_div_le_one_div_of_le (by positivity) hle
      linarith
    by_contra hlt
    push Not at hlt
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
    have := hall n
    linarith

end SuffAux

end BanachDensityHD
