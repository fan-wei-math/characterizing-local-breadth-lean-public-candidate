import BanachDensity1D.HistoryTopology

/-!
# Sections 6.4–6.8: the static protected forest and the online algorithm

Kleinberg–Wei, Part *Dimension one*, Sections 6.4 (static protected forest), 6.5 (online
algorithm), 6.6 (validity), 6.7 (local density) and 6.8 (formal copies).

The construction is written once, for a countable list of *vertices* `0, 1, 2, …` (an initial
segment of `ℕ`) carrying a language label `L_v`, a scale `N_v` and thresholds `s_v`, `q_v`
(`Requirements`). Two instances are used:

* `IsFixedEpsSystem X ε`: the vertices are the distinct languages of `X` (Section 6.4), with
  `q_i = (b(L_i) - ε)_+`, `s_i = (b(L_i) - ε/2)_+` and `N_i` as in (18);
* `IsCopySystem X`: the vertices are the formal copies `(L, m)`, `m ≥ 1` (Section 6.8), with
  `q = (b(L) - 2^{-m})_+`, `s = (b(L) - 2^{-m-1})_+`.

The parent rule is written with non-strict inclusion (Section 6.8). For the fixed-`ε` system the
labels of distinct vertices are distinct, so `L_v ⊆ L_u` with `u < v` is the strict inclusion of
(20), and a forest path never repeats a label, so the compressed chain `H̄[a,v]` of Section 6.8
is the chain `H[a,v]` of Section 6.4.

The paper leaves several choices free: the protected sets `Prot_a(H)`, the board partitions of
Lemma 6.12, and the tie-breaking rules of the algorithm. They are the fields of `Choices`; the
statements below hold for every choice satisfying `Choices.Valid`: the properties the paper
requires of them, except that `prot_spec` asks for protected sets for every safe list, a stronger
requirement than the paper's (see the docstring of `Choices.Valid`).

Boards: a partition of `ℤ` into consecutive intervals is given by its set `C` of cut points
(`c ∈ C` separates `c` from `c + 1`); `cutBoard C x` is the board containing `x`. A partition
`C'` coarsens `C` (every `C'`-board is a union of consecutive `C`-boards) iff `C' ⊆ C`.

Records: the paper defines the record `Z_{v,I}` by the update rule (23) and states that after
round `t` it is the LCA of the history `𝓗^t_{v,I}` (Section 6.5). The algorithm below uses that
closed form directly.
-/

namespace BanachDensity1D

open Set Filter Classical

/-! ## Boards -/

/-- The board of the partition with cut points `C` that contains `x`: all `y` such that no cut
lies between `x` and `y`. -/
def cutBoard (C : Set ℤ) (x : ℤ) : Set ℤ := {y | ∀ c ∈ C, ¬ (min x y ≤ c ∧ c < max x y)}

namespace ConstructionAux

/-- Every point lies in its own board. -/
lemma mem_cutBoard_self (C : Set ℤ) (x : ℤ) : x ∈ cutBoard C x := by
  intro c _ ⟨h1, h2⟩
  rw [min_self] at h1; rw [max_self] at h2; omega

/-- Boards of a coarser partition (fewer cuts) are larger. -/
lemma cutBoard_mono {C₁ C₂ : Set ℤ} (h : C₁ ⊆ C₂) (x : ℤ) : cutBoard C₂ x ⊆ cutBoard C₁ x :=
  fun _ hy c hc => hy c (h hc)

/-- Boards are equivalence classes: symmetry. -/
lemma cutBoard_symm {C : Set ℤ} {x y : ℤ} (h : y ∈ cutBoard C x) : x ∈ cutBoard C y := by
  intro c hc; rw [min_comm, max_comm]; exact h c hc

/-- Boards are equivalence classes: a point of a board has that board as its own. -/
lemma cutBoard_eq_of_mem {C : Set ℤ} {x y : ℤ} (h : y ∈ cutBoard C x) :
    cutBoard C y = cutBoard C x := by
  have key : ∀ x y, y ∈ cutBoard C x → cutBoard C y ⊆ cutBoard C x := by
    intro x y h z hz c hc hcz
    have h1 := h c hc
    have h2 := hz c hc
    simp only [min_le_iff, lt_max_iff] at h1 h2 hcz
    omega
  exact Subset.antisymm (key x y h) (key y x (cutBoard_symm h))

/-- The board between two consecutive cuts `a < b`. -/
lemma cutBoard_eq_Ioc {C : Set ℤ} {a b x : ℤ} (ha : a ∈ C) (hb : b ∈ C) (hax : a < x)
    (hxb : x ≤ b) (hno : ∀ c ∈ C, a < c → c < b → False) : cutBoard C x = Ioc a b := by
  ext y
  simp only [cutBoard, mem_ofPred_eq, mem_Ioc]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra hy; push Not at hy
      exact h a ha ⟨by rw [min_le_iff]; right; exact hy, by rw [lt_max_iff]; left; exact hax⟩
    · by_contra hy; push Not at hy
      exact h b hb ⟨by rw [min_le_iff]; left; exact hxb, by rw [lt_max_iff]; right; exact hy⟩
  · rintro ⟨hy1, hy2⟩ c hc ⟨h1, h2⟩
    have h1' : a < c := by rcases min_choice x y with hm | hm <;> rw [hm] at h1 <;> omega
    have h2' : c < b := by rcases max_choice x y with hm | hm <;> rw [hm] at h2 <;> omega
    exact hno c hc h1' h2'

/-- The board below the least cut `b`. -/
lemma cutBoard_eq_Iic {C : Set ℤ} {b x : ℤ} (hb : b ∈ C) (hxb : x ≤ b)
    (hno : ∀ c ∈ C, c < b → False) : cutBoard C x = Iic b := by
  ext y
  simp only [cutBoard, mem_ofPred_eq, mem_Iic]
  constructor
  · intro h
    by_contra hy; push Not at hy
    exact h b hb ⟨by rw [min_le_iff]; left; exact hxb, by rw [lt_max_iff]; right; exact hy⟩
  · intro hy c hc ⟨h1, h2⟩
    have h2' : c < b := by rcases max_choice x y with hm | hm <;> rw [hm] at h2 <;> omega
    exact hno c hc h2'

/-- The board above the greatest cut `a`. -/
lemma cutBoard_eq_Ioi {C : Set ℤ} {a x : ℤ} (ha : a ∈ C) (hax : a < x)
    (hno : ∀ c ∈ C, a < c → False) : cutBoard C x = Ioi a := by
  ext y
  simp only [cutBoard, mem_ofPred_eq, mem_Ioi]
  constructor
  · intro h
    by_contra hy; push Not at hy
    exact h a ha ⟨by rw [min_le_iff]; right; exact hy, by rw [lt_max_iff]; left; exact hax⟩
  · intro hy c hc ⟨h1, h2⟩
    have h1' : a < c := by rcases min_choice x y with hm | hm <;> rw [hm] at h1 <;> omega
    exact hno c hc h1'

/-- An interval `(p, n]` with no cut in `(p, n)` lies in the board of `n`. -/
lemma Ioc_subset_cutBoard {C : Set ℤ} {p n : ℤ} (h : ∀ d ∈ C, p < d → d < n → False) :
    Ioc p n ⊆ cutBoard C n := by
  rintro y ⟨hy1, hy2⟩ d hd ⟨h1, h2⟩
  rw [min_eq_right hy2] at h1; rw [max_eq_left hy2] at h2
  exact h d hd (by omega) h2

/-- Additivity of the `L`-count over adjacent intervals. -/
lemma ncard_inter_Ioc_add (L : Set ℤ) {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    (L ∩ Ioc a c).ncard = (L ∩ Ioc a b).ncard + (L ∩ Ioc b c).ncard := by
  rw [← Ioc_union_Ioc_eq_Ioc hab hbc, inter_union_distrib_left]
  refine ncard_union_eq ?_ ((finite_Ioc a b).inter_of_right L) ((finite_Ioc b c).inter_of_right L)
  rw [Set.disjoint_left]
  rintro z ⟨-, -, hz⟩ ⟨-, hz', -⟩
  omega

section Child

variable {Lu Lv Cu : Set ℤ} {Bu N : ℕ}

/-- A piece of a `u`-board meets `L_v` in at most `B_u` points. -/
lemma ncard_piece_le (hsub : Lv ⊆ Lu)
    (hCu : ∀ x, (Lu ∩ cutBoard Cu x).Finite ∧ (Lu ∩ cutBoard Cu x).ncard ≤ Bu)
    {S : Set ℤ} {x : ℤ} (hS : S ⊆ cutBoard Cu x) : (Lv ∩ S).ncard ≤ Bu :=
  (ncard_le_ncard (inter_subset_inter hsub hS) (hCu x).1).trans (hCu x).2

/-- One step of the greedy grouping, to the right of `c`. -/
lemma up_step (hsub : Lv ⊆ Lu) (hN : 1 ≤ N)
    (hCu : ∀ x, (Lu ∩ cutBoard Cu x).Finite ∧ (Lu ∩ cutBoard Cu x).ncard ≤ Bu)
    (c : ℤ) (hinf : (Lv ∩ Ioi c).Infinite) :
    ∃ d ∈ Cu, c < d ∧ N ≤ (Lv ∩ Ioc c d).ncard ∧ (Lv ∩ Ioc c d).ncard ≤ N + Bu - 1 := by
  obtain ⟨t, ht, htc⟩ := hinf.exists_subset_card_eq N
  have hne : t.Nonempty := Finset.card_pos.1 (by omega)
  set y := t.max' hne
  have hyt : y ∈ t := t.max'_mem hne
  have hcy : c < y := (ht hyt).2
  have hcut : ∃ d ∈ Cu, y ≤ d := by
    by_contra hno
    push Not at hno
    have hsubB : Ici y ⊆ cutBoard Cu y := by
      rintro z hz d hd ⟨h1, -⟩
      rw [min_eq_left (show y ≤ z from hz)] at h1
      exact absurd h1 (not_le.2 (hno d hd))
    have hfin : (Lv ∩ Ici y).Finite :=
      (hCu y).1.subset (inter_subset_inter hsub hsubB)
    apply hinf
    refine (hfin.union (finite_Icc c y)).subset ?_
    rintro z ⟨hz1, hz2⟩
    by_cases hzy : y ≤ z
    · exact Or.inl ⟨hz1, hzy⟩
    · exact Or.inr ⟨le_of_lt hz2, by omega⟩
  obtain ⟨d0, hd0C, hyd0⟩ := hcut
  let S : Set ℤ := {d | d ∈ Cu ∧ c < d ∧ N ≤ (Lv ∩ Ioc c d).ncard}
  have hd0S : d0 ∈ S := by
    refine ⟨hd0C, by omega, ?_⟩
    rw [← htc, ← ncard_coe_finset]
    refine ncard_le_ncard ?_ ((finite_Ioc c d0).inter_of_right Lv)
    intro z hz
    exact ⟨(ht hz).1, (ht hz).2, (t.le_max' z hz).trans hyd0⟩
  have hbdd : BddBelow S := ⟨c, fun d hd => le_of_lt hd.2.1⟩
  have hnS : sInf S ∈ S := Int.csInf_mem ⟨d0, hd0S⟩ hbdd
  set n := sInf S
  obtain ⟨hnC, hcn, hNn⟩ := hnS
  refine ⟨n, hnC, hcn, hNn, ?_⟩
  let A : Set ℤ := {d | d ∈ Cu ∧ c ≤ d ∧ d < n}
  by_cases hA : A.Nonempty
  · have hAb : BddAbove A := ⟨n, fun d hd => le_of_lt hd.2.2⟩
    have hpA : sSup A ∈ A := Int.csSup_mem hA hAb
    set p := sSup A
    obtain ⟨hpC, hcp, hpn⟩ := hpA
    have h1 : (Lv ∩ Ioc p n).ncard ≤ Bu := by
      refine ncard_piece_le hsub hCu (Ioc_subset_cutBoard fun d hd hpd hdn => ?_)
      have : d ≤ p := le_csSup hAb ⟨hd, by omega, hdn⟩
      omega
    have h2 : (Lv ∩ Ioc c p).ncard ≤ N - 1 := by
      by_contra hlt
      rcases eq_or_lt_of_le hcp with hcp' | hcp'
      · rw [hcp', Ioc_self, inter_empty, ncard_empty] at hlt; omega
      · have : n ≤ p := csInf_le hbdd ⟨hpC, hcp', by omega⟩
        omega
    rw [ncard_inter_Ioc_add Lv hcp (le_of_lt hpn)]
    omega
  · have h1 : (Lv ∩ Ioc c n).ncard ≤ Bu :=
      ncard_piece_le hsub hCu (Ioc_subset_cutBoard fun d hd hcd hdn =>
        hA ⟨d, hd, le_of_lt hcd, hdn⟩)
    omega

/-- One step of the greedy grouping, to the left of `c`. -/
lemma down_step (hsub : Lv ⊆ Lu) (hN : 1 ≤ N)
    (hCu : ∀ x, (Lu ∩ cutBoard Cu x).Finite ∧ (Lu ∩ cutBoard Cu x).ncard ≤ Bu)
    (c : ℤ) (hinf : (Lv ∩ Iic c).Infinite) :
    ∃ d ∈ Cu, d < c ∧ N ≤ (Lv ∩ Ioc d c).ncard ∧ (Lv ∩ Ioc d c).ncard ≤ N + Bu - 1 := by
  obtain ⟨t, ht, htc⟩ := hinf.exists_subset_card_eq N
  have hne : t.Nonempty := Finset.card_pos.1 (by omega)
  set y := t.min' hne
  have hyt : y ∈ t := t.min'_mem hne
  have hyc : y ≤ c := (ht hyt).2
  have hcut : ∃ d ∈ Cu, d < y := by
    by_contra hno
    push Not at hno
    have hsubB : Iic y ⊆ cutBoard Cu y := by
      rintro z hz d hd ⟨-, h2⟩
      rw [max_eq_left (show z ≤ y from hz)] at h2
      exact absurd h2 (not_lt.2 (hno d hd))
    have hfin : (Lv ∩ Iic y).Finite :=
      (hCu y).1.subset (inter_subset_inter hsub hsubB)
    apply hinf
    refine (hfin.union (finite_Icc y c)).subset ?_
    rintro z ⟨hz1, hz2⟩
    by_cases hzy : z ≤ y
    · exact Or.inl ⟨hz1, hzy⟩
    · exact Or.inr ⟨by omega, hz2⟩
  obtain ⟨d0, hd0C, hd0y⟩ := hcut
  let S : Set ℤ := {d | d ∈ Cu ∧ d < c ∧ N ≤ (Lv ∩ Ioc d c).ncard}
  have hd0S : d0 ∈ S := by
    refine ⟨hd0C, by omega, ?_⟩
    rw [← htc, ← ncard_coe_finset]
    refine ncard_le_ncard ?_ ((finite_Ioc d0 c).inter_of_right Lv)
    intro z hz
    exact ⟨(ht hz).1, lt_of_lt_of_le hd0y (t.min'_le z hz), (ht hz).2⟩
  have hbdd : BddAbove S := ⟨c, fun d hd => le_of_lt hd.2.1⟩
  have hnS : sSup S ∈ S := Int.csSup_mem ⟨d0, hd0S⟩ hbdd
  set n := sSup S
  obtain ⟨hnC, hnc, hNn⟩ := hnS
  refine ⟨n, hnC, hnc, hNn, ?_⟩
  let A : Set ℤ := {d | d ∈ Cu ∧ n < d ∧ d ≤ c}
  by_cases hA : A.Nonempty
  · have hAb : BddBelow A := ⟨n, fun d hd => le_of_lt hd.2.1⟩
    have hqA : sInf A ∈ A := Int.csInf_mem hA hAb
    set q := sInf A
    obtain ⟨hqC, hnq, hqc⟩ := hqA
    have h1 : (Lv ∩ Ioc n q).ncard ≤ Bu := by
      refine ncard_piece_le hsub hCu (Ioc_subset_cutBoard fun d hd hnd hdq => ?_)
      have : q ≤ d := csInf_le hAb ⟨hd, hnd, by omega⟩
      omega
    have h2 : (Lv ∩ Ioc q c).ncard ≤ N - 1 := by
      by_contra hlt
      rcases eq_or_lt_of_le hqc with hqc' | hqc'
      · rw [hqc', Ioc_self, inter_empty, ncard_empty] at hlt; omega
      · have : q ≤ n := le_csSup hbdd ⟨hqC, hqc', by omega⟩
        omega
    rw [ncard_inter_Ioc_add Lv (le_of_lt hnq) hqc]
    omega
  · have h1 : (Lv ∩ Ioc n c).ncard ≤ Bu :=
      ncard_piece_le hsub hCu (Ioc_subset_cutBoard fun d hd hnd hdc =>
        hA ⟨d, hd, hnd, le_of_lt hdc⟩)
    omega

end Child

/-- The boards of the partition with cut set `range e`, for `e` strictly increasing on `ℤ`. 
-/
lemma board_of_seq {e : ℤ → ℤ} (he : ∀ k, 1 ≤ e (k + 1) - e k) (x : ℤ) :
    ∃ k, cutBoard (range e) x = Ioc (e k) (e (k + 1)) := by
  have hmono : StrictMono e := strictMono_int_of_lt_succ fun k => by have := he k; omega
  have up : ∀ n : ℕ, e 0 + n ≤ e n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => have := he n; push_cast; omega
  have down : ∀ n : ℕ, e (-(n : ℤ)) ≤ e 0 - n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := he (-((n + 1 : ℕ) : ℤ))
      have h' : -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) := by push_cast; ring
      rw [h'] at this; push_cast at this ⊢; omega
  let S : Set ℤ := {k | e k < x}
  have hne : S.Nonempty := by
    refine ⟨-(((e 0 - x).toNat + 1 : ℕ) : ℤ), ?_⟩
    have := down ((e 0 - x).toNat + 1)
    show e _ < x
    push_cast at this ⊢; omega
  have hbdd : BddAbove S := by
    refine ⟨((x - e 0).toNat : ℤ), fun k hk => ?_⟩
    by_contra hlt
    push Not at hlt
    have := up k.toNat
    have hk' : e k < x := hk
    rw [Int.toNat_of_nonneg (by omega)] at this
    omega
  have hmem : sSup S ∈ S := Int.csSup_mem hne hbdd
  have hnot : sSup S + 1 ∉ S := fun h => by
    have := le_csSup hbdd h; omega
  set k := sSup S
  have hk1 : e k < x := hmem
  have hk2 : x ≤ e (k + 1) := by simpa [S] using hnot
  refine ⟨k, ?_⟩
  ext y
  simp only [cutBoard, mem_range, forall_exists_index, forall_apply_eq_imp_iff, mem_ofPred_eq,
    mem_Ioc]
  constructor
  · intro h
    by_contra hy
    rcases not_and_or.1 hy with hy | hy
    · exact h k ⟨by rw [min_le_iff]; right; omega, by rw [lt_max_iff]; left; exact hk1⟩
    · exact h (k + 1) ⟨by rw [min_le_iff]; left; exact hk2, by rw [lt_max_iff]; right; omega⟩
  · rintro ⟨hy1, hy2⟩ j ⟨h1, h2⟩
    have hlo : e k < e j := by
      rcases min_choice x y with hm | hm <;> rw [hm] at h1 <;> omega
    have hhi : e j < e (k + 1) := by
      rcases max_choice x y with hm | hm <;> rw [hm] at h2 <;> omega
    have := hmono.lt_iff_lt.1 hlo
    have := hmono.lt_iff_lt.1 hhi
    omega

/-- The partition into singletons. -/
lemma cutBoard_univ (x : ℤ) : cutBoard univ x = {x} := by
  ext y
  simp only [cutBoard, mem_univ, true_imp_iff, mem_ofPred_eq, mem_singleton_iff]
  constructor
  · intro h; by_contra hne
    exact h (min x y) ⟨le_rfl, by rcases lt_or_gt_of_ne hne with h | h <;> simp [h, h.le]⟩
  · rintro rfl c ⟨h1, h2⟩; simp at h1 h2; omega

/-- Lemma 6.12, child step (greedy grouping of consecutive `u`-boards). -/
theorem child_step (Lu Lv Cu : Set ℤ) (Bu N : ℕ) (hsub : Lv ⊆ Lu) (hinf : Lv.Infinite)
    (hN : 1 ≤ N) (hCu : ∀ x, (Lu ∩ cutBoard Cu x).Finite ∧ (Lu ∩ cutBoard Cu x).ncard ≤ Bu) :
    ∃ Cv ⊆ Cu, ∀ x, (Lv ∩ cutBoard Cv x).Finite ∧ N ≤ (Lv ∩ cutBoard Cv x).ncard ∧
      (Lv ∩ cutBoard Cv x).ncard ≤ N + Bu - 1 := by
  have hfinI : ∀ a b, (Lv ∩ Ioc a b).Finite := fun a b => (finite_Ioc a b).inter_of_right Lv
  have hup : ¬ BddAbove Lv → ∀ c, (Lv ∩ Ioi c).Infinite := by
    intro h c hfin
    obtain ⟨M, hM⟩ := hfin.bddAbove
    exact h ⟨max c M, fun z hz => by
      by_cases hzc : z ≤ c
      · exact le_max_of_le_left hzc
      · exact le_max_of_le_right (hM ⟨hz, lt_of_not_ge hzc⟩)⟩
  have hdown : ¬ BddBelow Lv → ∀ c, (Lv ∩ Iic c).Infinite := by
    intro h c hfin
    obtain ⟨M, hM⟩ := hfin.bddBelow
    exact h ⟨min c M, fun z hz => by
      by_cases hzc : c < z
      · exact min_le_of_left_le hzc.le
      · exact min_le_of_right_le (hM ⟨hz, le_of_not_gt hzc⟩)⟩
  by_cases hA : BddAbove Lv
  · -- `L_v` bounded above: group from the top downwards.
    have hB : ¬ BddBelow Lv := fun hB => hinf (hB.finite_of_bddAbove hA)
    obtain ⟨M, hM⟩ := hA
    choose pv hpvC hpvlt hpv1 hpv2 using fun c => down_step hsub hN hCu c (hdown hB c)
    let f : ℕ → ℤ := fun k => pv^[k + 1] M
    have hfs : ∀ k, f (k + 1) = pv (f k) := fun k => Function.iterate_succ_apply' pv (k + 1) M
    have hanti : StrictAnti f := strictAnti_nat_of_succ_lt fun k => by rw [hfs]; exact hpvlt _
    have hfle : ∀ k : ℕ, f k ≤ f 0 - k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => have := hanti (show k < k + 1 by omega); push_cast; omega
    refine ⟨range f, by
      rintro _ ⟨k, rfl⟩
      show pv^[k + 1] M ∈ Cu
      rw [Function.iterate_succ_apply']; exact hpvC _, fun x => ?_⟩
    by_cases hx : f 0 < x
    · have hb : cutBoard (range f) x = Ioi (f 0) :=
        cutBoard_eq_Ioi ⟨0, rfl⟩ hx (by
          rintro _ ⟨k, rfl⟩ hk
          exact absurd (hanti.antitone (Nat.zero_le k)) (not_le.2 hk))
      have hf0 : f 0 = pv M := rfl
      have he : Lv ∩ Ioi (f 0) = Lv ∩ Ioc (pv M) M := by
        rw [hf0]
        ext z
        simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
        constructor
        · rintro ⟨hz, h⟩; exact ⟨hz, h, hM hz⟩
        · rintro ⟨hz, h, -⟩; exact ⟨hz, h⟩
      rw [hb, he]
      exact ⟨hfinI _ _, hpv1 M, hpv2 M⟩
    · push Not at hx
      have hex : ∃ k, f k < x := ⟨(f 0 - x).toNat + 1, by
        have := hfle ((f 0 - x).toNat + 1); push_cast at this; omega⟩
      set k := Nat.find hex with hkdef
      have hk : f k < x := Nat.find_spec hex
      have hk0 : k ≠ 0 := fun h => by rw [h] at hk; omega
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      have hjx : x ≤ f j := not_lt.1 (Nat.find_min hex (show j < k by omega))
      rw [hj] at hk
      have hb : cutBoard (range f) x = Ioc (f (j + 1)) (f j) :=
        cutBoard_eq_Ioc ⟨j + 1, rfl⟩ ⟨j, rfl⟩ hk hjx (by
          rintro _ ⟨i, rfl⟩ h1 h2
          have := hanti.lt_iff_gt.1 h1
          have := hanti.lt_iff_gt.1 h2
          omega)
      rw [hb, hfs]
      exact ⟨hfinI _ _, hpv1 _, hpv2 _⟩
  by_cases hB : BddBelow Lv
  · -- `L_v` bounded below: group from the bottom upwards.
    obtain ⟨m, hm⟩ := hB
    choose nx hnxC hnxlt hnx1 hnx2 using fun c => up_step hsub hN hCu c (hup hA c)
    let e : ℕ → ℤ := fun k => nx^[k + 1] (m - 1)
    have hes : ∀ k, e (k + 1) = nx (e k) :=
      fun k => Function.iterate_succ_apply' nx (k + 1) (m - 1)
    have hmono : StrictMono e := strictMono_nat_of_lt_succ fun k => by rw [hes]; exact hnxlt _
    have hege : ∀ k : ℕ, e 0 + k ≤ e k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => have := hmono (show k < k + 1 by omega); push_cast; omega
    refine ⟨range e, by
      rintro _ ⟨k, rfl⟩
      show nx^[k + 1] (m - 1) ∈ Cu
      rw [Function.iterate_succ_apply']; exact hnxC _, fun x => ?_⟩
    by_cases hx : x ≤ e 0
    · have hb : cutBoard (range e) x = Iic (e 0) :=
        cutBoard_eq_Iic ⟨0, rfl⟩ hx (by
          rintro _ ⟨k, rfl⟩ hk
          exact absurd (hmono.monotone (Nat.zero_le k)) (not_le.2 hk))
      have he0 : e 0 = nx (m - 1) := rfl
      have he : Lv ∩ Iic (e 0) = Lv ∩ Ioc (m - 1) (nx (m - 1)) := by
        rw [he0]
        ext z
        simp only [mem_inter_iff, mem_Iic, mem_Ioc]
        constructor
        · rintro ⟨hz, h⟩; exact ⟨hz, by have := hm hz; omega, h⟩
        · rintro ⟨hz, -, h⟩; exact ⟨hz, h⟩
      rw [hb, he]
      exact ⟨hfinI _ _, hnx1 _, hnx2 _⟩
    · push Not at hx
      have hex : ∃ k, x ≤ e k := ⟨(x - e 0).toNat, by
        have := hege (x - e 0).toNat; omega⟩
      set k := Nat.find hex with hkdef
      have hk : x ≤ e k := Nat.find_spec hex
      have hk0 : k ≠ 0 := fun h => by rw [h] at hk; omega
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      have hjx : e j < x := not_le.1 (Nat.find_min hex (show j < k by omega))
      rw [hj] at hk
      have hb : cutBoard (range e) x = Ioc (e j) (e (j + 1)) :=
        cutBoard_eq_Ioc ⟨j, rfl⟩ ⟨j + 1, rfl⟩ hjx hk (by
          rintro _ ⟨i, rfl⟩ h1 h2
          have := hmono.lt_iff_lt.1 h1
          have := hmono.lt_iff_lt.1 h2
          omega)
      rw [hb, hes]
      exact ⟨hfinI _ _, hnx1 _, hnx2 _⟩
  · -- `L_v` unbounded in both directions: group outwards from a cut `c₀`.
    choose nx hnxC hnxlt hnx1 hnx2 using fun c => up_step hsub hN hCu c (hup hA c)
    choose pv hpvC hpvlt hpv1 hpv2 using fun c => down_step hsub hN hCu c (hdown hB c)
    set c₀ := nx 0
    let E : ℤ → ℤ := fun k => match k with
      | Int.ofNat j => nx^[j] c₀
      | Int.negSucc j => pv^[j + 1] c₀
    let P : ℤ → ℤ → Prop := fun a b =>
      a < b ∧ N ≤ (Lv ∩ Ioc a b).ncard ∧ (Lv ∩ Ioc a b).ncard ≤ N + Bu - 1
    have hEC : ∀ k, E k ∈ Cu := by
      intro k
      rcases k with j | j
      · rcases j with _ | j
        · exact hnxC 0
        · show nx^[j + 1] c₀ ∈ Cu
          rw [Function.iterate_succ_apply']; exact hnxC _
      · show pv^[j + 1] c₀ ∈ Cu
        rw [Function.iterate_succ_apply']; exact hpvC _
    have hEP : ∀ k, P (E k) (E (k + 1)) := by
      intro k
      rcases k with j | j
      · show P (nx^[j] c₀) (nx^[j + 1] c₀)
        rw [Function.iterate_succ_apply']
        exact ⟨hnxlt _, hnx1 _, hnx2 _⟩
      · rcases j with _ | j
        · show P (pv^[0 + 1] c₀) (nx^[0] c₀)
          simp only [zero_add, Function.iterate_one, Function.iterate_zero, id]
          exact ⟨hpvlt _, hpv1 _, hpv2 _⟩
        · have hk : Int.negSucc (j + 1) + 1 = Int.negSucc j := by
            rw [Int.negSucc_eq, Int.negSucc_eq]; push_cast; ring
          rw [hk]
          show P (pv^[j + 1 + 1] c₀) (pv^[j + 1] c₀)
          rw [Function.iterate_succ_apply' pv (j + 1)]
          exact ⟨hpvlt _, hpv1 _, hpv2 _⟩
    refine ⟨range E, by rintro _ ⟨k, rfl⟩; exact hEC k, fun x => ?_⟩
    obtain ⟨k, hk⟩ := board_of_seq (e := E) (fun k => by have := (hEP k).1; omega) x
    rw [hk]
    exact ⟨hfinI _ _, (hEP k).2.1, (hEP k).2.2⟩

/-- Lemma 6.12, root step: blocks of exactly `N` points (the child step for the partition into
singletons, `B_u = 1`). -/
theorem root_step (L : Set ℤ) (hL : L.Infinite) (N : ℕ) (hN : 1 ≤ N) :
    ∃ C : Set ℤ, ∀ x, (L ∩ cutBoard C x).ncard = N := by
  obtain ⟨Cv, -, h⟩ := child_step univ L univ 1 N (subset_univ L) hL hN fun x => by
    rw [cutBoard_univ, univ_inter]; simp
  exact ⟨Cv, fun x => by have := h x; omega⟩

end ConstructionAux

/-- **Lemma 6.12** (`lem:boards`), as its recursive construction. For a root `v`, `L_v` infinite
and `N_v ≥ 1`: there is a partition of `ℤ` into consecutive intervals each meeting `L_v` in
exactly `N_v` points (`B_v = N_v`). For `v` with parent `u`: if every `u`-board meets `L_u` in at
most `B_u` points (finitely many) and `L_v ⊆ L_u` is infinite, there is a coarsening (every
`v`-board a union of consecutive `u`-boards) whose boards meet `L_v` in between `N_v` and
`N_v + B_u - 1` points (`B_v = N_v + B_u - 1`). -/
theorem lem_boards :
    (∀ L : Set ℤ, L.Infinite → ∀ N : ℕ, 1 ≤ N →
      ∃ C : Set ℤ, ∀ x, (L ∩ cutBoard C x).ncard = N) ∧
    (∀ (Lu Lv Cu : Set ℤ) (Bu N : ℕ), Lv ⊆ Lu → Lv.Infinite → 1 ≤ N →
      (∀ x, (Lu ∩ cutBoard Cu x).Finite ∧ (Lu ∩ cutBoard Cu x).ncard ≤ Bu) →
      ∃ Cv ⊆ Cu, ∀ x, (Lv ∩ cutBoard Cv x).Finite ∧ N ≤ (Lv ∩ cutBoard Cv x).ncard ∧
        (Lv ∩ cutBoard Cv x).ncard ≤ N + Bu - 1) := by
  exact ⟨ConstructionAux.root_step, ConstructionAux.child_step⟩

/-! ## Vertices, requirements and choices -/

/-- Vertices `v` (those with `isV v`) with label `lab v`, scale `N v` and thresholds `s v`,
`q v`. -/
inductive Requirements
  | mk (isV : ℕ → Prop) (lab : ℕ → Set ℤ) (N : ℕ → ℕ) (s : ℕ → ℝ) (q : ℕ → ℝ)

namespace Requirements

/-- The vertices. -/
def isV : Requirements → ℕ → Prop
  | mk isV _ _ _ _ => isV

/-- The language label `L_v`. -/
def lab : Requirements → ℕ → Set ℤ
  | mk _ lab _ _ _ => lab

/-- The scale `N_v`. -/
def N : Requirements → ℕ → ℕ
  | mk _ _ N _ _ => N

/-- The safety threshold `s_v`. -/
def s : Requirements → ℕ → ℝ
  | mk _ _ _ s _ => s

/-- The density requirement `q_v`. -/
def q : Requirements → ℕ → ℝ
  | mk _ _ _ _ q => q

end Requirements

/-- The free choices of the construction: protected sets `prot a H = Prot_a(H)`, board
partitions for roots and for children, and a tie-breaking rule `pick S used` choosing a point of
`S` outside `used`. -/
inductive Choices
  | mk (prot : ℕ → List (Set ℤ) → Set ℤ) (rootCuts : ℕ → Set ℤ)
      (childCuts : ℕ → ℕ → Set ℤ → ℕ → Set ℤ) (pick : Set ℤ → Set ℤ → ℤ)

namespace Choices

/-- The protected set `Prot_a(H)` chosen for the requirement of `a` and the chain `H`. -/
def prot : Choices → ℕ → List (Set ℤ) → Set ℤ
  | mk prot _ _ _ => prot

/-- The board cuts chosen for `v` as a root. -/
def rootCuts : Choices → ℕ → Set ℤ
  | mk _ rootCuts _ _ => rootCuts

/-- The board cuts chosen for `v` with parent `u`, from the parent's cuts and bound `B_u`. -/
def childCuts : Choices → ℕ → ℕ → Set ℤ → ℕ → Set ℤ
  | mk _ _ childCuts _ => childCuts

/-- The tie-breaking rule: a point of `S` outside `used`. -/
def pick : Choices → Set ℤ → Set ℤ → ℤ
  | mk _ _ _ pick => pick

end Choices

/-- The properties the paper requires of its choices. `prot_spec`: for every index `a` with
`s_a > 0` and every list `H` that is safe for `(N_a, s_a)` (Definition 6.2, whatever language `H`
starts at), `prot a H` is a protected set (Definition 6.11) for `(N_a, s_a)` and `H`. The
construction uses `prot a H` only for `H = H[a,v]`, which starts at `L_a`, and only when `s_a > 0`
(as the paper requires); asking it for every safe list is a stronger requirement on the choice
than the paper makes. The theorem
`paperValid_extends` (Extension.lean) shows that, when the vertices form an initial segment
of `ℕ` (as in both vertex systems: `IsFixedEpsSystem.initial`, `IsCopySystem.all`), the stronger
requirement restricts nothing: a choice meeting the paper's requirement can then be changed into
one meeting `Choices.Valid` with the same forest data at every vertex and the same generator. `root_spec`,
`child_spec`: the board partitions are those of Lemma 6.12. `pick_spec`: `pick` chooses an unused
point when one exists. -/
structure Choices.Valid (X : Set (Set ℤ)) (R : Requirements) (C : Choices) : Prop where
  prot_spec : ∀ a H, 0 < R.s a → Safe X (R.N a) (R.s a) H →
    def_history_protected_set X (R.N a) (R.s a) H (C.prot a H)
  root_spec : ∀ v, (R.lab v).Infinite → 1 ≤ R.N v →
    ∀ x, (R.lab v ∩ cutBoard (C.rootCuts v) x).ncard = R.N v
  child_spec : ∀ v u Cu Bu, R.lab v ⊆ R.lab u → (R.lab v).Infinite → 1 ≤ R.N v →
    (∀ x, (R.lab u ∩ cutBoard Cu x).Finite ∧ (R.lab u ∩ cutBoard Cu x).ncard ≤ Bu) →
    C.childCuts v u Cu Bu ⊆ Cu ∧
    ∀ x, (R.lab v ∩ cutBoard (C.childCuts v u Cu Bu) x).Finite ∧
      R.N v ≤ (R.lab v ∩ cutBoard (C.childCuts v u Cu Bu) x).ncard ∧
      (R.lab v ∩ cutBoard (C.childCuts v u Cu Bu) x).ncard ≤ R.N v + Bu - 1
  pick_spec : ∀ S used, (S \ used).Nonempty → C.pick S used ∈ S \ used

/-- The fixed-`ε` vertex system of Section 6.4: the vertices `0, 1, …` (stopping if `X` is
finite) enumerate the distinct languages of `X`; `q_i = (b(L_i) - ε)_+`, `s_i = (b(L_i) - ε/2)_+`,
and `N_i ≥ 1` satisfies (18): `1/N_i ≤ ε/2` and `s_i < b_{N_i}(L_i)` if `s_i > 0`.
The fields `initial` (the vertices form an initial segment of `ℕ`) and `lab_inj` (distinct
vertices carry distinct languages) transcribe the paper's enumeration of Section 6.4; no proof
uses them (they are only established, when such a system is built in `Foundations.lean`). -/
structure IsFixedEpsSystem (X : Set (Set ℤ)) (ε : ℝ) (R : Requirements) : Prop where
  initial : ∀ u v, R.isV v → u ≤ v → R.isV u
  lab_mem : ∀ v, R.isV v → R.lab v ∈ X
  lab_inj : ∀ u v, R.isV u → R.isV v → R.lab u = R.lab v → u = v
  lab_surj : ∀ L ∈ X, ∃ v, R.isV v ∧ R.lab v = L
  q_def : ∀ v, R.isV v → R.q v = max (bK X (R.lab v) - ε) 0
  s_def : ∀ v, R.isV v → R.s v = max (bK X (R.lab v) - ε / 2) 0
  N_pos : ∀ v, R.isV v → 1 ≤ R.N v
  N_small : ∀ v, R.isV v → (1 : ℝ) / R.N v ≤ ε / 2
  N_safe : ∀ v, R.isV v → 0 < R.s v → R.s v < bn X (R.lab v) (R.N v)

/-- The formal-copy vertex system of Section 6.8: every `v` is a vertex, and `v ↦ (L_v, m_v)`
(`m_v = copy v`) enumerates all pairs `(L, m)` with `L ∈ X`, `m ≥ 1`, each once, with `(L, m)`
before `(L, m + 1)`; `q = (b(L) - 2^{-m})_+`, `s = (b(L) - 2^{-m-1})_+`, `1/N ≤ 2^{-m-1}` and
`s < b_N(L)` if `s > 0`. -/
structure IsCopySystem (X : Set (Set ℤ)) (R : Requirements) (copy : ℕ → ℕ) : Prop where
  all : ∀ v, R.isV v
  lab_mem : ∀ v, R.lab v ∈ X
  copy_pos : ∀ v, 1 ≤ copy v
  inj : ∀ u v, R.lab u = R.lab v → copy u = copy v → u = v
  surj : ∀ L ∈ X, ∀ m, 1 ≤ m → ∃ v, R.lab v = L ∧ copy v = m
  order : ∀ u v, R.lab u = R.lab v → copy v = copy u + 1 → u < v
  q_def : ∀ v, R.q v = max (bK X (R.lab v) - (1 / 2 : ℝ) ^ copy v) 0
  s_def : ∀ v, R.s v = max (bK X (R.lab v) - (1 / 2 : ℝ) ^ (copy v + 1)) 0
  N_pos : ∀ v, 1 ≤ R.N v
  N_small : ∀ v, (1 : ℝ) / R.N v ≤ (1 / 2 : ℝ) ^ (copy v + 1)
  N_safe : ∀ v, 0 < R.s v → R.s v < bn X (R.lab v) (R.N v)

/-! ## The forest -/

/-- The data attached to a vertex: its parent, its ancestor path (root first, the vertex last),
its board cuts, its board bound `B_v`, and its total protected set `P_v`. -/
inductive VData
  | mk (parent : Option ℕ) (anc : List ℕ) (cuts : Set ℤ) (B : ℕ) (P : Set ℤ)

namespace VData

/-- The parent of the vertex, if it is not a root. -/
def parent : VData → Option ℕ
  | mk parent _ _ _ _ => parent

/-- The ancestor path, root first, the vertex last. -/
def anc : VData → List ℕ
  | mk _ anc _ _ _ => anc

/-- The cut points of the vertex's board partition. -/
def cuts : VData → Set ℤ
  | mk _ _ cuts _ _ => cuts

/-- The board bound `B_v`. -/
def B : VData → ℕ
  | mk _ _ _ B _ => B

/-- The total protected set `P_v`. -/
def P : VData → Set ℤ
  | mk _ _ _ _ P => P

end VData

instance : Inhabited VData := ⟨⟨none, [], ∅, 0, ∅⟩⟩

/-- Delete consecutive repetitions of the same language. -/
noncomputable def compress : List (Set ℤ) → List (Set ℤ)
  | [] => []
  | [a] => [a]
  | a :: b :: t => if a = b then compress (b :: t) else a :: compress (b :: t)

/-- The possible parents (20) of `v` (non-strict inclusion, Section 6.8), in increasing index
order: earlier vertices `u` with `L_v ⊆ L_u` and `P_u ⊆ L_v`. -/
noncomputable def possibleParents (R : Requirements) (prev : List VData) (v : ℕ) : List ℕ :=
  (List.range v).filter fun u =>
    decide (R.isV u ∧ R.lab v ⊆ R.lab u ∧ (prev.getD u default).P ⊆ R.lab v)

/-- The parent scan: retain the first possible parent, and replace the retained `p` by `u`
whenever `L_u ⊆ L_p`. -/
noncomputable def scanParent (R : Requirements) : List ℕ → Option ℕ
  | [] => none
  | u :: t => some (t.foldl (fun p u' => if R.lab u' ⊆ R.lab p then u' else p) u)

/-- The compressed chain of labels read from the ancestor list `anc`, from `a` on (consecutive
repetitions deleted). This is the chain `H a` that `processVertex` reads, and `pathChain R C a v`
is `readChain R (vdata R C v).anc a` (`ConstructionAux.pathChain_eq_readChain`); both definitions
spell the expression out, definitionally equal to this one. -/
noncomputable def ConstructionAux.readChain (R : Requirements) (anc : List ℕ) (a : ℕ) :
    List (Set ℤ) :=
  compress ((anc.dropWhile (· ≠ a)).map R.lab)

/-- Processing vertex `v` (Section 6.4, steps 1–3) given the data of the earlier vertices. -/
noncomputable def processVertex (R : Requirements) (C : Choices) (prev : List VData) (v : ℕ) :
    VData :=
  let pd : ℕ → VData := fun u => prev.getD u default
  let par := scanParent R (possibleParents R prev v)
  let anc : List ℕ := match par with
    | none => [v]
    | some u => (pd u).anc ++ [v]
  let cuts : Set ℤ := match par with
    | none => C.rootCuts v
    | some u => C.childCuts v u (pd u).cuts (pd u).B
  let B : ℕ := match par with
    | none => R.N v
    | some u => R.N v + (pd u).B - 1
  let cutsOf : ℕ → Set ℤ := fun a => if a = v then cuts else (pd a).cuts
  let H : ℕ → List (Set ℤ) := fun a => compress ((anc.dropWhile (· ≠ a)).map R.lab)
  let P : Set ℤ := ⋃ a ∈ {a | a ∈ anc ∧ 0 < R.s a},
    (C.prot a (H a) ∪ ⋃ x : ℤ, {y | y ∈ R.lab v ∩ cutBoard (cutsOf a) x ∧
      def_raw_pairing_score (H a) (R.lab a ∩ cutBoard (cutsOf a) x) < R.s a})
  ⟨par, anc, cuts, B, P⟩

/-- The data of the vertices `0, …, v - 1`, built in index order. -/
noncomputable def buildForest (R : Requirements) (C : Choices) : ℕ → List VData
  | 0 => []
  | v + 1 => buildForest R C v ++ [processVertex R C (buildForest R C v) v]

/-- The data of vertex `v`. -/
noncomputable def vdata (R : Requirements) (C : Choices) (v : ℕ) : VData :=
  processVertex R C (buildForest R C v) v

/-- `a ⪯ v`: `a` is an ancestor of `v`, equality allowed. -/
def IsAnc (R : Requirements) (C : Choices) (a v : ℕ) : Prop := a ∈ (vdata R C v).anc

/-- The `v`-board `I_v(x)` containing `x`. -/
noncomputable def boardOf (R : Requirements) (C : Choices) (v : ℕ) (x : ℤ) : Set ℤ :=
  cutBoard (vdata R C v).cuts x

/-- The compressed chain `H̄[a,v]` of labels on the forest path from `a` to `v` (consecutive
repetitions deleted; for the fixed-`ε` system this is `H[a,v]`). -/
noncomputable def pathChain (R : Requirements) (C : Choices) (a v : ℕ) : List (Set ℤ) :=
  compress (((vdata R C v).anc.dropWhile (· ≠ a)).map R.lab)

/-- `H̄[a,v]` is the chain that the processing of `v` reads from `a` on. -/
lemma ConstructionAux.pathChain_eq_readChain (R : Requirements) (C : Choices) (a v : ℕ) :
    pathChain R C a v = ConstructionAux.readChain R (vdata R C v).anc a := rfl

/-! ## The online algorithm (Section 6.5) -/

/-- `v` is a vertex consistent with the inputs `S`: `isV v` and `S ⊆ L_v`. -/
def Consistent (R : Requirements) (S : Set ℤ) (v : ℕ) : Prop := R.isV v ∧ S ⊆ R.lab v

/-- `v` is critical: consistent, and `L_v ⊆ L_u` for every earlier consistent `u < v`. -/
def Critical (R : Requirements) (S : Set ℤ) (v : ℕ) : Prop :=
  Consistent R S v ∧ ∀ u < v, Consistent R S u → R.lab v ⊆ R.lab u

/-- The current guess `Q_t`: the largest-index critical vertex among the first `t` vertices (on
the inputs `ws = (w_1, …, w_t)`), if any. -/
noncomputable def guess (R : Requirements) (ws : List ℤ) : Option ℕ :=
  if ∃ v < ws.length, Critical R {x | x ∈ ws} v then
    some (Nat.findGreatest (Critical R {x | x ∈ ws}) (ws.length - 1))
  else none

/-- The lowest common ancestor of a set of vertices: the deepest vertex that is an ancestor of
all of them (ancestor indices increase along a path, so the deepest is the largest). -/
noncomputable def lca (R : Requirements) (C : Choices) (S : Set ℕ) : ℕ :=
  sSup {a | ∀ y ∈ S, IsAnc R C a y}

/-- The history `𝓗^t_{v,I}` after the round with inputs `ws`: the guesses `Q_r` of rounds
`r ≤ t` that are defined, descend from `v`, and have input `w_r ∈ I`. -/
def recordHistory (R : Requirements) (C : Choices) (ws : List ℤ) (v : ℕ) (I : Set ℤ) :
    Set ℕ :=
  {y | ∃ r < ws.length, guess R (ws.take (r + 1)) = some y ∧ IsAnc R C v y ∧ ws.getD r 0 ∈ I}

/-- The record `Z_{v,I}` after the round with inputs `ws`: the LCA of `𝓗^t_{v,I}`. -/
noncomputable def record (R : Requirements) (C : Choices) (ws : List ℤ) (v : ℕ) (I : Set ℤ) :
    ℕ :=
  lca R C (recordHistory R C ws v I)

/-- The pod `I_v(w_t) ∩ L_{Z_{v, I_v(w_t)}}` of the active vertex `v` on the round with inputs
`ws`. -/
noncomputable def pod (R : Requirements) (C : Choices) (ws : List ℤ) (v : ℕ) : Set ℤ :=
  boardOf R C v (ws.getLastD 0) ∩ R.lab (record R C ws v (boardOf R C v (ws.getLastD 0)))

/-- One round of the algorithm: with no guess, output any available integer; otherwise scan the
active path from root to `Q_t` and output an available point of the first pod containing one,
or, if every pod is exhausted, an available point of `L_{Q_t}`. Available means neither an
input so far nor an earlier output. -/
noncomputable def algStep (R : Requirements) (C : Choices) (ws prevOuts : List ℤ) : ℤ :=
  let used : Set ℤ := {x | x ∈ ws ∨ x ∈ prevOuts}
  match guess R ws with
  | none => C.pick univ used
  | some Q =>
    match (vdata R C Q).anc.find? (fun v => decide ((pod R C ws v \ used).Nonempty)) with
    | some v => C.pick (pod R C ws v) used
    | none => C.pick (R.lab Q) used

/-- The outputs of the rounds `0, …, t` on the inputs `ws = (w_0, …, w_t)`. -/
noncomputable def algOutputs (R : Requirements) (C : Choices) (ws : List ℤ) : List ℤ :=
  if h : ws = [] then [] else
    algOutputs R C ws.dropLast ++ [algStep R C ws (algOutputs R C ws.dropLast)]
termination_by ws.length
decreasing_by
  simp only [List.length_dropLast]
  have := List.length_pos_of_ne_nil h
  omega

/-- The generator of the construction. -/
noncomputable def algGen (R : Requirements) (C : Choices) : Generator :=
  fun ws => (algOutputs R C ws).getLastD 0

/-! ## Lemmas 6.13–6.19 (fixed `ε`) -/






/-- A `z`-board `I` is exceptional for the capture time `t₀` (Section 6.6): its `K`-trace
contains an input or an output of a round before `t₀`, or it contains a board of an ancestor of
`z` (including `z`) whose record was initialized before `t₀`, i.e. the board `I_a(w_r)` of a
round `r < t₀` on which `a` was active. -/
def Exceptional (R : Requirements) (C : Choices) (w : ℕ → ℤ) (z t₀ : ℕ) (I : Set ℤ) : Prop :=
  (∃ r < t₀, w r ∈ R.lab z ∩ I ∨ (algGen R C).out w r ∈ R.lab z ∩ I) ∨
  ∃ a, IsAnc R C a z ∧ ∃ r < t₀, ∃ Q, guess R (inputsUpTo w r) = some Q ∧ IsAnc R C a Q ∧
    boardOf R C a (w r) ⊆ I

namespace ConstructionAux

open Finset

/-- The potential `Φ = (visible white) + ⌊(visible unused)/2⌋` of the pairing game, for white
points `W`, black points `Bl` and visible set `V`. -/
def potential (W Bl V : Finset ℤ) : ℕ := (W ∩ V).card + (V \ (W ∪ Bl)).card / 2

/-- A turn of the pairing game does not decrease the potential. -/
lemma potential_turn {W W' Bl Bl' V : Finset ℤ} {a : ℤ} (hWW : W ⊆ W')
    (hBl : Bl' = if a ∈ W then Bl else insert a Bl) (hdisj : Disjoint W' Bl')
    (hresp : (∃ x ∈ V, x ∉ W ∧ x ∉ Bl') → ∃ x ∈ V, x ∉ W ∧ x ∉ Bl' ∧ x ∈ W') :
    potential W Bl V ≤ potential W' Bl' V := by
  unfold potential
  have hBlsub : Bl ⊆ Bl' := by
    rw [hBl]; split_ifs
    · exact Finset.Subset.rfl
    · exact Finset.subset_insert _ _
  have hBl'sub : Bl' ⊆ insert a Bl := by
    rw [hBl]; split_ifs
    · exact Finset.subset_insert _ _
    · exact Finset.Subset.rfl
  set K := (W' \ W) ∩ V with hKdef
  set U := V \ (W ∪ Bl) with hUdef
  set U' := V \ (W' ∪ Bl') with hU'def
  have hw : (W' ∩ V).card = (W ∩ V).card + K.card := by
    have heq : W' ∩ V = W ∩ V ∪ (W' \ W) ∩ V := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro ⟨h1, h2⟩; by_cases h : x ∈ W
        · exact Or.inl ⟨h, h2⟩
        · exact Or.inr ⟨⟨h1, h⟩, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨⟨h1, -⟩, h2⟩)
        · exact ⟨hWW h1, h2⟩
        · exact ⟨h1, h2⟩
    rw [heq, Finset.card_union_of_disjoint]
    rw [Finset.disjoint_left]
    intro x h1 h2
    exact (Finset.mem_sdiff.1 (Finset.mem_inter.1 h2).1).2 (Finset.mem_inter.1 h1).1
  have hKU : K ⊆ U := by
    intro x hx
    simp only [K, Finset.mem_inter, Finset.mem_sdiff] at hx
    simp only [U, Finset.mem_sdiff, Finset.mem_union, not_or]
    exact ⟨hx.2, hx.1.2, fun hb => Finset.disjoint_left.1 hdisj hx.1.1 (hBlsub hb)⟩
  have hUK : (U \ K).card = U.card - K.card := Finset.card_sdiff_of_subset hKU
  have hsub1 : (U \ K).erase a ⊆ U' := by
    intro x hx
    simp only [Finset.mem_erase, Finset.mem_sdiff, U, K, Finset.mem_union, Finset.mem_inter, not_or, not_and] at hx
    simp only [U', Finset.mem_sdiff, Finset.mem_union, not_or]
    obtain ⟨hxa, ⟨hxV, hxW, hxBl⟩, hxK⟩ := hx
    refine ⟨hxV, fun h => hxK ⟨h, hxW⟩ hxV, fun h => ?_⟩
    rcases Finset.mem_insert.1 (hBl'sub h) with h | h
    · exact hxa h
    · exact hxBl h
  have hsub2 : a ∉ U → U \ K ⊆ U' := by
    intro haU x hx
    have hxa : x ≠ a := fun h => haU (h ▸ (Finset.mem_sdiff.1 hx).1)
    exact hsub1 (Finset.mem_erase.2 ⟨hxa, hx⟩)
  have hc1 : U.card - K.card - 1 ≤ U'.card := by
    have := Finset.card_le_card hsub1
    have := Finset.pred_card_le_card_erase (s := U \ K) (a := a)
    omega
  have hKle : K.card ≤ U.card := Finset.card_le_card hKU
  by_cases haU : a ∈ U
  · have hk : 2 ≤ U.card → 1 ≤ K.card := by
      intro h2
      obtain ⟨x, hxU, hxa⟩ := Finset.exists_mem_ne (show 1 < U.card by omega) a
      simp only [U, Finset.mem_sdiff, Finset.mem_union, not_or] at hxU
      have hx' : x ∉ Bl' := fun h => by
        rcases Finset.mem_insert.1 (hBl'sub h) with h | h
        · exact hxa h
        · exact hxU.2.2 h
      obtain ⟨y, hyV, hyW, -, hyW'⟩ := hresp ⟨x, hxU.1, hxU.2.1, hx'⟩
      exact Finset.card_pos.2 ⟨y, by simp only [K, Finset.mem_inter, Finset.mem_sdiff]; exact ⟨⟨hyW', hyW⟩, hyV⟩⟩
    omega
  · have := Finset.card_le_card (hsub2 haU)
    omega

/-- Revealing new points does not decrease the potential, and adds at least `⌊d/2⌋`, provided
every black point is already visible. -/
lemma potential_reveal {W Bl V V' : Finset ℤ} (hVV : V ⊆ V') (hBl : Bl ⊆ V) :
    potential W Bl V + (V' \ V).card / 2 ≤ potential W Bl V' := by
  unfold potential
  set D := V' \ V
  have hw : (W ∩ V').card = (W ∩ V).card + (W ∩ D).card := by
    have heq : W ∩ V' = W ∩ V ∪ W ∩ (V' \ V) := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro ⟨h1, h2⟩; by_cases h : x ∈ V
        · exact Or.inl ⟨h1, h⟩
        · exact Or.inr ⟨h1, h2, h⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2, -⟩)
        · exact ⟨h1, hVV h2⟩
        · exact ⟨h1, h2⟩
    rw [heq, Finset.card_union_of_disjoint]
    rw [Finset.disjoint_left]
    intro x h1 h2
    exact (Finset.mem_sdiff.1 (Finset.mem_inter.1 h2).2).2 (Finset.mem_inter.1 h1).2
  have hu : (V \ (W ∪ Bl)) ∪ (D \ W) ⊆ V' \ (W ∪ Bl) := by
    intro x hx
    simp only [D, Finset.mem_union, Finset.mem_sdiff, not_or] at hx ⊢
    rcases hx with ⟨h1, h2, h3⟩ | ⟨⟨h1, h2⟩, h3⟩
    · exact ⟨hVV h1, h2, h3⟩
    · exact ⟨h1, h3, fun h => h2 (hBl h)⟩
  have hdj : Disjoint (V \ (W ∪ Bl)) (D \ W) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    exact (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 h2).1).2 (Finset.mem_sdiff.1 h1).1
  have h1 := Finset.card_le_card hu
  rw [Finset.card_union_of_disjoint hdj] at h1
  have h2 := Finset.card_sdiff_add_card_inter D W
  have h3 : (D ∩ W).card = (W ∩ D).card := by rw [Finset.inter_comm]
  omega

/-- Revealing several stages. -/
lemma potential_reveal_many (Y : ℕ → Finset ℤ) (hY : Monotone Y) (W Bl : Finset ℤ) (s : ℕ)
    (hBl : Bl ⊆ Y s) : ∀ s', s ≤ s' →
    potential W Bl (Y s) + ∑ i ∈ Ico s s', (Y (i + 1) \ Y i).card / 2 ≤ potential W Bl (Y s') := by
  intro s' hss'
  induction s', hss' using Nat.le_induction with
  | base => simp
  | succ s' hss' ih =>
    rw [Finset.sum_Ico_succ_top hss']
    have := potential_reveal (W := W) (hY (show s' ≤ s' + 1 by omega)) (hBl.trans (hY hss'))
    omega

end ConstructionAux

/-- **Lemma 6.18** (`lem:pairing-game`, local pairing game). A finite board `B` is revealed
through an increasing filtration `∅ = Y₀ ⊆ Y₁ ⊆ ⋯ ⊆ Y_m = B`; `d_i = |Y_i \ Y_{i-1}|`. On turn
`j` (of `T`) the visible set is `Y_{stage j}` (`stage` nondecreasing) and the adversary selects a
visible point `a j` (repetitions allowed). Points selected by the algorithm are white (`W j`
before turn `j`), other adversary-selected points black (`Bl j`). A selected point not already
white becomes black; then, if an unused visible point remains, the algorithm makes one white;
other events may make any unused points of `B` white at any time. If every point of `B` is
selected by the adversary, the final number of white points is at least `∑ ⌊d_i / 2⌋`.
The hypotheses `hY0` (`Y₀ = ∅`), `hW0` (`W 0 ⊆ B`) and `hWsub` (`W (j+1) ⊆ B`) mirror the paper's
statement (the filtration starts at `∅` inside `B`); the Lean proof does not use them. -/
theorem lem_pairing_game (Bd : Finset ℤ) (m : ℕ) (Y : ℕ → Finset ℤ) (hY0 : Y 0 = ∅)
    (hYmono : Monotone Y) (hYm : Y m = Bd) (T : ℕ) (stage : ℕ → ℕ) (hst : Monotone stage)
    (hstm : ∀ j, stage j ≤ m) (a : ℕ → ℤ) (ha : ∀ j < T, a j ∈ Y (stage j))
    (W Bl : ℕ → Finset ℤ) (hBl0 : Bl 0 = ∅) (hW0 : W 0 ⊆ Bd)
    (hBl : ∀ j < T, Bl (j + 1) = if a j ∈ W j then Bl j else insert (a j) (Bl j))
    (hWmono : ∀ j < T, W j ⊆ W (j + 1)) (hWsub : ∀ j < T, W (j + 1) ⊆ Bd)
    (hWdisj : ∀ j < T, Disjoint (W (j + 1)) (Bl (j + 1)))
    (hresp : ∀ j < T, (∃ x ∈ Y (stage j), x ∉ W j ∧ x ∉ Bl (j + 1)) →
      ∃ x ∈ Y (stage j), x ∉ W j ∧ x ∉ Bl (j + 1) ∧ x ∈ W (j + 1))
    (hcomplete : ∀ x ∈ Bd, ∃ j < T, a j = x) :
    ∑ i ∈ Finset.range m, (Y (i + 1) \ Y i).card / 2 ≤ (W T).card := by
  open ConstructionAux Finset in
  have hBlstep : ∀ j < T, Bl (j + 1) ⊆ insert (a j) (Bl j) := fun j hj => by
    rw [hBl j hj]; split_ifs
    · exact Finset.subset_insert _ _
    · exact Finset.Subset.rfl
  have hBlmono : ∀ j < T, Bl j ⊆ Bl (j + 1) := fun j hj => by
    rw [hBl j hj]; split_ifs
    · exact Finset.Subset.rfl
    · exact Finset.subset_insert _ _
  have hBlvis : ∀ j ≤ T, Bl j ⊆ Y (stage j) := by
    intro j
    induction j with
    | zero => intro _; rw [hBl0]; exact Finset.empty_subset _
    | succ j ih =>
      intro hj
      refine (hBlstep j (by omega)).trans ?_
      refine Finset.insert_subset ?_ ?_
      · exact hYmono (hst (Nat.le_succ j)) (ha j (by omega))
      · exact (ih (by omega)).trans (hYmono (hst (Nat.le_succ j)))
  have hmain : ∀ j ≤ T, ∑ i ∈ range (stage j), (Y (i + 1) \ Y i).card / 2 ≤
      potential (W j) (Bl j) (Y (stage j)) := by
    intro j
    induction j with
    | zero =>
      intro _
      have := potential_reveal_many Y hYmono (W 0) (Bl 0) 0 (by rw [hBl0]; exact Finset.empty_subset _)
        (stage 0) (Nat.zero_le _)
      rw [Finset.range_eq_Ico]; omega
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 : potential (W j) (Bl j) (Y (stage j)) ≤
          potential (W (j + 1)) (Bl (j + 1)) (Y (stage j)) :=
        potential_turn (hWmono j (by omega)) (hBl j (by omega))
          (hWdisj j (by omega)) (hresp j (by omega))
      have hle : stage j ≤ stage (j + 1) := hst (Nat.le_succ j)
      have h3 := potential_reveal_many Y hYmono (W (j + 1)) (Bl (j + 1)) (stage j)
        ((hBlstep j (by omega)).trans (Finset.insert_subset (ha j (by omega)) (hBlvis j (by omega))))
        (stage (j + 1)) hle
      rw [← Finset.sum_range_add_sum_Ico _ hle]
      omega
  have hWchain : ∀ j k, j ≤ k → k ≤ T → W j ⊆ W k := by
    intro j k hjk
    induction k, hjk using Nat.le_induction with
    | base => intro _; exact Finset.Subset.rfl
    | succ k hjk ih => intro hk; exact (ih (by omega)).trans (hWmono k (by omega))
  have hBlchain : ∀ j k, j ≤ k → k ≤ T → Bl j ⊆ Bl k := by
    intro j k hjk
    induction k, hjk using Nat.le_induction with
    | base => intro _; exact Finset.Subset.rfl
    | succ k hjk ih => intro hk; exact (ih (by omega)).trans (hBlmono k (by omega))
  have hempty : Bd \ (W T ∪ Bl T) = ∅ := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union, not_or, Finset.notMem_empty, iff_false, not_and, not_not]
    intro hx
    obtain ⟨j, hj, rfl⟩ := hcomplete x hx
    by_cases h : a j ∈ W j
    · exact absurd (hWchain j T (by omega) le_rfl h)
    · intro _
      have : a j ∈ Bl (j + 1) := by rw [hBl j hj, if_neg h]; exact Finset.mem_insert_self _ _
      exact hBlchain (j + 1) T (by omega) le_rfl this
  have h1 := hmain T le_rfl
  have h2 := potential_reveal_many Y hYmono (W T) (Bl T) (stage T) (hBlvis T le_rfl) m (hstm T)
  rw [hYm] at h2
  unfold potential at h1 h2
  rw [hempty, Finset.card_empty] at h2
  have h3 : (W T ∩ Bd).card ≤ (W T).card := Finset.card_le_card Finset.inter_subset_left
  rw [← Finset.sum_range_add_sum_Ico _ (hstm T)]
  omega



/-! ## Lemmas 6.20–6.22 (formal copies) -/




namespace ConstructionAux

/-- The end of `H ++ [L]` is `L`. -/
lemma chainEnd_snoc (H : List (Set ℤ)) (L : Set ℤ) : chainEnd (H ++ [L]) = L := by
  simp [chainEnd]

/-- For every list `H` that is safe for `(n, q)` there is a protected set (Definition 6.11). 
-/
theorem prot_exists (X : Set (Set ℤ)) (n : ℕ) (q : ℝ) (H : List (Set ℤ)) (hs : Safe X n q H) :
    ∃ P, def_history_protected_set X n q H P := by
  by_contra hno
  have bad : ∀ P : Set ℤ, P.Finite → P ⊆ chainEnd H → ∃ L ∈ X, P ⊆ L ∧ L ⊂ chainEnd H ∧
      ∃ T : LTree, def_aot X L T ∧ ∀ Q ∈ T.paths, cn (appendPath (H ++ [L]) Q) n ≤ q := by
    intro P hP hPM
    by_contra h
    apply hno
    refine ⟨P, hP, hPM, fun L hL hPL hLM => ?_⟩
    intro hu
    obtain ⟨T, hT, hTq⟩ := hu
    rw [chainEnd_snoc] at hT
    exact h ⟨L, hL, hPL, hLM, T, hT, hTq⟩
  set M := chainEnd H
  have hcount : {P : Set ℤ | P.Finite ∧ P ⊆ M}.Countable :=
    (Set.countable_ofPred_finite_subset (s := M) (to_countable M)).mono
      fun P (h : P.Finite ∧ P ⊆ M) => (⟨h.1, h.2⟩ : P.Finite ∧ P ⊆ M)
  obtain ⟨f, hf⟩ := hcount.exists_eq_range ⟨∅, finite_empty, empty_subset _⟩
  have hfi : ∀ i, (f i).Finite ∧ f i ⊆ M := fun i => by
    have : f i ∈ range f := mem_range_self i
    rw [← hf] at this; exact this
  choose L hLX hPL hLM T hT hTq using fun i => bad (f i) (hfi i).1 (hfi i).2
  apply hs
  refine ⟨LTree.node M T, ⟨rfl, fun i => ?_, fun F hF hFM => ?_⟩, ?_⟩
  · refine ⟨?_, ?_, (hT i).2⟩
    · rw [(hT i).1]; exact hLX i
    · rw [(hT i).1]; exact hLM i
  · have : F ∈ range f := by rw [← hf]; exact ⟨hF, hFM⟩
    obtain ⟨i, rfl⟩ := this
    exact ⟨i, by rw [(hT i).1]; exact hPL i⟩
  · rintro P ⟨i, Q, hQ, rfl⟩
    have h := hTq i Q hQ
    obtain ⟨Q', rfl⟩ := HistoryTopologyAux.paths_head hQ
    rw [(hT i).1] at h ⊢
    have : appendPath H (M :: L i :: Q') = appendPath (H ++ [L i]) (L i :: Q') := by
      simp [appendPath]
    rw [this]; exact h

/-- Choices built from the existence results (`prot_exists`, `lem_boards`), with `pick`
returning an unused point when there is one. 
-/
noncomputable def mkChoices (X : Set (Set ℤ)) (R : Requirements) : Choices :=
  .mk (fun a H => if h : ∃ P, def_history_protected_set X (R.N a) (R.s a) H P then h.choose else ∅)
    (fun v => if h : ∃ C : Set ℤ, ∀ x, (R.lab v ∩ cutBoard C x).ncard = R.N v then h.choose else ∅)
    (fun v u Cu Bu => if h : ∃ Cv, Cv ⊆ Cu ∧ ∀ x, (R.lab v ∩ cutBoard Cv x).Finite ∧
        R.N v ≤ (R.lab v ∩ cutBoard Cv x).ncard ∧
        (R.lab v ∩ cutBoard Cv x).ncard ≤ R.N v + Bu - 1
      then h.choose else ∅)
    (fun S used => if h : (S \ used).Nonempty then h.some else 0)

/-- The board partitions of `mkChoices` at a root are those of Lemma 6.12 (from `lem_boards`). -/
lemma mkChoices_root_spec (X : Set (Set ℤ)) (R : Requirements) : ∀ v, (R.lab v).Infinite →
    1 ≤ R.N v → ∀ x, (R.lab v ∩ cutBoard ((mkChoices X R).rootCuts v) x).ncard = R.N v := by
  intro v hinf hN x
  have hex : ∃ C : Set ℤ, ∀ x, (R.lab v ∩ cutBoard C x).ncard = R.N v :=
    lem_boards.1 (R.lab v) hinf (R.N v) hN
  show (R.lab v ∩ cutBoard (if h : ∃ C : Set ℤ, ∀ x, (R.lab v ∩ cutBoard C x).ncard = R.N v
    then h.choose else ∅) x).ncard = R.N v
  rw [dif_pos hex]; exact hex.choose_spec x

/-- The board partitions of `mkChoices` at a child are those of Lemma 6.12 (from `lem_boards`). -/
lemma mkChoices_child_spec (X : Set (Set ℤ)) (R : Requirements) :
    ∀ v u Cu Bu, R.lab v ⊆ R.lab u → (R.lab v).Infinite → 1 ≤ R.N v →
    (∀ x, (R.lab u ∩ cutBoard Cu x).Finite ∧ (R.lab u ∩ cutBoard Cu x).ncard ≤ Bu) →
    (mkChoices X R).childCuts v u Cu Bu ⊆ Cu ∧
    ∀ x, (R.lab v ∩ cutBoard ((mkChoices X R).childCuts v u Cu Bu) x).Finite ∧
      R.N v ≤ (R.lab v ∩ cutBoard ((mkChoices X R).childCuts v u Cu Bu) x).ncard ∧
      (R.lab v ∩ cutBoard ((mkChoices X R).childCuts v u Cu Bu) x).ncard ≤ R.N v + Bu - 1 := by
  intro v u Cu Bu hsub hinf hN hCu
  have hex : ∃ Cv, Cv ⊆ Cu ∧ ∀ x, (R.lab v ∩ cutBoard Cv x).Finite ∧
      R.N v ≤ (R.lab v ∩ cutBoard Cv x).ncard ∧
      (R.lab v ∩ cutBoard Cv x).ncard ≤ R.N v + Bu - 1 := by
    obtain ⟨Cv, h1, h2⟩ := lem_boards.2 (R.lab u) (R.lab v) Cu Bu (R.N v) hsub hinf hN hCu
    exact ⟨Cv, h1, h2⟩
  have e : (mkChoices X R).childCuts v u Cu Bu = hex.choose := by
    simp only [mkChoices, Choices.childCuts]; exact dif_pos hex
  rw [e]; exact hex.choose_spec

/-- `mkChoices` picks an unused point when there is one. -/
lemma mkChoices_pick_spec (X : Set (Set ℤ)) (R : Requirements) :
    ∀ S used, (S \ used).Nonempty → (mkChoices X R).pick S used ∈ S \ used := by
  intro S used h
  show (if h : (S \ used).Nonempty then h.some else 0) ∈ S \ used
  rw [dif_pos h]; exact h.some_mem

/-- `mkChoices` is valid. Its protected sets come from `prot_exists`; its board partitions and
`pick` from `mkChoices_root_spec`, `mkChoices_child_spec` and `mkChoices_pick_spec`. -/
theorem mkChoices_valid (X : Set (Set ℤ)) (R : Requirements) : (mkChoices X R).Valid X R where
  prot_spec a H _ hs := by
    have h := prot_exists X (R.N a) (R.s a) H hs
    show def_history_protected_set X (R.N a) (R.s a) H
      (if h : ∃ P, def_history_protected_set X (R.N a) (R.s a) H P then h.choose else ∅)
    rw [dif_pos h]; exact h.choose_spec
  root_spec := mkChoices_root_spec X R
  child_spec := mkChoices_child_spec X R
  pick_spec := mkChoices_pick_spec X R

/-- A defined guess is a critical vertex. -/
lemma guess_critical {R : Requirements} {ws : List ℤ} {Q : ℕ} (h : guess R ws = some Q) :
    Critical R {x | x ∈ ws} Q := by
  unfold guess at h
  split_ifs at h with hex
  obtain ⟨v, hv, hc⟩ := hex
  obtain rfl := Option.some_inj.1 h
  exact Nat.findGreatest_spec (by omega : v ≤ ws.length - 1) hc

/-- A defined guess is a vertex. -/
lemma guess_isV {R : Requirements} {ws : List ℤ} {Q : ℕ} (h : guess R ws = some Q) : R.isV Q :=
  (guess_critical h).1.1

/-- The output of a round is neither an input so far nor an earlier output. -/
lemma algStep_fresh {X : Set (Set ℤ)} (hX : LangClass X) {R : Requirements}
    (hlab : ∀ v, R.isV v → R.lab v ∈ X) {C : Choices} (hC : C.Valid X R)
    (ws prev : List ℤ) : algStep R C ws prev ∉ ws ∧ algStep R C ws prev ∉ prev := by
  set U : Set ℤ := {x | x ∈ ws ∨ x ∈ prev} with hU
  have hUfin : U.Finite := (ws.finite_toSet.union prev.finite_toSet).subset fun x hx => hx
  have key : ∃ S, (S \ U).Nonempty ∧ algStep R C ws prev = C.pick S U := by
    rcases hg : guess R ws with _ | Q
    · refine ⟨univ, (infinite_univ.sdiff hUfin).nonempty, ?_⟩
      simp only [algStep, hg, hU]
    · rcases hf : (vdata R C Q).anc.find? (fun v => decide ((pod R C ws v \ U).Nonempty))
        with _ | v
      · have hQ := (guess_critical hg).1.1
        refine ⟨R.lab Q, ((hX.infinite _ (hlab Q hQ)).sdiff hUfin).nonempty, ?_⟩
        simp only [algStep, hg, ← hU, hf]
      · have hv := List.find?_some hf
        refine ⟨pod R C ws v, of_decide_eq_true hv, ?_⟩
        simp only [algStep, hg, ← hU, hf]
  obtain ⟨S, hS, heq⟩ := key
  have := hC.pick_spec S U hS
  rw [heq]
  exact ⟨fun h => this.2 (Or.inl h), fun h => this.2 (Or.inr h)⟩

/-- Unfolding `algOutputs` on a nonempty list. -/
lemma algOutputs_eq (R : Requirements) (C : Choices) {ws : List ℤ} (h : ws ≠ []) :
    algOutputs R C ws =
      algOutputs R C ws.dropLast ++ [algStep R C ws (algOutputs R C ws.dropLast)] := by
  rw [algOutputs, dif_neg h]

/-- No rounds, no outputs. -/
lemma algOutputs_nil (R : Requirements) (C : Choices) : algOutputs R C [] = [] := by
  rw [algOutputs]; simp

/-- The inputs up to any round form a nonempty list. -/
lemma inputsUpTo_ne_nil (w : ℕ → ℤ) (t : ℕ) : inputsUpTo w t ≠ [] := by
  simp [inputsUpTo]

/-- Dropping the last input up to round `t + 1` gives the inputs up to round `t`. -/
lemma inputsUpTo_dropLast (w : ℕ → ℤ) (t : ℕ) :
    (inputsUpTo w (t + 1)).dropLast = inputsUpTo w t := by
  simp only [inputsUpTo]
  rw [List.ofFn_succ', List.concat_eq_append, List.dropLast_concat]
  rfl

/-- For `i ≤ t`, the input `w i` is among the inputs up to round `t`. -/
lemma mem_inputsUpTo (w : ℕ → ℤ) {i t : ℕ} (h : i ≤ t) : w i ∈ inputsUpTo w t := by
  simp only [inputsUpTo, List.mem_ofFn]
  exact ⟨⟨i, by omega⟩, rfl⟩

/-- The generator's output at round `t` is `algStep` on the inputs up to `t` and the earlier
outputs. -/
lemma algGen_out (R : Requirements) (C : Choices) (w : ℕ → ℤ) (t : ℕ) :
    (algGen R C).out w t =
      algStep R C (inputsUpTo w t) (algOutputs R C (inputsUpTo w t).dropLast) := by
  simp only [Generator.out, algGen]
  rw [algOutputs_eq R C (inputsUpTo_ne_nil w t)]
  simp

/-- For `s ≤ t`, the algorithm's outputs on the inputs up to round `s` are a prefix of its
outputs on the inputs up to round `t`. -/
lemma algOutputs_prefix (R : Requirements) (C : Choices) (w : ℕ → ℤ) {s t : ℕ} (h : s ≤ t) :
    algOutputs R C (inputsUpTo w s) <+: algOutputs R C (inputsUpTo w t) := by
  induction t, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ t hst ih =>
    refine ih.trans ?_
    rw [algOutputs_eq R C (inputsUpTo_ne_nil w (t + 1)), inputsUpTo_dropLast]
    exact List.prefix_append _ _

/-- The generator's output at round `s` is in the algorithm's output list for the inputs up to
`s`. -/
lemma out_mem_algOutputs (R : Requirements) (C : Choices) (w : ℕ → ℤ) (s : ℕ) :
    (algGen R C).out w s ∈ algOutputs R C (inputsUpTo w s) := by
  rw [algGen_out, algOutputs_eq R C (inputsUpTo_ne_nil w s)]
  simp

/-! ### The forest: shared facts on `buildForest` and `vdata` -/

/-- The forest built up to `n` has `n` entries. -/
lemma buildForest_length (R : Requirements) (C : Choices) : ∀ n, (buildForest R C n).length = n
  | 0 => rfl
  | n + 1 => by simp [buildForest, buildForest_length R C n]

/-- The `u`-th entry of the forest built up to `n` is the data of `u`. -/
lemma buildForest_getD (R : Requirements) (C : Choices) :
    ∀ n u, u < n → (buildForest R C n).getD u default = vdata R C u
  | 0, u, h => absurd h (Nat.not_lt_zero u)
  | n + 1, u, h => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | rfl
    · rw [buildForest, List.getD_append _ _ _ _ (by rw [buildForest_length]; exact h')]
      exact buildForest_getD R C n u h'
    · rw [buildForest, List.getD_append_right _ _ _ _ (by rw [buildForest_length])]
      simp [buildForest_length, vdata]

/-- An invariant of the parent scan. -/
lemma foldl_inv (R : Requirements) (P : ℕ → Prop) : ∀ (t : List ℕ) (p : ℕ), P p →
    (∀ p, ∀ u ∈ t, P p → P (if R.lab u ⊆ R.lab p then u else p)) →
    P (t.foldl (fun p u' => if R.lab u' ⊆ R.lab p then u' else p) p)
  | [], _, hp, _ => hp
  | b :: t, p, hp, h => by
    simp only [List.foldl_cons]
    exact foldl_inv R P t _ (h p b List.mem_cons_self hp)
      (fun p u hu => h p u (List.mem_cons_of_mem _ hu))

/-- The parent scan returns a member of its list (`foldl_inv` with `P := (· ∈ p :: t)`). -/
lemma foldl_mem (R : Requirements) (t : List ℕ) (p : ℕ) :
    t.foldl (fun p u' => if R.lab u' ⊆ R.lab p then u' else p) p ∈ p :: t :=
  foldl_inv R (· ∈ p :: t) t p List.mem_cons_self fun q u hu hq => by
    split_ifs
    · exact List.mem_cons_of_mem _ hu
    · exact hq

/-- The parent returned by the scan is a possible parent. -/
lemma scanParent_mem (R : Requirements) : ∀ (l : List ℕ) (u : ℕ), scanParent R l = some u → u ∈ l
  | [], u, h => by simp [scanParent] at h
  | a :: t, u, h => by
    simp only [scanParent, Option.some.injEq] at h
    subst h
    exact foldl_mem R t a

/-- The data of `v`: a root, or a child of a possible parent `p < v`. -/
lemma vdata_cases (R : Requirements) (C : Choices) (v : ℕ) :
    ((vdata R C v).parent = none ∧ (vdata R C v).anc = [v] ∧
      (vdata R C v).cuts = C.rootCuts v ∧ (vdata R C v).B = R.N v) ∨
    (∃ p, (vdata R C v).parent = some p ∧ p < v ∧ R.isV p ∧ R.lab v ⊆ R.lab p ∧
      (vdata R C p).P ⊆ R.lab v ∧ (vdata R C v).anc = (vdata R C p).anc ++ [v] ∧
      (vdata R C v).cuts = C.childCuts v p (vdata R C p).cuts (vdata R C p).B ∧
      (vdata R C v).B = R.N v + (vdata R C p).B - 1) := by
  simp only [vdata, processVertex, VData.parent, VData.anc, VData.cuts, VData.B]
  split
  · next h => exact Or.inl ⟨h, rfl, rfl, rfl⟩
  · next p h =>
    have hm := scanParent_mem R _ p h
    simp only [possibleParents, List.mem_filter, List.mem_range, decide_eq_true_eq] at hm
    obtain ⟨hpv, hpV, hsub, hP⟩ := hm
    rw [buildForest_getD R C v p hpv] at hP ⊢
    exact Or.inr ⟨p, h, hpv, hpV, hsub, hP, rfl, rfl, rfl⟩

/-- Ancestors of a vertex are vertices. -/
lemma isV_of_anc (R : Requirements) (C : Choices) :
    ∀ v, R.isV v → ∀ a ∈ (vdata R C v).anc, R.isV a := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hv a ha
    rcases vdata_cases R C v with ⟨-, h, -⟩ | ⟨p, -, hpv, hpV, -, -, h, -⟩
    · rw [h] at ha; simp at ha; subst ha; exact hv
    · rw [h] at ha
      rcases List.mem_append.1 ha with ha | ha
      · exact ih p hpv hpV a ha
      · simp at ha; subst ha; exact hv

end ConstructionAux

namespace ConstructionAux
/-- Obligation O3: valid choices exist for every vertex data. -/
theorem exists_valid_choices (X : Set (Set ℤ)) (R : Requirements) : ∃ C : Choices, C.Valid X R := by
  exact ⟨mkChoices X R, mkChoices_valid X R⟩

/-- Obligation O4: the constructed generator is admissible. -/
theorem algGen_admissible {X : Set (Set ℤ)} (hX : LangClass X) {R : Requirements}
    (hlab : ∀ v, R.isV v → R.lab v ∈ X) {C : Choices} (hC : C.Valid X R) :
    (algGen R C).Admissible := by
  intro w t
  have hfresh := algStep_fresh hX hlab hC (inputsUpTo w t)
    (algOutputs R C (inputsUpTo w t).dropLast)
  rw [← algGen_out] at hfresh
  refine ⟨fun i hi heq => hfresh.1 (heq ▸ mem_inputsUpTo w hi), fun s hs heq => ?_⟩
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  rw [inputsUpTo_dropLast] at hfresh
  apply hfresh.2
  rw [← heq]
  exact (algOutputs_prefix R C w (show s ≤ t' by omega)).subset (out_mem_algOutputs R C w s)
end ConstructionAux

end BanachDensity1D
