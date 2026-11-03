import BanachDensityHD.Trees

/-!
# Section 7 and Theorem 1.13: failure of simultaneous optimality

Kleinberg–Wei, *Characterizing Local Breadth in Language Generation*.
Historical source numbering is retained; current mappings are in the release registry.

-/

namespace BanachDensityHD

open Set Filter
open scoped Classical

/-! ## The family of §7.2, the strip-only family (Remark 3), the cells and tests of §7.3

The definitions of §7 stand first, so that every lemma of `SeparationAux` is stated in them. -/

/-- The plane `ℤ²` inside `ℤ^d` (`d ≥ 2`): `(x,y) ↦ (x, y, 0, …, 0)` (end of §7.4). -/
def emb2 (d : ℕ) (p : ℤ × ℤ) : Pt d :=
  fun i => if i.val = 0 then p.1 else if i.val = 1 then p.2 else 0

/-- The cell `C_{i,j} = (2i,2j) + {0,1}²`. -/
def cell (i j : ℕ) : Set (ℤ × ℤ) := {p | p.1 ∈ Icc (2 * (i : ℤ)) (2 * i + 1) ∧ p.2 ∈ Icc (2 * (j : ℤ)) (2 * j + 1)}

/-- The capped strip `V_{k,ℓ} = ({0,…,2k+1} × ℕ) ∪ {0,…,2ℓ+1}²`. -/
def cappedStrip (k ℓ : ℕ) : Set (ℤ × ℤ) :=
  {p | p.1 ∈ Icc 0 (2 * (k : ℤ) + 1) ∧ 0 ≤ p.2} ∪ {p | p.1 ∈ Icc 0 (2 * (ℓ : ℤ) + 1) ∧ p.2 ∈ Icc 0 (2 * (ℓ : ℤ) + 1)}

/-- A deletion rule `(i, m, r)`: delete the cells `C_{i, r + t m}`, `t ≥ 0`, of cell-column `i`. -/
def deleted (rule : ℕ × ℕ × ℕ) : Set (ℤ × ℤ) := ⋃ t : ℕ, cell rule.1 (rule.2.2 + t * rule.2.1)

/-- The family `𝒳` of §7.2 (planar version): the full grid `ℕ²` and every capped strip
`V_{k,ℓ}` (`1 ≤ k ≤ ℓ`) with finitely many deletion rules in cell-columns `1 ≤ i ≤ k`,
differences `m ≥ 1`. -/
def family7 : Set (Set (ℤ × ℤ)) :=
  {L | L = {p | 0 ≤ p.1 ∧ 0 ≤ p.2}} ∪
  {L | ∃ (k ℓ : ℕ) (rules : Finset (ℕ × ℕ × ℕ)), 1 ≤ k ∧ k ≤ ℓ ∧
      (∀ ρ ∈ rules, 1 ≤ ρ.1 ∧ ρ.1 ≤ k ∧ 1 ≤ ρ.2.1) ∧
      L = cappedStrip k ℓ \ ⋃ ρ ∈ rules, deleted ρ}

/-- The family of §7 in `ℤ^d`. -/
def family7d (d : ℕ) : Set (Set (Pt d)) := (fun L => emb2 d '' L) '' family7

/-- The distinguished language `K₀ = ℕ²` (embedded). -/
def K0d (d : ℕ) : Set (Pt d) := emb2 d '' {p | 0 ≤ p.1 ∧ 0 ≤ p.2}

/-- The strip-only family of Remark 3 (`sec:orientation`): the members of `𝒳` other than the
full grid (vertical capped strips with deletions) and their transposes (horizontal ones). -/
def stripFamily (d : ℕ) : Set (Set (Pt d)) :=
  (fun L => emb2 d '' L) '' ((family7 \ {{p | 0 ≤ p.1 ∧ 0 ≤ p.2}}) ∪
    (fun L => Prod.swap '' L) '' (family7 \ {{p | 0 ≤ p.1 ∧ 0 ≤ p.2}}))

/-- The point `a = (2i, 2j)` (lower left) of the cell `C_{i,j}`. -/
def cellA (i j : ℕ) : ℤ × ℤ := (2 * i, 2 * j)

/-- The point `b = (2i, 2j+1)` (upper left) of the cell `C_{i,j}`. -/
def cellB (i j : ℕ) : ℤ × ℤ := (2 * i, 2 * j + 1)

/-- The point `c = (2i+1, 2j)` (lower right) of the cell `C_{i,j}`. -/
def cellC (i j : ℕ) : ℤ × ℤ := (2 * i + 1, 2 * j)

/-- The cell `C_{i,j}` was forced in the run on `l` (Lemma 7.4, items 1–3): the adversary is the
first to touch the cell, by inputting its point `a` (nothing in the cell was input or output in an
earlier round); each of `a, b, c` is eventually an input or an output; and at most one of
`a, b, c` is an output. -/
def CellForced {d : ℕ} (G : Generator (Pt d)) (l : List (Pt d)) (i j : ℕ) : Prop :=
  (∃ t, ∃ ht : t < l.length, l.get ⟨t, ht⟩ = emb2 d (cellA i j) ∧
      ∀ t' < t, ∀ ht' : t' < l.length, l.get ⟨t', ht'⟩ ∉ emb2 d '' cell i j ∧
        G (l.take (t' + 1)) ∉ emb2 d '' cell i j) ∧
  (emb2 d (cellA i j) ∈ usedBy G l ∧ emb2 d (cellB i j) ∈ usedBy G l ∧
      emb2 d (cellC i j) ∈ usedBy G l) ∧
  (({emb2 d (cellA i j), emb2 d (cellB i j), emb2 d (cellC i j)} ∩ outsOf G l).ncard ≤ 1)

/-- The horizontal test of cell-row `j` over cell-columns `1,…,n`, embedded into dimension `d`.
For `d ≥ 2` it consists of the `2n` points `a, c` of cells `C_{1,j},…,C_{n,j}`; for `n ≥ 1`
this is the nonempty row rectangle `[2, 2n+1] × {2j}` of size `2n × 1` in the embedded plane.
In lower dimensions the embedding can identify points; at `n = 0` the test is empty. -/
def hTest (d n j : ℕ) : Set (Pt d) :=
  emb2 d '' {p | p.1 ∈ Icc 2 (2 * (n : ℤ) + 1) ∧ p.2 = 2 * (j : ℤ)}

namespace SeparationAux

/-! ## Finite runs of a generator -/

section Runs
variable {α : Type*}

theorem inputsUpTo_eq {w : ℕ → α} {l : List α} (hw : ∀ i (hi : i < l.length), w i = l[i])
    {t : ℕ} (ht : t < l.length) : inputsUpTo w t = l.take (t + 1) := by
  unfold inputsUpTo
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_take]; omega
  · intro i h1 h2
    simp only [List.getElem_ofFn, List.getElem_take]
    exact hw i (by simp only [List.length_ofFn] at h1; omega)

theorem inputsUpTo_take (w : ℕ → α) {r t : ℕ} (h : r ≤ t) :
    (inputsUpTo w t).take (r + 1) = inputsUpTo w r :=
  (inputsUpTo_eq (l := inputsUpTo w t)
    (fun _ _ => by simp only [inputsUpTo, List.getElem_ofFn])
    (by simp only [inputsUpTo, List.length_ofFn]; omega)).symm

theorem out_eq {G : Generator α} {w : ℕ → α} {l : List α}
    (hw : ∀ i (hi : i < l.length), w i = l[i]) {t : ℕ} (ht : t < l.length) :
    G.out w t = G (l.take (t + 1)) := by
  unfold Generator.out; rw [inputsUpTo_eq hw ht]

/-- Freshness on finite input lists. -/
theorem fresh_list {G : Generator α} (hG : G.Fresh) (l : List α) {t : ℕ} (ht : t < l.length) :
    G (l.take (t + 1)) ∉ l.take (t + 1) ∧ ∀ s < t, G (l.take (s + 1)) ≠ G (l.take (t + 1)) := by
  let w : ℕ → α := fun i => l.getD i (l[0]'(by omega))
  have hw : ∀ i (hi : i < l.length), w i = l[i] := fun i hi => List.getD_eq_getElem _ _ hi
  obtain ⟨h1, h2⟩ := hG w t
  rw [out_eq hw ht] at h1 h2
  refine ⟨fun hx => ?_, fun s hs => ?_⟩
  · obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
    simp only [List.length_take] at hi
    apply h1 i (by omega)
    rw [hw i (by omega), ← hix, List.getElem_take]
  · have := h2 s hs
    rwa [out_eq hw (by omega)] at this

theorem outsOf_mono (G : Generator α) (l r : List α) : outsOf G l ⊆ outsOf G (l ++ r) := by
  rintro x ⟨t, ht, rfl⟩
  exact ⟨t, by simp only [List.length_append]; omega, by
    rw [List.take_append_of_le_length (by omega)]⟩

theorem usedBy_mono (G : Generator α) (l r : List α) : usedBy G l ⊆ usedBy G (l ++ r) :=
  union_subset_union (fun _ hx => List.mem_append_left r hx) (outsOf_mono G l r)

theorem outsOf_finite (G : Generator α) (l : List α) : (outsOf G l).Finite := by
  refine ((Set.finite_lt_nat l.length).image (fun t => G (l.take (t + 1)))).subset ?_
  rintro x ⟨t, ht, rfl⟩
  exact ⟨t, ht, rfl⟩

theorem usedBy_finite (G : Generator α) (l : List α) : (usedBy G l).Finite :=
  (List.finite_toSet l).union (outsOf_finite G l)

/-- An output of a later round is not a point used earlier. -/
theorem out_not_used {G : Generator α} (hG : G.Fresh) (l r : List α) {t : ℕ}
    (ht : l.length ≤ t) (ht' : t < (l ++ r).length) :
    G ((l ++ r).take (t + 1)) ∉ usedBy G l := by
  obtain ⟨h1, h2⟩ := fresh_list hG (l ++ r) ht'
  rintro (hx | ⟨s, hs, hsx⟩)
  · apply h1
    obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
    have hi' : i < ((l ++ r).take (t + 1)).length := by simp; omega
    have : ((l ++ r).take (t + 1))[i] = l[i] := by
      simp [List.getElem_take, List.getElem_append_left hi]
    rw [← hix, ← this]; exact List.getElem_mem hi'
  · apply h2 s (by omega)
    rw [List.take_append_of_le_length (by omega), hsx]

/-- Every output of `l ++ r` is an output of `l` or of one of the new rounds (the rounds of `r`). -/
theorem outsOf_append (G : Generator α) (l r : List α) {x : α} (hx : x ∈ outsOf G (l ++ r)) :
    x ∈ outsOf G l ∨ ∃ j < r.length, G ((l ++ r).take (l.length + j + 1)) = x := by
  obtain ⟨t, ht, rfl⟩ := hx
  by_cases htl : t < l.length
  · left; exact ⟨t, htl, by rw [List.take_append_of_le_length (by omega)]⟩
  · right
    refine ⟨t - l.length, by simp only [List.length_append] at ht; omega, ?_⟩
    congr 2; omega

/-- A used point output on `l ++ r` was already output on `l`. -/
theorem outs_used_sub {G : Generator α} (hG : G.Fresh) (l r : List α) {x : α}
    (hx : x ∈ outsOf G (l ++ r)) (hxu : x ∈ usedBy G l) : x ∈ outsOf G l := by
  rcases outsOf_append G l r hx with h | ⟨j, hj, rfl⟩
  · exact h
  · exact absurd hxu (out_not_used hG l r (by omega) (by simp only [List.length_append]; omega))

/-- Sealing: a point used in `l` is output on the limit only if it was output on `l`. -/
theorem sealed {G : Generator α} (hG : G.Fresh) {w : ℕ → α} {l : List α}
    (hw : ∀ i (hi : i < l.length), w i = l[i]) {x : α} (hx : x ∈ G.outputSet w)
    (hxu : x ∈ usedBy G l) : x ∈ outsOf G l := by
  obtain ⟨t, rfl⟩ := hx
  by_cases ht : t < l.length
  · exact ⟨t, ht, (out_eq hw ht).symm⟩
  · exfalso
    obtain ⟨h1, h2⟩ := hG w t
    rcases hxu with hx | ⟨s, hs, hsx⟩
    · obtain ⟨i, hi, hix⟩ := List.getElem_of_mem (show G.out w t ∈ l from hx)
      apply h1 i (by omega)
      rw [hw i hi, hix]
    · apply h2 s (by omega)
      rw [out_eq hw hs, hsx]

/-- On the limit, the outputs in a set finished at `l` are those output on `l`. -/
theorem outputSet_inter_eq {G : Generator α} (hG : G.Fresh) {w : ℕ → α} {l : List α}
    (hw : ∀ i (hi : i < l.length), w i = l[i]) {A : Set α} (hA : A ⊆ usedBy G l) :
    G.outputSet w ∩ A = outsOf G l ∩ A := by
  ext x
  refine ⟨fun h => ⟨sealed hG hw h.1 (hA h.2), h.2⟩, fun h => ⟨?_, h.2⟩⟩
  obtain ⟨t, ht, hx⟩ := h.1
  exact ⟨t, by rw [out_eq hw ht, hx]⟩

/-! ### Limits of increasing histories -/

theorem limit_exists (hs : ℕ → List α) (hmono : ∀ k, ∃ r, hs (k + 1) = hs k ++ r)
    (hlen : ∀ k, k ≤ (hs k).length) :
    ∃ w : ℕ → α, (∀ k i (hi : i < (hs k).length), w i = (hs k)[i]) ∧
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

/-- The first point of the enumeration `e` not in `l` (or `e 0` if there is none). -/
noncomputable def nextPt (e : ℕ → α) (l : List α) : α :=
  if h : ∃ k, e k ∉ l then e (Nat.find h) else e 0

theorem exists_not_mem {L : Set α} (hL : L.Infinite) {e : ℕ → α} (he : range e = L)
    (l : List α) : ∃ k, e k ∉ l := by
  by_contra h
  push Not at h
  apply hL
  refine (List.finite_toSet l).subset ?_
  rw [← he]; rintro _ ⟨k, rfl⟩; exact h k

theorem nextPt_not_mem {L : Set α} (hL : L.Infinite) {e : ℕ → α} (he : range e = L)
    (l : List α) : nextPt e l ∉ l := by
  have h := exists_not_mem hL he l
  unfold nextPt; rw [dif_pos h]; exact Nat.find_spec h

theorem nextPt_mem {L : Set α} {e : ℕ → α} (he : range e = L) (l : List α) : nextPt e l ∈ L := by
  unfold nextPt; split_ifs <;> (rw [← he]; exact mem_range_self _)

theorem nextPt_eq_of (e : ℕ → α) (l : List α) (k : ℕ) (hk : e k ∉ l)
    (hmin : ∀ i < k, e i ∈ l) : nextPt e l = e k := by
  have hex : ∃ k, e k ∉ l := ⟨k, hk⟩
  unfold nextPt
  rw [dif_pos hex]
  congr 1
  refine le_antisymm (Nat.find_min' hex hk) ?_
  by_contra hlt
  push Not at hlt
  exact Nat.find_spec hex (hmin _ hlt)

/-- **Staged enumerations.** Starting from `xs ⊆ L`, append `nextPt e` and then a
stage-dependent finite extension inside `L`. `nextPt` selects the first not-yet-input point
of `e` if one exists, and defaults to `e 0` when exhausted, allowing repetitions. The limit
is a full enumeration of `L` agreeing with every stage, without an infinitude premise. -/
theorem staged {L : Set α} {e : ℕ → α} (he : range e = L) (xs : List α)
    (hxs : ∀ x ∈ xs, x ∈ L) (step : ℕ → List α → List α)
    (hstep : ∀ k l, (∀ x ∈ l, x ∈ L) → ∀ x ∈ step k l, x ∈ L) :
    ∃ (w : ℕ → α) (hs : ℕ → List α), IsFullEnumeration w L ∧ hs 0 = xs ∧
      (∀ k, hs (k + 1) = (hs k ++ [nextPt e (hs k)]) ++ step k (hs k ++ [nextPt e (hs k)])) ∧
      (∀ k i (hi : i < (hs k).length), w i = (hs k)[i]) ∧ (∀ k, ∀ x ∈ hs k, x ∈ L) ∧
      (∀ k, k ≤ (hs k).length) := by
  let hs : ℕ → List α := fun k => Nat.rec xs (fun k l =>
    (l ++ [nextPt e l]) ++ step k (l ++ [nextPt e l])) k
  have hs_succ : ∀ k, hs (k + 1) = (hs k ++ [nextPt e (hs k)]) ++
      step k (hs k ++ [nextPt e (hs k)]) := fun k => rfl
  have hsL : ∀ k, ∀ x ∈ hs k, x ∈ L := by
    intro k
    induction k with
    | zero => exact hxs
    | succ k ih =>
      rw [hs_succ]
      have h1 : ∀ x ∈ hs k ++ [nextPt e (hs k)], x ∈ L := by
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact ih x hx
        · rw [List.mem_singleton.1 hx]; exact nextPt_mem he _
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact h1 x hx
      · exact hstep k _ h1 x hx
  have hlen : ∀ k, k ≤ (hs k).length := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [hs_succ]; simp only [List.length_append, List.length_singleton]; omega
  obtain ⟨w, hw, hrange⟩ := limit_exists hs
    (fun k => ⟨_, by rw [hs_succ, List.append_assoc]⟩) hlen
  -- every `e i` with `i < k` is input by stage `k`
  have hcov : ∀ k, ∀ i < k, e i ∈ hs k := by
    intro k
    induction k with
    | zero => intro i hi; omega
    | succ k ih =>
      intro i hi
      have hsub : hs k ⊆ hs (k + 1) := by
        rw [hs_succ, List.append_assoc]; exact List.subset_append_left _ _
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact hsub (ih i hi)
      · rcases em (e i ∈ hs i) with hin | hin
        · exact hsub hin
        · have : nextPt e (hs i) = e i := nextPt_eq_of e _ i hin ih
          rw [hs_succ, ← this]; simp
  refine ⟨w, hs, ?_, rfl, hs_succ, hw, hsL, hlen⟩
  ext x
  rw [hrange]
  constructor
  · rintro ⟨k, hk⟩; exact hsL k x hk
  · intro hx
    rw [← he] at hx
    obtain ⟨i, rfl⟩ := hx
    exact ⟨i + 1, hcov (i + 1) i (by omega)⟩

/-- **Bad attempts cannot repeat forever.** If from every admissible history inside `L` some
continuation inside `L` produces an output outside `L`, then repeating such continuations,
interleaved with the enumeration of `L`, gives a full enumeration of `L` with infinitely many
outputs outside `L`: impossible for a generator eventually valid on `L`. -/
theorem no_bad_forever [Countable α] {G : Generator α} {L : Set α} (hL : L.Infinite)
    (hval : ∀ w, IsFullEnumeration w L → G.EventuallyValid w L)
    (Q : List α → Prop) (xs : List α) (hxs : ∀ x ∈ xs, x ∈ L) (hQ0 : Q xs)
    (hQnext : ∀ l x, Q l → x ∉ l → Q (l ++ [x]))
    (hbad : ∀ l, Q l → (∀ x ∈ l, x ∈ L) → ∃ cont : List α, (∀ x ∈ cont, x ∈ L) ∧
      Q (l ++ cont) ∧ ∃ j < cont.length, G ((l ++ cont).take (l.length + j + 1)) ∉ L) :
    False := by
  obtain ⟨e, he⟩ : ∃ e : ℕ → α, range e = L := by
    obtain ⟨e, he⟩ := (Set.to_countable L).exists_eq_range hL.nonempty
    exact ⟨e, he.symm⟩
  let step : ℕ → List α → List α := fun _ l =>
    if h : Q l ∧ ∀ x ∈ l, x ∈ L then (hbad l h.1 h.2).choose else []
  have hstep : ∀ k l, (∀ x ∈ l, x ∈ L) → ∀ x ∈ step k l, x ∈ L := by
    intro k l hl x hx
    simp only [step] at hx
    split_ifs at hx with h
    · exact (hbad l h.1 h.2).choose_spec.1 x hx
    · simp at hx
  obtain ⟨w, hs, hfull, hs0, hs_succ, hw, hsL, hlen⟩ := staged he xs hxs step hstep
  have hQ : ∀ k, Q (hs k) := by
    intro k
    induction k with
    | zero => rw [hs0]; exact hQ0
    | succ k ih =>
      have h1 := hQnext _ _ ih (nextPt_not_mem hL he (hs k))
      have h2 : ∀ x ∈ hs k ++ [nextPt e (hs k)], x ∈ L := by
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hsL k x hx
        · rw [List.mem_singleton.1 hx]; exact nextPt_mem he _
      rw [hs_succ]
      simp only [step, dif_pos (And.intro h1 h2)]
      exact (hbad _ h1 h2).choose_spec.2.1
  refine (Set.infinite_of_forall_exists_gt ?_) (hval w hfull)
  intro N
  set l := hs N ++ [nextPt e (hs N)] with hl
  have h1 := hQnext _ _ (hQ N) (nextPt_not_mem hL he (hs N))
  have h2 : ∀ x ∈ l, x ∈ L := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hsL N x hx
    · rw [List.mem_singleton.1 hx]; exact nextPt_mem he _
  have hsN : hs (N + 1) = l ++ (hbad l h1 h2).choose := by
    rw [hs_succ]; show l ++ step N l = _; simp only [step]; rw [dif_pos ⟨h1, h2⟩]
  obtain ⟨cont, hsN, j, hj, hbadj⟩ : ∃ cont, hs (N + 1) = l ++ cont ∧
      ∃ j < cont.length, G ((l ++ cont).take (l.length + j + 1)) ∉ L :=
    ⟨_, hsN, (hbad l h1 h2).choose_spec.2.2⟩
  refine ⟨l.length + j, ?_, ?_⟩
  · show G.out w (l.length + j) ∉ L
    have hlt : l.length + j < (hs (N + 1)).length := by
      rw [hsN]; have := @List.length_append _ l cont; omega
    rw [out_eq (hw (N + 1)) hlt, hsN]
    exact hbadj
  · have := hlen N
    simp only [hl, List.length_append, List.length_singleton]; omega

/-- **Validity commitment** (strong form): from any finite history inside `L`, a finite extension
inside `L` commits the generator to `L` on every further continuation inside `L` (repetitions
allowed). -/
theorem commit_strong [Countable α] {G : Generator α} {L : Set α} (hL : L.Infinite)
    (hval : ∀ w, IsFullEnumeration w L → G.EventuallyValid w L)
    (xs : List α) (hxL : ∀ x ∈ xs, x ∈ L) :
    ∃ ext : List α, (∀ x ∈ ext, x ∈ L) ∧
      ∀ cont : List α, (∀ x ∈ cont, x ∈ L) →
        ∀ j < cont.length, G ((xs ++ ext ++ cont).take ((xs ++ ext).length + j + 1)) ∈ L := by
  by_contra hcon
  push Not at hcon
  refine no_bad_forever hL hval (fun l => xs <+: l) xs hxL (List.prefix_refl xs)
    (fun l x h _ => h.trans (List.prefix_append l [x])) ?_
  intro l hl hlL
  obtain ⟨ext, rfl⟩ := hl
  obtain ⟨cont, hcont, j, hj, hbad⟩ := hcon ext (fun x hx => hlL x (List.mem_append_right _ hx))
  exact ⟨cont, hcont, (List.prefix_append _ _).trans (List.prefix_append _ _), j, hj, hbad⟩

end Runs

end SeparationAux

/-! ## Lemma 7.3: validity commitment -/

/-- **Lemma 7.3** (`lem:validity-commitment`), in the lattice setting of the paper (`L ⊆ ℤ^d`
infinite, hence countably infinite, so full enumerations exist and the hypothesis is not
vacuous — over an uncountable type the generalized statement would be false): a generator
eventually valid on `L`, after any
finite sequence of distinct inputs from `L`, is committed to `L` by a finite continuation of
distinct inputs from `L`: every later output, on every continuation of distinct new points of `L`,
lies in `L`. -/
theorem lem_validity_commitment {d : ℕ} (G : Generator (Pt d)) (L : Set (Pt d)) (hL : L.Infinite)
    (hval : ∀ w, IsFullEnumeration w L → G.EventuallyValid w L)
    (xs : List (Pt d)) (hxs : xs.Nodup) (hxL : ∀ x ∈ xs, x ∈ L) :
    ∃ ext : List (Pt d), (xs ++ ext).Nodup ∧ (∀ x ∈ ext, x ∈ L) ∧
      ∀ cont : List (Pt d), (xs ++ ext ++ cont).Nodup → (∀ x ∈ cont, x ∈ L) →
        ∀ j < cont.length, G ((xs ++ ext ++ cont).take ((xs ++ ext).length + j + 1)) ∈ L := by
  by_contra hcon
  push Not at hcon
  refine SeparationAux.no_bad_forever hL hval (fun l => xs <+: l ∧ l.Nodup) xs hxL ⟨List.prefix_refl xs, hxs⟩
    (fun l x h hx => ⟨h.1.trans (List.prefix_append l [x]),
      List.nodup_append.2 ⟨h.2, List.nodup_singleton x,
        fun a ha b hb hab => hx (by rw [List.mem_singleton.1 hb] at hab; exact hab ▸ ha)⟩⟩) ?_
  intro l hl hlL
  obtain ⟨⟨ext, rfl⟩, hnd⟩ := hl
  obtain ⟨cont, hnd', hcont, j, hj, hbad⟩ :=
    hcon ext hnd (fun x hx => hlL x (List.mem_append_right _ hx))
  exact ⟨cont, hcont, ⟨(List.prefix_append _ _).trans (List.prefix_append _ _), hnd'⟩, j, hj, hbad⟩

namespace SeparationAux


/-! ## Planar geometry -/

/-- The quadrant `ℕ²`. -/
def quad : Set (ℤ × ℤ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2}

theorem emb2_inj {d : ℕ} (hd : 2 ≤ d) : Function.Injective (emb2 d) := by
  intro p q h
  have h0 := congrFun h ⟨0, by omega⟩
  have h1 := congrFun h ⟨1, by omega⟩
  simp only [emb2] at h0 h1
  simp at h0 h1
  exact Prod.ext h0 h1

/-- The coordinate `i` of a point (`0` if `i ≥ d`). -/
def crd {d : ℕ} (i : ℕ) (v : Pt d) : ℤ := if h : i < d then v ⟨i, h⟩ else 0

theorem crd_emb2_0 {d : ℕ} (hd : 2 ≤ d) (p : ℤ × ℤ) : crd 0 (emb2 d p) = p.1 := by
  simp [crd, emb2, show 0 < d by omega]

theorem crd_emb2_1 {d : ℕ} (hd : 2 ≤ d) (p : ℤ × ℤ) : crd 1 (emb2 d p) = p.2 := by
  simp [crd, emb2, show 1 < d by omega]

/-- The planar projection. -/
def proj {d : ℕ} (v : Pt d) : ℤ × ℤ := (crd 0 v, crd 1 v)

theorem proj_emb2 {d : ℕ} (hd : 2 ≤ d) (p : ℤ × ℤ) : proj (emb2 d p) = p := by
  simp [proj, crd_emb2_0 hd, crd_emb2_1 hd]

/-- Membership of an embedded point in a rectangle. -/
theorem emb2_mem_pts {d : ℕ} (hd : 2 ≤ d) (R : Rect d) (p : ℤ × ℤ) :
    emb2 d p ∈ R.pts ↔ (∀ i : Fin d, 2 ≤ i.val → R.lo i ≤ 0 ∧ 0 ≤ R.hi i) ∧
      crd 0 R.lo ≤ p.1 ∧ p.1 ≤ crd 0 R.hi ∧ crd 1 R.lo ≤ p.2 ∧ p.2 ≤ crd 1 R.hi := by
  have h0 : 0 < d := by omega
  have h1 : 1 < d := by omega
  simp only [Rect.pts, mem_Icc, Pi.le_def, crd, dif_pos h0, dif_pos h1]
  constructor
  · rintro ⟨hl, hh⟩
    refine ⟨fun i hi => ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · have := hl i; simp only [emb2] at this; rwa [if_neg (by omega), if_neg (by omega)] at this
    · have := hh i; simp only [emb2] at this; rwa [if_neg (by omega), if_neg (by omega)] at this
    · simpa [emb2] using hl ⟨0, h0⟩
    · simpa [emb2] using hh ⟨0, h0⟩
    · simpa [emb2] using hl ⟨1, h1⟩
    · simpa [emb2] using hh ⟨1, h1⟩
  · rintro ⟨hz, ha, hb, hc, he⟩
    refine ⟨fun i => ?_, fun i => ?_⟩
    · simp only [emb2]
      split_ifs with i0 i1
      · have : i = ⟨0, h0⟩ := Fin.ext i0
        subst this; exact ha
      · have : i = ⟨1, h1⟩ := Fin.ext i1
        subst this; exact hc
      · exact (hz i (by omega)).1
    · simp only [emb2]
      split_ifs with i0 i1
      · have : i = ⟨0, h0⟩ := Fin.ext i0
        subst this; exact hb
      · have : i = ⟨1, h1⟩ := Fin.ext i1
        subst this; exact he
      · exact (hz i (by omega)).2

/-- A planar box `[a,b] × [c,e]`. -/
def box (a b c e : ℤ) : Set (ℤ × ℤ) := {p | a ≤ p.1 ∧ p.1 ≤ b ∧ c ≤ p.2 ∧ p.2 ≤ e}

theorem box_eq (a b c e : ℤ) :
    box a b c e = ((Finset.Icc a b ×ˢ Finset.Icc c e : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
  ext p
  simp only [box, Finset.coe_product, mem_prod, Finset.coe_Icc, mem_Icc, mem_setOf_eq]
  tauto

theorem box_finite (a b c e : ℤ) : (box a b c e).Finite := by
  rw [box_eq]; exact Finset.finite_toSet _

theorem ncard_box (a b c e : ℤ) : (box a b c e).ncard = (b + 1 - a).toNat * (e + 1 - c).toNat := by
  rw [box_eq, ncard_coe_finset, Finset.card_product, Int.card_Icc, Int.card_Icc]

/-- The preimage of a rectangle in the plane is a box (or empty). -/
theorem preimage_pts {d : ℕ} (hd : 2 ≤ d) (R : Rect d) :
    ∃ (Z : Prop) (a b c e : ℤ), emb2 d ⁻¹' R.pts = {p | Z ∧ p ∈ box a b c e} :=
  ⟨(∀ i : Fin d, 2 ≤ i.val → R.lo i ≤ 0 ∧ 0 ≤ R.hi i), crd 0 R.lo, crd 0 R.hi, crd 1 R.lo,
    crd 1 R.hi, by ext p; simp only [mem_preimage, emb2_mem_pts hd, box, mem_setOf_eq]⟩

/-- The rectangle with planar corners `(a,c)` and `(b,e)`. -/
def prect (d : ℕ) (a b c e : ℤ) (hab : a ≤ b) (hce : c ≤ e) : Rect d :=
  Rect.mk (emb2 d (a, c)) (emb2 d (b, e)) (by
    intro i; simp only [emb2]; split_ifs <;> omega)

theorem prect_pts {d : ℕ} (hd : 2 ≤ d) {a b c e : ℤ} (hab : a ≤ b) (hce : c ≤ e) :
    (prect d a b c e hab hce).pts = emb2 d '' box a b c e := by
  ext v
  constructor
  · intro hv
    have hv' : v = emb2 d (crd 0 v, crd 1 v) := by
      funext i
      by_cases i0 : i.val = 0
      · have : i = ⟨0, by omega⟩ := Fin.ext i0
        rw [this]; simp [emb2, crd, show 0 < d by omega]
      · by_cases i1 : i.val = 1
        · have : i = ⟨1, by omega⟩ := Fin.ext i1
          rw [this]; simp [emb2, crd, show 1 < d by omega]
        · have h1 := hv.1 i; have h2 := hv.2 i
          simp only [prect, Rect.lo, Rect.hi, emb2, if_neg i0, if_neg i1] at h1 h2
          simp only [emb2, if_neg i0, if_neg i1]; omega
    rw [hv'] at hv ⊢
    refine ⟨_, ?_, rfl⟩
    rw [emb2_mem_pts hd] at hv
    obtain ⟨-, h1, h2, h3, h4⟩ := hv
    simp only [prect, Rect.lo, Rect.hi, crd_emb2_0 hd, crd_emb2_1 hd] at h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨p, hp, rfl⟩
    rw [emb2_mem_pts hd]
    refine ⟨fun i hi => ?_, ?_⟩
    · simp only [prect, Rect.lo, Rect.hi, emb2, if_neg (show i.val ≠ 0 by omega),
        if_neg (show i.val ≠ 1 by omega)]; simp
    · simp only [prect, Rect.lo, Rect.hi, crd_emb2_0 hd, crd_emb2_1 hd]
      exact hp

/-- Equality of totalized `Set.ncard` values under the injective embedding `emb2 d`.
For finite sets this counts points inside the embedded set. Infinite corresponding sets
both have totalized natural cardinality zero; finiteness is not assumed here. -/
theorem ncard_inter_emb {d : ℕ} (hd : 2 ≤ d) (A : Set (Pt d)) (Lp : Set (ℤ × ℤ)) :
    (A ∩ emb2 d '' Lp).ncard = (emb2 d ⁻¹' A ∩ Lp).ncard := by
  rw [inter_comm, ← Set.image_inter_preimage, inter_comm,
    ncard_image_of_injective _ (emb2_inj hd)]

theorem prect_vol {d : ℕ} (hd : 2 ≤ d) {a b c e : ℤ} (hab : a ≤ b) (hce : c ≤ e) :
    (prect d a b c e hab hce).vol = (b + 1 - a).toNat * (e + 1 - c).toNat := by
  rw [Rect.vol, prect_pts hd, ncard_image_of_injective _ (emb2_inj hd), ncard_box]

/-! ## Cell saturation and the family -/

/-- Membership depends only on the cell. -/
def Sat (S : Set (ℤ × ℤ)) : Prop :=
  ∀ p q : ℤ × ℤ, p.1 / 2 = q.1 / 2 → p.2 / 2 = q.2 / 2 → p ∈ S → q ∈ S

theorem sat_quad : Sat quad := by
  intro p q h1 h2 hp; simp only [quad, mem_setOf_eq] at *; omega

theorem sat_cell (i j : ℕ) : Sat (cell i j) := by
  intro p q h1 h2 hp; simp only [cell, mem_setOf_eq, mem_Icc] at *; omega

theorem sat_capped (k ℓ : ℕ) : Sat (cappedStrip k ℓ) := by
  intro p q h1 h2 hp; simp only [cappedStrip, mem_union, mem_setOf_eq, mem_Icc] at *; omega

theorem sat_compl {S : Set (ℤ × ℤ)} (h : Sat S) : Sat Sᶜ :=
  fun p q h1 h2 hp hq => hp (h q p h1.symm h2.symm hq)

theorem sat_iUnion {ι : Sort*} {S : ι → Set (ℤ × ℤ)} (h : ∀ i, Sat (S i)) : Sat (⋃ i, S i) := by
  intro p q h1 h2 hp
  obtain ⟨i, hi⟩ := mem_iUnion.1 hp
  exact mem_iUnion.2 ⟨i, h i p q h1 h2 hi⟩

theorem sat_inter {S T : Set (ℤ × ℤ)} (hS : Sat S) (hT : Sat T) : Sat (S ∩ T) :=
  fun p q h1 h2 hp => ⟨hS p q h1 h2 hp.1, hT p q h1 h2 hp.2⟩

theorem sat_deleted (ρ : ℕ × ℕ × ℕ) : Sat (deleted ρ) := sat_iUnion fun _ => sat_cell _ _

theorem sat_strip (k ℓ : ℕ) (rules : Finset (ℕ × ℕ × ℕ)) :
    Sat (cappedStrip k ℓ \ ⋃ ρ ∈ rules, deleted ρ) :=
  sat_inter (sat_capped k ℓ) (sat_compl (sat_iUnion fun ρ => sat_iUnion fun _ => sat_deleted ρ))

theorem sat_family {L : Set (ℤ × ℤ)} (hL : L ∈ family7) : Sat L := by
  rcases hL with rfl | ⟨k, ℓ, rules, -, -, -, rfl⟩
  · exact sat_quad
  · exact sat_strip k ℓ rules

theorem family_sub_quad {L : Set (ℤ × ℤ)} (hL : L ∈ family7) : L ⊆ quad := by
  rcases hL with rfl | ⟨k, ℓ, rules, -, -, -, rfl⟩
  · exact le_rfl
  · rintro p ⟨hp, -⟩
    simp only [cappedStrip, mem_union, mem_setOf_eq, mem_Icc] at hp
    simp only [quad, mem_setOf_eq]; omega

theorem not_mem_deleted_col0 {ρ : ℕ × ℕ × ℕ} (hρ : 1 ≤ ρ.1) {p : ℤ × ℤ} (hp : p.1 ≤ 1) :
    p ∉ deleted ρ := by
  intro h
  obtain ⟨t, ht⟩ := mem_iUnion.1 h
  simp only [cell, mem_setOf_eq, mem_Icc] at ht
  have : (1 : ℤ) ≤ ρ.1 := by exact_mod_cast hρ
  omega

/-- Cell-column `0` lies in every member of the family. -/
theorem col0_mem {L : Set (ℤ × ℤ)} (hL : L ∈ family7) {p : ℤ × ℤ} (h1 : 0 ≤ p.1) (h1' : p.1 ≤ 1)
    (h2 : 0 ≤ p.2) : p ∈ L := by
  rcases hL with rfl | ⟨k, ℓ, rules, hk, -, hrules, rfl⟩
  · exact ⟨h1, h2⟩
  · refine ⟨Or.inl ⟨⟨h1, by omega⟩, h2⟩, ?_⟩
    simp only [mem_iUnion, not_exists]
    intro ρ hρ
    exact not_mem_deleted_col0 (hrules ρ hρ).1 h1'

/-- Members other than the quadrant have bounded width. -/
theorem strip_width {L : Set (ℤ × ℤ)} (hL : L ∈ family7) (hne : L ≠ quad) :
    ∃ W : ℤ, ∀ p ∈ L, 0 ≤ p.1 ∧ p.1 ≤ W := by
  rcases hL with h | ⟨k, ℓ, rules, -, hkℓ, -, rfl⟩
  · exact absurd h hne
  · refine ⟨2 * ℓ + 1, fun p hp => ?_⟩
    have := hp.1
    simp only [cappedStrip, mem_union, mem_setOf_eq, mem_Icc] at this
    have : (k : ℤ) ≤ ℓ := by exact_mod_cast hkℓ
    omega

theorem family7_countable : family7.Countable := by
  have : family7 ⊆ {quad} ∪ range (fun x : ℕ × ℕ × Finset (ℕ × ℕ × ℕ) =>
      cappedStrip x.1 x.2.1 \ ⋃ ρ ∈ x.2.2, deleted ρ) := by
    rintro L (h | ⟨k, ℓ, rules, -, -, -, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨(k, ℓ, rules), rfl⟩
  exact ((countable_singleton _).union (countable_range _)).mono this

theorem col0_infinite {L : Set (ℤ × ℤ)} (hL : L ∈ family7) : L.Infinite := by
  have hinj : Function.Injective (fun n : ℕ => ((0 : ℤ), (n : ℤ))) := by
    intro a b h; simpa using h
  refine Set.infinite_of_injective_forall_mem hinj fun n => col0_mem hL le_rfl (by norm_num)
    (by positivity)

theorem langClass_family7d {d : ℕ} (hd : 2 ≤ d) : LangClass (family7d d) where
  nonempty := ⟨_, quad, Or.inl rfl, rfl⟩
  countable := family7_countable.image _
  infinite := by
    rintro L ⟨Lp, hLp, rfl⟩
    exact (col0_infinite hLp).image (emb2_inj hd).injOn

theorem quad_mem : quad ∈ family7 := Or.inl rfl

theorem K0d_eq (d : ℕ) : K0d d = emb2 d '' quad := rfl

theorem K0d_mem (d : ℕ) : K0d d ∈ family7d d := ⟨quad, quad_mem, rfl⟩

theorem strip_mem {k ℓ : ℕ} (hk : 1 ≤ k) (hkℓ : k ≤ ℓ) : cappedStrip k ℓ ∈ family7 :=
  Or.inr ⟨k, ℓ, ∅, hk, hkℓ, by simp, by simp⟩

theorem strip_ne_quad (k ℓ : ℕ) : cappedStrip k ℓ ≠ quad := by
  intro h
  have : ((2 * (k : ℤ) + 2 * ℓ + 2, 0) : ℤ × ℤ) ∈ quad := ⟨by positivity, le_rfl⟩
  rw [← h] at this
  simp only [cappedStrip, mem_union, mem_setOf_eq, mem_Icc] at this
  omega

theorem strip_sub_quad (k ℓ : ℕ) : cappedStrip k ℓ ⊆ quad := by
  intro p hp
  simp only [cappedStrip, mem_union, mem_setOf_eq, mem_Icc] at hp
  simp only [quad, mem_setOf_eq]; omega


/-! ## Bounds for `δ_h` -/

theorem threshold_vol {h : ℕ → ℝ} (hh : IsThreshold h) {d : ℕ} (R : Rect d) : h 1 ≤ h R.vol :=
  hh.2.1 (mem_Ici.2 le_rfl) (mem_Ici.2 (BasicAux.rect_vol_pos R)) (BasicAux.rect_vol_pos R)

/-- Upper bound for `δ_h` from tests at every level `k ∈ ℕ`. -/
theorem deltaH_le_of_tests {d : ℕ} {h : ℕ → ℝ} (hh : IsThreshold h) (O L : Set (Pt d)) (β : ℝ)
    (H : ∀ k : ℕ, ∃ R : Rect d, (k : ℝ) * h R.vol ≤ mass L R ∧
      ((O ∩ L ∩ R.pts).ncard : ℝ) / mass L R ≤ β) : deltaH h O L ≤ β := by
  have ht := (deltaH_tendsto h hh.1 O L).1
  refine le_of_tendsto' ht fun s => ?_
  obtain ⟨R, hR, hβ⟩ := H ⌈s⌉₊
  have hpos := hh.1 _ (BasicAux.rect_vol_pos R)
  have hsR : s * h R.vol ≤ mass L R :=
    le_trans (mul_le_mul_of_nonneg_right (Nat.le_ceil s) hpos.le) hR
  have hmem : ((O ∩ L ∩ R.pts).ncard : ℝ) / mass L R ∈ BasicAux.tests h O L s := ⟨R, hsR, rfl⟩
  rw [BasicAux.testInf_eq, if_pos ⟨_, hmem⟩]
  exact (csInf_le (BasicAux.tests_bdd h O L s) hmem).trans hβ

/-- Lower bound for `δ_h` from a counting bound with an additive error. -/
theorem deltaH_ge_of_count {d : ℕ} {h : ℕ → ℝ} (hh : IsThreshold h) (O L : Set (Pt d))
    (β C : ℝ) (hβ : β ≤ 1) (H : ∀ R : Rect d, β * mass L R - C ≤ (O ∩ L ∩ R.pts).ncard) :
    β ≤ deltaH h O L := by
  have ht := (deltaH_tendsto h hh.1 O L).1
  have hmono := BasicAux.testInf_mono h hh.1 O L
  have h1 : 0 < h 1 := hh.1 1 le_rfl
  refine le_of_forall_sub_le fun ε hε => ?_
  set s : ℝ := |C| / (ε * h 1) + 1 with hs
  have hs0 : 0 < s := by positivity
  refine le_trans ?_ (hmono.ge_of_tendsto ht s)
  rw [BasicAux.testInf_eq]
  split_ifs with hne
  · refine le_csInf hne ?_
    rintro _ ⟨R, hR, rfl⟩
    have hvol := threshold_vol hh R
    have hm : s * h 1 ≤ mass L R := le_trans (mul_le_mul_of_nonneg_left hvol hs0.le) hR
    have hmpos : 0 < (mass L R : ℝ) := lt_of_lt_of_le (by positivity) hm
    rw [le_div_iff₀ hmpos]
    have e1 : ε * (s * h 1) = |C| + ε * h 1 := by
      rw [hs]; field_simp
    have e2 : |C| ≤ ε * mass L R := by
      nlinarith [mul_le_mul_of_nonneg_left hm hε.le, mul_pos hε h1]
    have e3 : (β - ε) * mass L R = β * mass L R - ε * mass L R := by ring
    rw [e3]
    linarith [H R, le_abs_self C]
  · linarith

/-! ## Counting pairs -/

/-- If every pair `{p, π p}` inside `S` away from `E` meets `O`, the exported conclusion is
`|S| ≤ 2|O ∩ S| + 2|E| + |{p ∈ S : π p ∉ S}|`. The bound on internal partners,
`|{p ∈ S : π p ∈ S}| ≤ 2|O ∩ S| + 2|E|`, is the local proof step `h1`. -/
theorem pair_count {β : Type*} (S O E : Set β) (hS : S.Finite) (hE : E.Finite) (π : β → β)
    (hπ : ∀ p, π (π p) = p)
    (hcov : ∀ p ∈ S, π p ∈ S → p ∉ E → π p ∉ E → p ∈ O ∨ π p ∈ O) :
    S.ncard ≤ 2 * (O ∩ S).ncard + 2 * E.ncard + (S \ {p ∈ S | π p ∈ S}).ncard := by
  have h1 : {p ∈ S | π p ∈ S}.ncard ≤ 2 * (O ∩ S).ncard + 2 * E.ncard := by
    have hOS : (O ∩ S).Finite := hS.subset inter_subset_right
    have hsub : {p ∈ S | π p ∈ S} ⊆ ((O ∩ S) ∪ π '' (O ∩ S)) ∪ (E ∪ π '' E) := by
      rintro p ⟨hp, hpp⟩
      by_cases h1 : p ∈ E
      · exact Or.inr (Or.inl h1)
      by_cases h2 : π p ∈ E
      · exact Or.inr (Or.inr ⟨π p, h2, hπ p⟩)
      rcases hcov p hp hpp h1 h2 with h | h
      · exact Or.inl (Or.inl ⟨h, hp⟩)
      · exact Or.inl (Or.inr ⟨π p, ⟨h, hpp⟩, hπ p⟩)
    have hfin : (((O ∩ S) ∪ π '' (O ∩ S)) ∪ (E ∪ π '' E)).Finite :=
      (hOS.union (hOS.image π)).union (hE.union (hE.image π))
    calc {p ∈ S | π p ∈ S}.ncard ≤ (((O ∩ S) ∪ π '' (O ∩ S)) ∪ (E ∪ π '' E)).ncard :=
          ncard_le_ncard hsub hfin
      _ ≤ ((O ∩ S) ∪ π '' (O ∩ S)).ncard + (E ∪ π '' E).ncard := ncard_union_le _ _
      _ ≤ ((O ∩ S).ncard + (π '' (O ∩ S)).ncard) + (E.ncard + (π '' E).ncard) :=
          add_le_add (ncard_union_le _ _) (ncard_union_le _ _)
      _ ≤ ((O ∩ S).ncard + (O ∩ S).ncard) + (E.ncard + E.ncard) :=
          add_le_add (add_le_add le_rfl (ncard_image_le hOS)) (add_le_add le_rfl (ncard_image_le hE))
      _ = 2 * (O ∩ S).ncard + 2 * E.ncard := by ring
  have h2 : {p ∈ S | π p ∈ S} ⊆ S := fun p hp => hp.1
  have h3 := ncard_diff_add_ncard_of_subset h2 hS
  omega

/-! ## Partners -/

/-- The partner coordinate inside a cell: `2i ↔ 2i+1`. -/
def flip (z : ℤ) : ℤ := if z % 2 = 0 then z + 1 else z - 1

theorem flip_flip (z : ℤ) : flip (flip z) = z := by
  unfold flip; split_ifs <;> omega

theorem flip_div (z : ℤ) : flip z / 2 = z / 2 := by
  unfold flip; split_ifs <;> omega

theorem flip_ne (z : ℤ) : flip z ≠ z := by
  unfold flip; split_ifs <;> omega

/-- Vertical pairing in the plane, flipping the second coordinate. -/
def pv (p : ℤ × ℤ) : ℤ × ℤ := (p.1, flip p.2)
/-- Horizontal pairing in the plane, flipping the first coordinate. -/
def ph (p : ℤ × ℤ) : ℤ × ℤ := (flip p.1, p.2)
/-- Checkerboard pairing in the plane, choosing between `ph` and `pv`. -/
def pc (p : ℤ × ℤ) : ℤ × ℤ := if (p.1 / 2 + p.2 / 2) % 2 = 1 then ph p else pv p

theorem pv_pv (p : ℤ × ℤ) : pv (pv p) = p := by simp [pv, flip_flip]
theorem ph_ph (p : ℤ × ℤ) : ph (ph p) = p := by simp [ph, flip_flip]
theorem pc_pc (p : ℤ × ℤ) : pc (pc p) = p := by
  unfold pc
  split_ifs with h1 h2 h2
  · exact ph_ph p
  · simp [ph, flip_div] at h2; omega
  · simp [pv, flip_div] at h2; omega
  · exact pv_pv p

theorem pv_ne (p : ℤ × ℤ) : pv p ≠ p := fun h => flip_ne p.2 (congrArg Prod.snd h)
theorem ph_ne (p : ℤ × ℤ) : ph p ≠ p := fun h => flip_ne p.1 (congrArg Prod.fst h)
theorem pc_ne (p : ℤ × ℤ) : pc p ≠ p := by
  unfold pc; split_ifs
  · exact ph_ne p
  · exact pv_ne p

theorem sat_pv {S : Set (ℤ × ℤ)} (hS : Sat S) {p : ℤ × ℤ} (hp : p ∈ S) : pv p ∈ S :=
  hS p _ rfl (flip_div p.2).symm hp
theorem sat_ph {S : Set (ℤ × ℤ)} (hS : Sat S) {p : ℤ × ℤ} (hp : p ∈ S) : ph p ∈ S :=
  hS p _ (flip_div p.1).symm rfl hp
theorem sat_pc {S : Set (ℤ × ℤ)} (hS : Sat S) {p : ℤ × ℤ} (hp : p ∈ S) : pc p ∈ S := by
  unfold pc; split_ifs
  · exact sat_ph hS hp
  · exact sat_pv hS hp

/-! ## Geometry of the cut pairs -/

theorem ncard_le_of_sub_finset {β : Type*} {A : Set β} (F : Finset β) (h : A ⊆ F) :
    A.ncard ≤ F.card := by
  have := ncard_le_ncard h (Finset.finite_toSet F)
  rwa [ncard_coe_finset] at this

/-- Vertical pairing on a set of bounded width: at most `2 * (W + 1).toNat` points of a box
lose their partner. The naturalized width also covers negative `W`. -/
theorem cut_vertical (Lp : Set (ℤ × ℤ)) (hsat : Sat Lp) (W : ℤ)
    (hW : ∀ p ∈ Lp, 0 ≤ p.1 ∧ p.1 ≤ W) (Z : Prop) (a b c e : ℤ) :
    let S := Lp ∩ {p | Z ∧ p ∈ box a b c e}
    (S \ {p ∈ S | pv p ∈ S}).ncard ≤ 2 * (W + 1).toNat := by
  intro S
  have hsub : S \ {p ∈ S | pv p ∈ S} ⊆ ((Finset.Icc 0 W ×ˢ ({c, e} : Finset ℤ) : Finset (ℤ × ℤ)) :
      Set (ℤ × ℤ)) := by
    rintro p ⟨⟨hpL, hZ, hb⟩, hn⟩
    have hpv : pv p ∉ {p | Z ∧ p ∈ box a b c e} := fun h => hn ⟨⟨hpL, hZ, hb⟩, sat_pv hsat hpL, h⟩
    simp only [box, mem_setOf_eq, pv, not_and, not_le] at hpv hb
    have := hpv hZ
    have hw := hW p hpL
    simp only [Finset.coe_product, mem_prod, Finset.coe_Icc, mem_Icc, Finset.coe_insert,
      Finset.coe_singleton, mem_insert_iff, mem_singleton_iff]
    refine ⟨hw, ?_⟩
    unfold flip at this
    split_ifs at this <;> omega
  refine (ncard_le_of_sub_finset _ hsub).trans ?_
  rw [Finset.card_product, Int.card_Icc, sub_zero]
  have : ({c, e} : Finset ℤ).card ≤ 2 := Finset.card_le_two
  have := Nat.mul_le_mul_left (W + 1).toNat this
  omega

/-- Horizontal pairing on a set of bounded height. -/
theorem cut_horizontal (Lp : Set (ℤ × ℤ)) (hsat : Sat Lp) (W : ℤ)
    (hW : ∀ p ∈ Lp, 0 ≤ p.2 ∧ p.2 ≤ W) (Z : Prop) (a b c e : ℤ) :
    let S := Lp ∩ {p | Z ∧ p ∈ box a b c e}
    (S \ {p ∈ S | ph p ∈ S}).ncard ≤ 2 * (W + 1).toNat := by
  intro S
  have hsub : S \ {p ∈ S | ph p ∈ S} ⊆ ((({a, b} : Finset ℤ) ×ˢ Finset.Icc 0 W : Finset (ℤ × ℤ)) :
      Set (ℤ × ℤ)) := by
    rintro p ⟨⟨hpL, hZ, hb⟩, hn⟩
    have hph : ph p ∉ {p | Z ∧ p ∈ box a b c e} := fun h => hn ⟨⟨hpL, hZ, hb⟩, sat_ph hsat hpL, h⟩
    simp only [box, mem_setOf_eq, ph, not_and, not_le] at hph hb
    have := hph hZ
    have hw := hW p hpL
    simp only [Finset.coe_product, mem_prod, Finset.coe_Icc, mem_Icc, Finset.coe_insert,
      Finset.coe_singleton, mem_insert_iff, mem_singleton_iff]
    refine ⟨?_, hw⟩
    unfold flip at this
    split_ifs at this <;> omega
  refine (ncard_le_of_sub_finset _ hsub).trans ?_
  rw [Finset.card_product, Int.card_Icc, sub_zero]
  have : ({a, b} : Finset ℤ).card ≤ 2 := Finset.card_le_two
  have := Nat.mul_le_mul_right (W + 1).toNat this
  omega

/-- Among `z₁ - z₀ + 1` consecutive integers, at most about half have `⌊y/2⌋` of a given parity. -/
theorem parity_count (z0 z1 r : ℤ) :
    2 * ((Finset.Icc z0 z1).filter (fun y => (r + y / 2) % 2 = 1)).card ≤
      (z1 + 1 - z0).toNat + 2 := by
  set T := (Finset.Icc z0 z1).filter (fun y => (r + y / 2) % 2 = 1) with hT
  have hinj : Function.Injective (fun y : ℤ => y + 2) := fun x y h => by simpa using h
  have hdisj : Disjoint T (T.image (fun y => y + 2)) := by
    rw [Finset.disjoint_left]
    intro y hy hy'
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy'
    simp only [hT, Finset.mem_filter] at hx hy
    omega
  have hsub : T ∪ T.image (fun y => y + 2) ⊆ Finset.Icc z0 (z1 + 2) := by
    intro y hy
    rcases Finset.mem_union.1 hy with hy | hy
    · simp only [hT, Finset.mem_filter, Finset.mem_Icc] at hy ⊢; omega
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      simp only [hT, Finset.mem_filter, Finset.mem_Icc] at hx ⊢; omega
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj,
    Int.card_Icc] at this
  omega

/-- Checkerboard pairing on the quadrant: at most `|S|/2 + 6` points of a box lose their partner. -/
theorem cut_checker (Z : Prop) (a b c e : ℤ) :
    let S := quad ∩ {p | Z ∧ p ∈ box a b c e}
    2 * (S \ {p ∈ S | pc p ∈ S}).ncard ≤ S.ncard + 12 := by
  intro S
  by_cases hZ : Z
  swap
  · have : S = ∅ := by ext p; simp [S, hZ]
    simp [this]
  set a' := max a 0
  set c' := max c 0
  have hS : S = box a' b c' e := by
    ext p; simp only [S, quad, box, mem_inter_iff, mem_setOf_eq, a', c']
    constructor
    · rintro ⟨⟨h1, h2⟩, -, h3, h4, h5, h6⟩; omega
    · rintro ⟨h3, h4, h5, h6⟩; exact ⟨⟨by omega, by omega⟩, hZ, by omega, h4, by omega, h6⟩
  by_cases hne : a' ≤ b ∧ c' ≤ e
  swap
  · have : S = ∅ := by
      rw [hS]; ext p; simp only [box, mem_setOf_eq, mem_empty_iff_false, iff_false]; omega
    simp [this]
  obtain ⟨hab, hce⟩ := hne
  let F : ℤ → Finset ℤ := fun x => (Finset.Icc c' e).filter (fun y => (x / 2 + y / 2) % 2 = 1)
  let F' : ℤ → Finset ℤ := fun y => (Finset.Icc a' b).filter (fun x => (y / 2 + 1 + x / 2) % 2 = 1)
  let Hc : Finset (ℤ × ℤ) := ({a'} ×ˢ F a') ∪ ({b} ×ˢ F b)
  let Vr : Finset (ℤ × ℤ) := (F' c' ×ˢ {c'}) ∪ (F' e ×ˢ {e})
  have hsub : S \ {p ∈ S | pc p ∈ S} ⊆ ((Hc ∪ Vr : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
    rintro p ⟨hpS, hn⟩
    have hpS' := hpS
    rw [hS] at hpS'
    simp only [box, mem_setOf_eq] at hpS'
    have hpc : pc p ∉ S := fun h => hn ⟨hpS, h⟩
    rw [hS] at hpc
    simp only [Hc, Vr, F, F', Finset.coe_union, Finset.coe_product, Finset.coe_singleton,
      Finset.coe_filter, Finset.mem_Icc, mem_union, mem_prod, mem_singleton_iff, mem_setOf_eq]
    unfold pc at hpc
    split_ifs at hpc with ht
    · simp only [box, ph, mem_setOf_eq] at hpc
      unfold flip at hpc
      left
      split_ifs at hpc <;> omega
    · simp only [box, pv, mem_setOf_eq] at hpc
      unfold flip at hpc
      right
      split_ifs at hpc <;> omega
  have hcard := ncard_le_of_sub_finset _ hsub
  have hSn : S.ncard = (b + 1 - a').toNat * (e + 1 - c').toNat := by rw [hS, ncard_box]
  have pF : ∀ x, 2 * (F x).card ≤ (e + 1 - c').toNat + 2 := fun x => parity_count c' e (x / 2)
  have pF' : ∀ y, 2 * (F' y).card ≤ (b + 1 - a').toNat + 2 :=
    fun y => parity_count a' b (y / 2 + 1)
  have hHc : 2 * Hc.card ≤ (if a' = b then 1 else 2) * ((e + 1 - c').toNat + 2) := by
    split_ifs with h
    · have : Hc = {a'} ×ˢ F a' := by simp only [Hc, h, Finset.union_self]
      rw [this, Finset.card_product, Finset.card_singleton]; linarith [pF a']
    · have h1 := Finset.card_union_le ({a'} ×ˢ F a') ({b} ×ˢ F b)
      rw [Finset.card_product, Finset.card_product, Finset.card_singleton,
        Finset.card_singleton] at h1
      linarith [pF a', pF b]
  have hVr : 2 * Vr.card ≤ (if c' = e then 1 else 2) * ((b + 1 - a').toNat + 2) := by
    split_ifs with h
    · have : Vr = F' c' ×ˢ {c'} := by simp only [Vr, h, Finset.union_self]
      rw [this, Finset.card_product, Finset.card_singleton]; linarith [pF' c']
    · have h1 := Finset.card_union_le (F' c' ×ˢ {c'}) (F' e ×ˢ {e})
      rw [Finset.card_product, Finset.card_product, Finset.card_singleton,
        Finset.card_singleton] at h1
      linarith [pF' c', pF' e]
  have hU := Finset.card_union_le Hc Vr
  rw [hSn]
  set W := (b + 1 - a').toNat with hW
  set H := (e + 1 - c').toNat with hH
  have hW1 : 1 ≤ W := by omega
  have hH1 : 1 ≤ H := by omega
  have hWa : a' = b ↔ W = 1 := by omega
  have hHa : c' = e ↔ H = 1 := by omega
  by_cases h1 : W = 1 <;> by_cases h2 : H = 1
  · rw [if_pos (hWa.2 h1)] at hHc; rw [if_pos (hHa.2 h2)] at hVr
    have hP : W * H = 1 := by rw [h1, h2]
    rw [hP]; omega
  · rw [if_pos (hWa.2 h1)] at hHc; rw [if_neg (fun h => h2 (hHa.1 h))] at hVr
    have hP : W * H = H := by rw [h1, one_mul]
    rw [hP]; omega
  · rw [if_neg (fun h => h1 (hWa.1 h))] at hHc; rw [if_pos (hHa.2 h2)] at hVr
    have hP : W * H = W := by rw [h2, mul_one]
    rw [hP]; omega
  · rw [if_neg (fun h => h1 (hWa.1 h))] at hHc; rw [if_neg (fun h => h2 (hHa.1 h))] at hVr
    have : 2 * W + 2 * H ≤ W * H + 4 := by
      have hW2 : (2:ℤ) ≤ W := by exact_mod_cast (show 2 ≤ W by omega)
      have hH2 : (2:ℤ) ≤ H := by exact_mod_cast (show 2 ≤ H by omega)
      have : ((2 * W + 2 * H : ℕ) : ℤ) ≤ ((W * H + 4 : ℕ) : ℤ) := by
        push_cast; nlinarith [mul_nonneg (sub_nonneg.2 hW2) (sub_nonneg.2 hH2)]
      exact_mod_cast this
    generalize W * H = P at *
    omega

/-! ## Pairing generators -/

section PairGen
variable {d : ℕ}

/-- Return the candidate if unused; otherwise return the first unused fallback point when
one exists. If the fallback is exhausted, return the candidate even though it is used.
Unusedness therefore requires a fallback-existence hypothesis, supplied by injectivity in
`chooseOut_not_mem`. -/
noncomputable def chooseOut (cand : Pt d) (fb : ℕ → Pt d) (used : List (Pt d)) : Pt d :=
  if cand ∈ used then (if h : ∃ n, fb n ∉ used then fb (Nat.find h) else cand) else cand

/-- A pairing operation using `l.getLastD 0` as the last input (thus `0` for an empty
history). Return its partner if unused, otherwise the first unused fallback point if one
exists; on fallback exhaustion return the possibly used partner. The freshness theorem
`pairGen_fresh` assumes each fallback map is injective. -/
noncomputable def pairGen (part : List (Pt d) → Pt d → Pt d) (fb : List (Pt d) → ℕ → Pt d)
    (l : List (Pt d)) : Pt d :=
  chooseOut (part l (l.getLastD 0)) (fb l)
    (l ++ List.ofFn (n := l.length - 1) fun i => pairGen part fb (l.take (i.val + 1)))
termination_by l.length
decreasing_by all_goals (simp only [List.length_take]; omega)

theorem chooseOut_not_mem (cand : Pt d) {fb : ℕ → Pt d} (hfb : Function.Injective fb)
    (used : List (Pt d)) : chooseOut cand fb used ∉ used := by
  unfold chooseOut
  split_ifs with h1 h2
  · exact Nat.find_spec h2
  · exfalso
    push Not at h2
    exact (Set.infinite_range_of_injective hfb) ((List.finite_toSet used).subset
      (by rintro _ ⟨n, rfl⟩; exact h2 n))
  · exact h1

theorem chooseOut_cases (cand : Pt d) (fb : ℕ → Pt d) (used : List (Pt d)) :
    chooseOut cand fb used = cand ∨ ∃ n, chooseOut cand fb used = fb n := by
  unfold chooseOut
  split_ifs
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl rfl
  · exact Or.inl rfl

theorem chooseOut_eq (cand : Pt d) (fb : ℕ → Pt d) {used : List (Pt d)} (h : cand ∉ used) :
    chooseOut cand fb used = cand := by
  unfold chooseOut; rw [if_neg h]

theorem getLastD_inputsUpTo (w : ℕ → Pt d) (t : ℕ) : (inputsUpTo w t).getLastD 0 = w t := by
  rw [inputsUpTo, List.ofFn_succ_last]
  simp

theorem pairGen_fresh {part : List (Pt d) → Pt d → Pt d} {fb : List (Pt d) → ℕ → Pt d}
    (hfb : ∀ l, Function.Injective (fb l)) : Generator.Fresh (pairGen part fb) := by
  intro w t
  have hmain := chooseOut_not_mem (part (inputsUpTo w t) ((inputsUpTo w t).getLastD 0))
    (hfb (inputsUpTo w t)) ((inputsUpTo w t) ++ List.ofFn (n := (inputsUpTo w t).length - 1)
      fun i => pairGen part fb ((inputsUpTo w t).take (i.val + 1)))
  rw [← pairGen.eq_1] at hmain
  have hout : Generator.out (pairGen part fb) w t = pairGen part fb (inputsUpTo w t) := rfl
  refine ⟨fun i hi h => hmain ?_, fun s hs h => hmain ?_⟩
  · rw [← hout, ← h]
    apply List.mem_append_left
    simp only [inputsUpTo, List.mem_ofFn]
    exact ⟨⟨i, by omega⟩, rfl⟩
  · rw [← hout, ← h]
    apply List.mem_append_right
    rw [List.mem_ofFn]
    refine ⟨⟨s, by simp [inputsUpTo]; omega⟩, ?_⟩
    simp only [Generator.out]
    rw [inputsUpTo_take w hs.le]

/-- The pairing property: a pair `{p, π p}` of input points whose first input happens at a round
`≥ T₀` (from which on the partner rule is `π`) contains an output. -/
theorem pairGen_cover {part : List (Pt d) → Pt d → Pt d} {fb : List (Pt d) → ℕ → Pt d}
    (w : ℕ → Pt d) (π : Pt d → Pt d) (T0 : ℕ)
    (hpart : ∀ t, T0 ≤ t → part (inputsUpTo w t) (w t) = π (w t)) (p : Pt d)
    (hπp : π (π p) = p) (hne : π p ≠ p) (hp : p ∈ range w)
    (hT : ∀ t < T0, w t ≠ p ∧ w t ≠ π p) :
    p ∈ Generator.outputSet (pairGen part fb) w ∨ π p ∈ Generator.outputSet (pairGen part fb) w := by
  have hex : ∃ t, w t = p ∨ w t = π p := by
    obtain ⟨t, ht⟩ := hp; exact ⟨t, Or.inl ht⟩
  set t0 := Nat.find hex
  have ht0 := Nat.find_spec hex
  have hmin : ∀ s < t0, ¬ (w s = p ∨ w s = π p) := fun s hs => Nat.find_min hex hs
  have hT0 : T0 ≤ t0 := by
    by_contra h
    push Not at h
    rcases ht0 with h' | h'
    · exact (hT t0 h).1 h'
    · exact (hT t0 h).2 h'
  -- the general claim for `x = w t0`, `y = π x`
  have key : ∀ x y : Pt d, w t0 = x → π x = y → y ≠ x → (∀ s < t0, w s ≠ y) →
      y ∈ Generator.outputSet (pairGen part fb) w := by
    intro x y hx hy hyx hys
    set l := inputsUpTo w t0
    have hcand : part l (l.getLastD 0) = y := by
      rw [getLastD_inputsUpTo, hpart t0 hT0, hx, hy]
    by_cases hyl : y ∈ l
    · simp only [l, inputsUpTo, List.mem_ofFn] at hyl
      obtain ⟨⟨s, hs⟩, hs'⟩ := hyl
      simp only at hs'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
      · exact absurd hs' (hys s hs)
      · exact absurd (hs'.symm.trans hx) hyx
    by_cases hyp : y ∈ List.ofFn (n := l.length - 1) fun i => pairGen part fb (l.take (i.val + 1))
    · rw [List.mem_ofFn] at hyp
      obtain ⟨⟨s, hs⟩, hs'⟩ := hyp
      refine ⟨s, ?_⟩
      simp only [Generator.out] at hs' ⊢
      have hst : s ≤ t0 := by simp [l, inputsUpTo] at hs; omega
      rw [← inputsUpTo_take w hst]; exact hs'
    · refine ⟨t0, ?_⟩
      show pairGen part fb l = y
      rw [pairGen.eq_1, hcand]
      exact chooseOut_eq y _ (by simp only [List.mem_append, not_or]; exact ⟨hyl, hyp⟩)
  rcases ht0 with h | h
  · exact Or.inr (key p (π p) h rfl hne fun s hs h' => hmin s hs (Or.inr h'))
  · exact Or.inl (key (π p) p h hπp (Ne.symm hne) fun s hs h' => hmin s hs (Or.inl h'))

/-- Outputs are candidates or fallback points. -/
theorem pairGen_out_cases (part : List (Pt d) → Pt d → Pt d) (fb : List (Pt d) → ℕ → Pt d)
    (w : ℕ → Pt d) (t : ℕ) :
    Generator.out (pairGen part fb) w t = part (inputsUpTo w t) (w t) ∨
      ∃ n, Generator.out (pairGen part fb) w t = fb (inputsUpTo w t) n := by
  show pairGen part fb (inputsUpTo w t) = _ ∨ ∃ n, pairGen part fb (inputsUpTo w t) = _
  rw [pairGen.eq_1, getLastD_inputsUpTo]
  exact chooseOut_cases _ _ _

/-- Lift a planar map to `ℤ^d` through the plane `emb2`. -/
def liftP (f : ℤ × ℤ → ℤ × ℤ) (v : Pt d) : Pt d := emb2 d (f (proj v))

theorem liftP_emb2 (hd : 2 ≤ d) (f : ℤ × ℤ → ℤ × ℤ) (p : ℤ × ℤ) :
    liftP f (emb2 d p) = emb2 d (f p) := by
  simp [liftP, proj_emb2 hd]

/-- The fallback points `(0, n)` of the common column. -/
def fbCol (n : ℕ) : Pt d := emb2 d (0, n)
/-- The fallback points `(n, 0)` of the common row. -/
def fbRow (n : ℕ) : Pt d := emb2 d (n, 0)

theorem fbCol_inj (hd : 2 ≤ d) : Function.Injective (fbCol (d := d)) := by
  intro a b h; have := emb2_inj hd h; simpa using this
theorem fbRow_inj (hd : 2 ≤ d) : Function.Injective (fbRow (d := d)) := by
  intro a b h; have := emb2_inj hd h; simpa using this

/-! ### Counting inside the plane -/

theorem mass_emb (hd : 2 ≤ d) (Lp : Set (ℤ × ℤ)) (R : Rect d) :
    mass (emb2 d '' Lp) R = (Lp ∩ emb2 d ⁻¹' R.pts).ncard := by
  rw [mass, inter_comm, ncard_inter_emb hd, inter_comm]

theorem count_emb (hd : 2 ≤ d) (O : Set (Pt d)) (Lp : Set (ℤ × ℤ)) (R : Rect d) :
    (O ∩ emb2 d '' Lp ∩ R.pts).ncard = (emb2 d ⁻¹' O ∩ (Lp ∩ emb2 d ⁻¹' R.pts)).ncard := by
  have : O ∩ emb2 d '' Lp ∩ R.pts = (O ∩ R.pts) ∩ emb2 d '' Lp := by
    ext x; simp only [mem_inter_iff]; tauto
  rw [this, ncard_inter_emb hd]
  congr 1; ext x; simp only [mem_inter_iff, mem_preimage]; tauto

/-- The planar form of a pairing generator's guarantee: if, for the planar partner `π`, every
pair of the target away from a finite exceptional set meets the output set, and the points of a
box losing their partner number at most `κ |S| + C`, the generator guarantees `(1-κ)/2`. -/
theorem guarantee_planar (hd : 2 ≤ d) {h : ℕ → ℝ} (hh : IsThreshold h) (Lp : Set (ℤ × ℤ))
    (O : Set (Pt d)) (π : ℤ × ℤ → ℤ × ℤ) (hπ : ∀ p, π (π p) = p) (E : Set (ℤ × ℤ))
    (hE : E.Finite)
    (hcov : ∀ p ∈ Lp, π p ∈ Lp → p ∉ E → π p ∉ E → emb2 d p ∈ O ∨ emb2 d (π p) ∈ O)
    (κ C : ℝ) (hκ : 0 ≤ κ)
    (hcut : ∀ R : Rect d, ((Lp ∩ emb2 d ⁻¹' R.pts) \
      {p ∈ Lp ∩ emb2 d ⁻¹' R.pts | π p ∈ Lp ∩ emb2 d ⁻¹' R.pts}).ncard ≤
        κ * (Lp ∩ emb2 d ⁻¹' R.pts).ncard + C) :
    (1 - κ) / 2 ≤ deltaH h O (emb2 d '' Lp) := by
  refine deltaH_ge_of_count hh O _ ((1 - κ) / 2) (C / 2 + E.ncard) (by linarith) fun R => ?_
  rw [mass_emb hd, count_emb hd]
  set S := Lp ∩ emb2 d ⁻¹' R.pts
  have hSf : S.Finite := ((BasicAux.rect_pts_finite R).preimage (emb2_inj hd).injOn).subset
    inter_subset_right
  have h1 := pair_count S (emb2 d ⁻¹' O) E hSf hE π hπ (fun p hp hq h1 h2 => hcov p hp.1 hq.1 h1 h2)
  have h2 := hcut R
  have h3 : (S.ncard : ℝ) ≤ 2 * ((emb2 d ⁻¹' O ∩ S).ncard : ℝ) + 2 * E.ncard +
      ((S \ {p ∈ S | π p ∈ S}).ncard : ℝ) := by exact_mod_cast h1
  nlinarith

end PairGen

/-! ## Forcing cells (Lemma 7.4) -/

section Block
variable {d : ℕ}

theorem fresh_app {G : Generator (Pt d)} (hG : G.Fresh) (l r : List (Pt d)) {k : ℕ}
    (hk : k < r.length) :
    G (l ++ r.take (k + 1)) ∉ l ++ r.take (k + 1) ∧
      ∀ k' < k, G (l ++ r.take (k' + 1)) ≠ G (l ++ r.take (k + 1)) := by
  have := fresh_list hG (l ++ r) (t := l.length + k) (by simp; omega)
  rw [show l.length + k + 1 = l.length + (k + 1) by ring, List.take_length_add_append] at this
  refine ⟨this.1, fun k' hk' => ?_⟩
  have h2 := this.2 (l.length + k') (by omega)
  rwa [show l.length + k' + 1 = l.length + (k' + 1) by ring, List.take_length_add_append] at h2

theorem cellA_mem (i j : ℕ) : cellA i j ∈ cell i j := by
  simp [cellA, cell]
theorem cellB_mem (i j : ℕ) : cellB i j ∈ cell i j := by
  simp [cellB, cell]
theorem cellC_mem (i j : ℕ) : cellC i j ∈ cell i j := by
  simp [cellC, cell]

theorem forced_mono {G : Generator (Pt d)} (hG : G.Fresh) {l : List (Pt d)} {i j : ℕ}
    (h : CellForced G l i j) (r : List (Pt d)) : CellForced G (l ++ r) i j := by
  obtain ⟨⟨t, ht, hta, hbefore⟩, ⟨hA, hB, hC⟩, hcount⟩ := h
  refine ⟨⟨t, by simp; omega, ?_, fun t' ht' ht'' => ?_⟩, ⟨usedBy_mono G l r hA,
    usedBy_mono G l r hB, usedBy_mono G l r hC⟩, ?_⟩
  · simp only [List.get_eq_getElem] at hta ⊢
    rw [List.getElem_append_left ht]; exact hta
  · have hlt : t' < l.length := by omega
    obtain ⟨h1, h2⟩ := hbefore t' ht' hlt
    simp only [List.get_eq_getElem] at h1 ⊢
    rw [List.getElem_append_left hlt, List.take_append_of_le_length (by omega)]
    exact ⟨h1, h2⟩
  · refine le_trans (ncard_le_ncard ?_ ((toFinite _).subset inter_subset_left)) hcount
    rintro x ⟨hx, hxo⟩
    refine ⟨hx, outs_used_sub hG l r hxo ?_⟩
    rcases hx with rfl | rfl | rfl
    · exact hA
    · exact hB
    · exact hC

/-- The three-point play in an untouched cell (§7.1): input `a`; then finish `b, c` so that at
most one of `a, b, c` is an output. -/
theorem three_point (hd : 2 ≤ d) {G : Generator (Pt d)} (hG : G.Fresh) (l : List (Pt d))
    (i j : ℕ) (hu : ∀ x ∈ emb2 d '' cell i j, x ∉ usedBy G l) :
    ∃ r : List (Pt d), (∀ x ∈ r, x ∈ emb2 d '' cell i j) ∧ CellForced G (l ++ r) i j := by
  set A := emb2 d (cellA i j)
  set B := emb2 d (cellB i j)
  set C := emb2 d (cellC i j)
  have hAc : A ∈ emb2 d '' cell i j := mem_image_of_mem _ (cellA_mem i j)
  have hBc : B ∈ emb2 d '' cell i j := mem_image_of_mem _ (cellB_mem i j)
  have hCc : C ∈ emb2 d '' cell i j := mem_image_of_mem _ (cellC_mem i j)
  have hAB : A ≠ B := fun h => by have := emb2_inj hd h; simp [cellA, cellB] at this
  have hAC : A ≠ C := fun h => by have := emb2_inj hd h; simp [cellA, cellC] at this
  have hBC : B ≠ C := fun h => by have := emb2_inj hd h; simp [cellB, cellC] at this
  -- a generic finishing lemma
  have finish : ∀ r : List (Pt d), r ≠ [] → r.head? = some A → (∀ x ∈ r, x = A ∨ x = B ∨ x = C) →
      B ∈ usedBy G (l ++ r) → C ∈ usedBy G (l ++ r) → ∀ z : Pt d,
      (∀ k < r.length, G (l ++ r.take (k + 1)) ∈ ({A, B, C} : Set (Pt d)) →
        G (l ++ r.take (k + 1)) = z) → CellForced G (l ++ r) i j := by
    intro r hr0 hhead hr hBu hCu z hz
    have hrl : 0 < r.length := List.length_pos_iff.2 hr0
    refine ⟨⟨l.length, by simp; omega, ?_, fun t' ht' ht'' => ?_⟩, ⟨Or.inl ?_, hBu, hCu⟩, ?_⟩
    · simp only [List.get_eq_getElem]
      rw [List.getElem_append_right (le_refl _)]
      simp only [Nat.sub_self]
      cases r with
      | nil => exact absurd rfl hr0
      | cons a r => simpa using hhead
    · simp only [List.get_eq_getElem]
      rw [List.getElem_append_left ht', List.take_append_of_le_length (by omega)]
      refine ⟨fun h => hu _ h (Or.inl (List.getElem_mem _)), fun h => hu _ h (Or.inr ⟨t', ht', rfl⟩)⟩
    · cases r with
      | nil => exact absurd rfl hr0
      | cons a r =>
        simp at hhead; subst hhead; exact List.mem_append_right _ (List.mem_cons.2 (Or.inl rfl))
    · have hsub : ({A, B, C} : Set (Pt d)) ∩ outsOf G (l ++ r) ⊆ {z} := by
        rintro x ⟨hx, hxo⟩
        rcases outsOf_append G l r hxo with hxl | ⟨k, hk, rfl⟩
        · exfalso
          have hxc : x ∈ emb2 d '' cell i j := by
            rcases hx with rfl | rfl | rfl
            · exact hAc
            · exact hBc
            · exact hCc
          exact hu x hxc (Or.inr hxl)
        · rw [show l.length + k + 1 = l.length + (k + 1) by ring, List.take_length_add_append] at hx ⊢
          exact hz k hk hx
      exact (ncard_le_ncard hsub (finite_singleton z)).trans (ncard_singleton z).le
  set y1 := G (l ++ [A])
  have hy1 := fresh_app hG l [A] (k := 0) (by simp)
  simp only [List.take_succ_cons, List.take_zero] at hy1
  have hy1A : y1 ≠ A := fun h => hy1.1 (List.mem_append_right _ (List.mem_singleton.2 h))
  by_cases h1 : y1 = B
  · -- input `c`
    refine ⟨[A, C], ?_, finish [A, C] (by simp) rfl (by simp) ?_ (Or.inl (by simp)) B ?_⟩
    · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hAc
      · exact hCc
    · exact Or.inr ⟨l.length, by simp, by
        rw [show l.length + 1 = l.length + 1 from rfl, List.take_length_add_append]; simpa using h1⟩
    · intro k hk hmem
      simp only [List.length_cons, List.length_nil] at hk
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
      · simpa using h1
      · have hf := fresh_app hG l [A, C] (k := 1) (by simp)
        simp only [List.take_succ_cons, List.take_zero] at hf hmem ⊢
        exfalso
        have h2 := hf.2 0 (by omega)
        simp only [List.take_succ_cons, List.take_zero] at h2
        rcases hmem with h | h | h
        · exact hf.1 (by rw [h]; simp)
        · exact h2 (by rw [h]; exact h1)
        · exact hf.1 (by rw [h]; simp)
  by_cases h1' : y1 = C
  · -- input `b`
    refine ⟨[A, B], ?_, finish [A, B] (by simp) rfl (by simp) (Or.inl (by simp)) ?_ C ?_⟩
    · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hAc
      · exact hBc
    · exact Or.inr ⟨l.length, by simp, by
        rw [show l.length + 1 = l.length + 1 from rfl, List.take_length_add_append]; simpa using h1'⟩
    · intro k hk hmem
      simp only [List.length_cons, List.length_nil] at hk
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
      · simpa using h1'
      · have hf := fresh_app hG l [A, B] (k := 1) (by simp)
        simp only [List.take_succ_cons, List.take_zero] at hf hmem ⊢
        exfalso
        have h2 := hf.2 0 (by omega)
        simp only [List.take_succ_cons, List.take_zero] at h2
        rcases hmem with h | h | h
        · exact hf.1 (by rw [h]; simp)
        · exact hf.1 (by rw [h]; simp)
        · exact h2 (by rw [h]; exact h1')
  -- `y1 ∉ {a, b, c}`: input `b`
  have hy1n : y1 ∉ ({A, B, C} : Set (Pt d)) := by
    rintro (h | h | h)
    · exact hy1A h
    · exact h1 h
    · exact h1' h
  set y2 := G (l ++ [A, B])
  have hf2 := fresh_app hG l [A, B] (k := 1) (by simp)
  simp only [List.take_succ_cons, List.take_zero] at hf2
  by_cases h2 : y2 = C
  · refine ⟨[A, B], ?_, finish [A, B] (by simp) rfl (by simp) (Or.inl (by simp)) ?_ C ?_⟩
    · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hAc
      · exact hBc
    · exact Or.inr ⟨l.length + 1, by simp, by
        rw [show l.length + 1 + 1 = l.length + 2 by ring, List.take_length_add_append]; simpa using h2⟩
    · intro k hk hmem
      simp only [List.length_cons, List.length_nil] at hk
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
      · exact absurd (by simpa using hmem) hy1n
      · simpa using h2
  · refine ⟨[A, B, C], ?_, finish [A, B, C] (by simp) rfl (by simp) (Or.inl (by simp))
      (Or.inl (by simp)) A ?_⟩
    · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact hAc
      · exact hBc
      · exact hCc
    · intro k hk hmem
      simp only [List.length_cons, List.length_nil] at hk
      exfalso
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
      · exact hy1n (by simpa using hmem)
      · simp only [List.take_succ_cons, List.take_zero] at hmem
        rcases hmem with h | h | h
        · exact hf2.1 (by rw [h]; simp)
        · exact hf2.1 (by rw [h]; simp)
        · exact h2 h
      · have hf3 := fresh_app hG l [A, B, C] (k := 2) (by simp)
        simp only [List.take_succ_cons, List.take_zero] at hf3 hmem
        rcases hmem with h | h | h
        · exact hf3.1 (by rw [h]; simp)
        · exact hf3.1 (by rw [h]; simp)
        · exact hf3.1 (by rw [h]; simp)

/-- Far enough up, no cell meets a given finite set. -/
theorem exists_T_above (hd : 2 ≤ d) (U : Set (Pt d)) (hU : U.Finite) (T0 m : ℕ) (hm : 1 ≤ m) :
    ∃ T, T0 ≤ T ∧ ∀ x ∈ U, ∀ i J : ℕ, T * m ≤ J → x ∉ emb2 d '' cell i J := by
  obtain ⟨B, hB⟩ := (hU.image (crd 1)).bddAbove
  refine ⟨T0 + B.toNat + 1, by omega, fun x hx i J hJ hxc => ?_⟩
  obtain ⟨p, hp, rfl⟩ := hxc
  have h1 := hB (mem_image_of_mem _ hx)
  rw [crd_emb2_1 hd] at h1
  simp only [cell, mem_setOf_eq, mem_Icc] at hp
  have : T0 + B.toNat + 1 ≤ J := le_trans (Nat.le_mul_of_pos_right _ hm) hJ
  have : ((T0 + B.toNat + 1 : ℕ) : ℤ) ≤ J := by exact_mod_cast this
  push_cast at this
  omega

theorem cells_disjoint {i j i' j' : ℕ} (h : (i, j) ≠ (i', j')) : Disjoint (cell i j) (cell i' j') := by
  rw [Set.disjoint_left]
  rintro p ⟨h1, h2⟩ ⟨h3, h4⟩
  simp only [mem_Icc] at h1 h2 h3 h4
  apply h
  have : (i : ℤ) = i' := by omega
  have : (j : ℤ) = j' := by omega
  simp_all

theorem mod_eq_of_eq {t u m j j' : ℕ} (hj : j < m) (hj' : j' < m) (h : t * m + j = u * m + j') :
    j = j' := by
  have : (t * m + j) % m = (u * m + j') % m := by rw [h]
  have e1 : (t * m + j) % m = j := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  have e2 : (u * m + j') % m = j' := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj']
  rw [e1, e2] at this; exact this

/-- A cell of another block position is not deleted by the rule of a position. -/
theorem cell_disjoint_rule {i j i' j' m T' t : ℕ} (hj : j < m) (hj' : j' < m)
    (hne : (i, j) ≠ (i', j')) : Disjoint (cell i (t * m + j)) (deleted (i', m, T' * m + j')) := by
  rw [deleted, Set.disjoint_iUnion_right]
  intro s
  apply cells_disjoint
  intro h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h
  apply hne
  have : t * m + j = (T' + s) * m + j' := by rw [h2]; ring
  rw [mod_eq_of_eq hj hj' this]

/-- The recursive form of the block construction. -/
theorem block_rec (hd : 2 ≤ d) {G : Generator (Pt d)} (hG : G ∈ ValidGen (family7d d))
    {k ℓ m n : ℕ} (hk : 1 ≤ k) (hkℓ : k ≤ ℓ) (hm : 1 ≤ m) (hnk : n ≤ k) :
    ∀ (P : List (ℕ × ℕ)), P.Nodup → (∀ e ∈ P, 1 ≤ e.1 ∧ e.1 ≤ n ∧ e.2 < m) →
    ∀ (rules : Finset (ℕ × ℕ × ℕ)), (∀ ρ ∈ rules, 1 ≤ ρ.1 ∧ ρ.1 ≤ k ∧ 1 ≤ ρ.2.1) →
      (∀ ρ ∈ rules, ∀ e ∈ P, ∀ t, Disjoint (cell e.1 (t * m + e.2)) (deleted ρ)) →
    ∀ (h : List (Pt d)),
      (∀ x ∈ h, x ∈ emb2 d '' (cappedStrip k ℓ \ ⋃ ρ ∈ rules, deleted ρ)) →
    ∀ T0 : ℕ, ∃ c : List (Pt d),
      (∀ x ∈ c, x ∈ emb2 d '' (cappedStrip k ℓ \ ⋃ ρ ∈ rules, deleted ρ)) ∧ ∃ T, T0 ≤ T ∧
      (∀ i j, 1 ≤ i → i ≤ n → j < m → ∀ x ∈ emb2 d '' cell i (T * m + j), x ∉ usedBy G h) ∧
      ∀ e ∈ P, CellForced G (h ++ c) e.1 (T * m + e.2) := by
  intro P
  induction P with
  | nil =>
    intro _ _ rules _ _ h _ T0
    obtain ⟨T, hT0, hT⟩ := exists_T_above hd (usedBy G h) (usedBy_finite G h) T0 m hm
    refine ⟨[], by simp, T, hT0, fun i j _ _ _ x hx hxu => hT x hxu i _ (by omega) hx, by simp⟩
  | cons e P ih =>
    intro hnd hP rules hrules hdisj h hh T0
    obtain ⟨ie, je⟩ := e
    have he := hP (ie, je) (by simp)
    simp only at he
    have hnd' : P.Nodup := (List.nodup_cons.1 hnd).2
    have heP : (ie, je) ∉ P := (List.nodup_cons.1 hnd).1
    obtain ⟨Te, hTe0, hTe⟩ := exists_T_above hd (usedBy G h) (usedBy_finite G h) T0 m hm
    set ρe : ℕ × ℕ × ℕ := (ie, m, Te * m + je) with hρe
    set rules' := insert ρe rules
    have hrules' : ∀ ρ ∈ rules', 1 ≤ ρ.1 ∧ ρ.1 ≤ k ∧ 1 ≤ ρ.2.1 := by
      intro ρ hρ
      rcases Finset.mem_insert.1 hρ with rfl | hρ
      · exact ⟨he.1, he.2.1.trans hnk, hm⟩
      · exact hrules ρ hρ
    -- cells deleted by the new rule are far up
    have hdel : ∀ p ∈ deleted ρe, ∃ J, Te * m ≤ J ∧ p ∈ cell ie J := by
      intro p hp
      obtain ⟨s, hs⟩ := mem_iUnion.1 hp
      exact ⟨_, by simp only [ρe]; omega, hs⟩
    set Jp := cappedStrip k ℓ \ ⋃ ρ ∈ rules, deleted ρ
    set Jp' := cappedStrip k ℓ \ ⋃ ρ ∈ rules', deleted ρ
    have hJ'J : Jp' ⊆ Jp := by
      rintro p ⟨hp1, hp2⟩
      refine ⟨hp1, fun h3 => hp2 ?_⟩
      simp only [mem_iUnion] at h3 ⊢
      obtain ⟨ρ, hρ, h4⟩ := h3
      exact ⟨ρ, Finset.mem_insert_of_mem hρ, h4⟩
    have hJ'mem : emb2 d '' Jp' ∈ family7d d :=
      ⟨Jp', Or.inr ⟨k, ℓ, rules', hk, hkℓ, hrules', rfl⟩, rfl⟩
    have hJ'inf : (emb2 d '' Jp').Infinite :=
      (col0_infinite (Or.inr ⟨k, ℓ, rules', hk, hkℓ, hrules', rfl⟩)).image (emb2_inj hd).injOn
    have hhJ' : ∀ x ∈ h, x ∈ emb2 d '' Jp' := by
      intro x hx
      obtain ⟨p, ⟨hp1, hp2⟩, rfl⟩ := hh x hx
      refine ⟨p, ⟨hp1, fun h3 => ?_⟩, rfl⟩
      simp only [mem_iUnion] at h3
      obtain ⟨ρ, hρ, h4⟩ := h3
      rcases Finset.mem_insert.1 hρ with rfl | hρ
      · obtain ⟨J, hJ, hpJ⟩ := hdel p h4
        exact hTe _ (Or.inl hx) ie J hJ ⟨p, hpJ, rfl⟩
      · exact hp2 (mem_iUnion₂.2 ⟨ρ, hρ, h4⟩)
    -- commitment to `J'`
    obtain ⟨ext, hextJ, hcommit⟩ := commit_strong hJ'inf
      (fun w hw => hG.2 _ hJ'mem w hw) h hhJ'
    have hdisj' : ∀ ρ ∈ rules', ∀ e ∈ P, ∀ t, Disjoint (cell e.1 (t * m + e.2)) (deleted ρ) := by
      intro ρ hρ e' he' t
      rcases Finset.mem_insert.1 hρ with rfl | hρ
      · have he'b := hP e' (by simp [he'])
        exact cell_disjoint_rule he'b.2.2 he.2.2 (fun h' => heP (h' ▸ he'))
      · exact hdisj ρ hρ e' (by simp [he']) t
    obtain ⟨c', hc'J, T, hTT, huntouched, hforced⟩ :=
      ih hnd' (fun e' he' => hP e' (by simp [he'])) rules' hrules' hdisj' (h ++ ext)
        (by
          intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact hhJ' x hx
          · exact hextJ x hx) Te
    -- the cell of `e` in block `T` is untouched after `h ++ ext ++ c'`
    set E := emb2 d '' cell ie (T * m + je)
    have hEJ' : ∀ x ∈ E, x ∉ emb2 d '' Jp' := by
      rintro x ⟨p, hp, rfl⟩ ⟨q, ⟨hq1, hq2⟩, hqp⟩
      rw [emb2_inj hd hqp] at hq2
      apply hq2
      refine mem_iUnion₂.2 ⟨ρe, Finset.mem_insert_self _ _, mem_iUnion.2 ⟨T - Te, ?_⟩⟩
      have : Te * m + je + (T - Te) * m = T * m + je := by
        have : (T - Te) * m + Te * m = T * m := by rw [← Nat.add_mul, Nat.sub_add_cancel hTT]
        omega
      simp only [ρe]; rw [this]; exact hp
    have hEu : ∀ x ∈ E, x ∉ usedBy G (h ++ ext ++ c') := by
      intro x hxE hxu
      rcases hxu with hxi | hxo
      · rcases List.mem_append.1 hxi with hxi | hxi
        · exact huntouched ie je he.1 he.2.1 he.2.2 x hxE (Or.inl hxi)
        · exact hEJ' x hxE (hc'J x hxi)
      · rcases outsOf_append G (h ++ ext) c' hxo with hxo | ⟨j, hj, rfl⟩
        · exact huntouched ie je he.1 he.2.1 he.2.2 _ hxE (Or.inr hxo)
        · exact hEJ' _ hxE (hcommit c' hc'J j hj)
    obtain ⟨r, hrE, hrforced⟩ := three_point hd hG.1 (h ++ ext ++ c') ie (T * m + je) hEu
    -- `E` lies in the current language
    have hEJ : ∀ x ∈ E, x ∈ emb2 d '' Jp := by
      rintro x ⟨p, hp, rfl⟩
      refine ⟨p, ⟨?_, ?_⟩, rfl⟩
      · simp only [cell, mem_setOf_eq, mem_Icc] at hp
        have : (ie : ℤ) ≤ k := by exact_mod_cast he.2.1.trans hnk
        left; simp only [mem_setOf_eq, mem_Icc]; omega
      · simp only [mem_iUnion, not_exists]
        intro ρ hρ hpρ
        exact Set.disjoint_left.1 (hdisj ρ hρ (ie, je) (by simp) T) hp hpρ
    have hJ'J' : ∀ x ∈ emb2 d '' Jp', x ∈ emb2 d '' Jp := fun x ⟨p, hp, hpx⟩ => ⟨p, hJ'J hp, hpx⟩
    refine ⟨ext ++ c' ++ r, ?_, T, hTe0.trans hTT, ?_, ?_⟩
    · intro x hx
      simp only [List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · exact hJ'J' x (hextJ x hx)
      · exact hJ'J' x (hc'J x hx)
      · exact hEJ x (hrE x hx)
    · intro i j hi1 hin hj x hx hxu
      exact huntouched i j hi1 hin hj x hx (usedBy_mono G h ext hxu)
    · intro e' he'
      have heq : h ++ (ext ++ c' ++ r) = h ++ ext ++ c' ++ r := by simp
      rw [heq]
      rcases List.mem_cons.1 he' with rfl | he'
      · exact hrforced
      · exact forced_mono hG.1 (hforced e' he') r

/-- The construction of Lemma 7.4 (`lem_block`), for any number `n ≤ k` of cell-columns. -/
theorem block (hd : 2 ≤ d) (G : Generator (Pt d)) (hG : G ∈ ValidGen (family7d d))
    {k ℓ : ℕ} (hk : 1 ≤ k) (hkℓ : k ≤ ℓ) (xs : List (Pt d))
    (hxV : ∀ x ∈ xs, x ∈ emb2 d '' cappedStrip k ℓ) (n m : ℕ) (hnk : n ≤ k) (hm : 1 ≤ m) :
    ∃ ext : List (Pt d), (∀ x ∈ ext, x ∈ emb2 d '' cappedStrip k ℓ) ∧
      ∃ T : ℕ, ∀ i, 1 ≤ i → i ≤ n → ∀ j < m, CellForced G (xs ++ ext) i (T + j) := by
  have hJ : cappedStrip k ℓ \ ⋃ ρ ∈ (∅ : Finset (ℕ × ℕ × ℕ)), deleted ρ = cappedStrip k ℓ := by
    simp
  obtain ⟨P, hP⟩ : ∃ P : List (ℕ × ℕ), P = (List.range' 1 n) ×ˢ (List.range m) := ⟨_, rfl⟩
  have hPnd : P.Nodup := by rw [hP]; exact (List.nodup_range' ).product List.nodup_range
  have hPmem : ∀ e, e ∈ P ↔ 1 ≤ e.1 ∧ e.1 ≤ n ∧ e.2 < m := by
    rintro ⟨a, b⟩
    rw [hP]
    simp [List.mem_range'_1]
    omega
  obtain ⟨c, hc, T, -, -, hforced⟩ := block_rec hd hG hk hkℓ hm hnk P hPnd
    (fun e he => (hPmem e).1 he) ∅ (by simp) (by simp) xs (by rw [hJ]; exact hxV) 0
  refine ⟨c, by rw [hJ] at hc; exact hc, T * m, fun i hi1 hin j hj => ?_⟩
  exact hforced (i, j) ((hPmem (i, j)).2 ⟨hi1, hin, hj⟩)

end Block

/-! ## Tests, counting in a forced block, Claim 7.6 and Lemma 7.5 -/

section Tests
variable {d : ℕ}

/-- The vertical test of cell-column `i` over cell-rows `T, …, T+m-1`: the `a, b` points. -/
def vTest (d i T m : ℕ) : Set (Pt d) :=
  emb2 d '' box (2 * (i : ℤ)) (2 * i) (2 * (T : ℤ)) (2 * T + 2 * m - 1)

theorem hTest_eq (d n j : ℕ) :
    hTest d n j = emb2 d '' box 2 (2 * (n : ℤ) + 1) (2 * (j : ℤ)) (2 * j) := by
  unfold hTest box
  congr 1; ext p; simp only [mem_setOf_eq, mem_Icc]; omega

theorem forced_A_not_out {G : Generator (Pt d)} (hG : G.Fresh) {l : List (Pt d)}
    {i j : ℕ} (h : CellForced G l i j) : emb2 d (cellA i j) ∉ outsOf G l := by
  obtain ⟨⟨t, ht, hta, hbefore⟩, -, -⟩ := h
  rintro ⟨s, hs, hsA⟩
  by_cases hst : s < t
  · exact (hbefore s hst hs).2 (by rw [hsA]; exact mem_image_of_mem _ (cellA_mem i j))
  · apply (fresh_list hG l hs).1
    rw [hsA, ← hta]
    simp only [List.get_eq_getElem]
    have : t < (l.take (s + 1)).length := by simp; omega
    have e : (l.take (s + 1))[t] = l[t] := by simp
    rw [← e]; exact List.getElem_mem this

/-- The outputs in the tests of a forced `n × m` block (Lemma 7.5): horizontal and vertical
tests share only the input points `a`, and each cell has at most one output among `b, c`. -/
theorem block_count (hd : 2 ≤ d) {G : Generator (Pt d)} (hG : G.Fresh) (l : List (Pt d))
    (n m T : ℕ) (hF : ∀ i, 1 ≤ i → i ≤ n → ∀ j < m, CellForced G l i (T + j)) :
    (∑ j ∈ Finset.range m, (hTest d n (T + j) ∩ outsOf G l).ncard) +
      (∑ i ∈ Finset.Icc 1 n, (vTest d i T m ∩ outsOf G l).ncard) ≤ n * m := by
  let γ : ℕ → ℕ → ℕ := fun i j => if emb2 d (cellC i (T + j)) ∈ outsOf G l then 1 else 0
  let β : ℕ → ℕ → ℕ := fun i j => if emb2 d (cellB i (T + j)) ∈ outsOf G l then 1 else 0
  have ha : ∀ j < m, (hTest d n (T + j) ∩ outsOf G l).ncard ≤ ∑ i ∈ Finset.Icc 1 n, γ i j := by
    intro j hj
    have hsub : hTest d n (T + j) ∩ outsOf G l ⊆
        (((Finset.Icc 1 n).filter (fun i => emb2 d (cellC i (T + j)) ∈ outsOf G l)).image
          (fun i => emb2 d (cellC i (T + j))) : Set (Pt d)) := by
      rintro x ⟨⟨p, hp, rfl⟩, hxo⟩
      simp only [mem_setOf_eq, mem_Icc] at hp
      obtain ⟨i, hi⟩ : ∃ i : ℕ, p.1 = 2 * i ∨ p.1 = 2 * i + 1 := ⟨(p.1 / 2).toNat, by omega⟩
      have hi1 : 1 ≤ i ∧ i ≤ n := by omega
      rcases hi with hi | hi
      · exfalso
        have : p = cellA i (T + j) := by
          simp only [cellA]; ext <;> simp <;> omega
        rw [this] at hxo
        exact forced_A_not_out hG (hF i hi1.1 hi1.2 j hj) hxo
      · have : p = cellC i (T + j) := by
          simp only [cellC]; ext <;> simp <;> omega
        rw [this] at hxo ⊢
        simp only [Finset.coe_image, Finset.coe_filter, Finset.mem_Icc]
        exact ⟨i, ⟨hi1, hxo⟩, rfl⟩
    refine (ncard_le_of_sub_finset _ hsub).trans (Finset.card_image_le.trans ?_)
    rw [Finset.card_filter]
  have hb : ∀ i, 1 ≤ i → i ≤ n → (vTest d i T m ∩ outsOf G l).ncard ≤
      ∑ j ∈ Finset.range m, β i j := by
    intro i hi1 hin
    have hsub : vTest d i T m ∩ outsOf G l ⊆
        (((Finset.range m).filter (fun j => emb2 d (cellB i (T + j)) ∈ outsOf G l)).image
          (fun j => emb2 d (cellB i (T + j))) : Set (Pt d)) := by
      rintro x ⟨⟨p, hp, rfl⟩, hxo⟩
      simp only [box, mem_setOf_eq] at hp
      obtain ⟨j, hj⟩ : ∃ j : ℕ, p.2 = 2 * (T + j : ℕ) ∨ p.2 = 2 * (T + j : ℕ) + 1 :=
        ⟨(p.2 / 2 - T).toNat, by push_cast; omega⟩
      have hjm : j < m := by push_cast at hj; omega
      rcases hj with hj | hj
      · exfalso
        have : p = cellA i (T + j) := by
          simp only [cellA]; ext <;> simp <;> push_cast at hj <;> omega
        rw [this] at hxo
        exact forced_A_not_out hG (hF i hi1 hin j hjm) hxo
      · have : p = cellB i (T + j) := by
          simp only [cellB]; ext <;> simp <;> push_cast at hj <;> omega
        rw [this] at hxo ⊢
        simp only [Finset.coe_image, Finset.coe_filter, Finset.mem_range]
        exact ⟨j, ⟨hjm, hxo⟩, rfl⟩
    refine (ncard_le_of_sub_finset _ hsub).trans (Finset.card_image_le.trans ?_)
    rw [Finset.card_filter]
  have hc : ∀ i, 1 ≤ i → i ≤ n → ∀ j < m, γ i j + β i j ≤ 1 := by
    intro i hi1 hin j hj
    have hF' := (hF i hi1 hin j hj).2.2
    simp only [γ, β]
    split_ifs with h1 h2
    · exfalso
      have hBC : emb2 d (cellB i (T + j)) ≠ emb2 d (cellC i (T + j)) := fun h =>
        by have := emb2_inj hd h; simp [cellB, cellC] at this
      have hsub : ({emb2 d (cellB i (T + j)), emb2 d (cellC i (T + j))} : Set (Pt d)) ⊆
          {emb2 d (cellA i (T + j)), emb2 d (cellB i (T + j)), emb2 d (cellC i (T + j))} ∩
            outsOf G l := by
        intro x hx
        rcases hx with rfl | rfl
        · exact ⟨Or.inr (Or.inl rfl), h2⟩
        · exact ⟨Or.inr (Or.inr rfl), h1⟩
      have := ncard_le_ncard hsub ((toFinite _).subset inter_subset_left)
      rw [ncard_pair hBC] at this
      omega
    all_goals simp
  calc (∑ j ∈ Finset.range m, (hTest d n (T + j) ∩ outsOf G l).ncard) +
        (∑ i ∈ Finset.Icc 1 n, (vTest d i T m ∩ outsOf G l).ncard)
      ≤ (∑ j ∈ Finset.range m, ∑ i ∈ Finset.Icc 1 n, γ i j) +
        (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.range m, β i j) := by
        gcongr with j hj i hi
        · exact ha j (Finset.mem_range.1 hj)
        · have := Finset.mem_Icc.1 hi; exact hb i this.1 this.2
    _ = ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.range m, (γ i j + β i j) := by
        rw [Finset.sum_comm, ← Finset.sum_add_distrib]
        congr 1; ext i; rw [Finset.sum_add_distrib]
    _ ≤ ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.range m, 1 := by
        gcongr with i hi j hj
        have := Finset.mem_Icc.1 hi
        exact hc i this.1 this.2 j (Finset.mem_range.1 hj)
    _ = n * m := by simp

theorem hTest_used {G : Generator (Pt d)} {l : List (Pt d)} {n T j : ℕ}
    (hF : ∀ i, 1 ≤ i → i ≤ n → CellForced G l i (T + j)) : hTest d n (T + j) ⊆ usedBy G l := by
  rintro x ⟨p, hp, rfl⟩
  simp only [mem_setOf_eq, mem_Icc] at hp
  obtain ⟨i, hi⟩ : ∃ i : ℕ, p.1 = 2 * i ∨ p.1 = 2 * i + 1 := ⟨(p.1 / 2).toNat, by omega⟩
  have hi1 : 1 ≤ i ∧ i ≤ n := by omega
  have hF' := (hF i hi1.1 hi1.2).2.1
  rcases hi with hi | hi
  · have : p = cellA i (T + j) := by simp only [cellA]; ext <;> simp <;> omega
    rw [this]; exact hF'.1
  · have : p = cellC i (T + j) := by simp only [cellC]; ext <;> simp <;> omega
    rw [this]; exact hF'.2.2

theorem vTest_used {G : Generator (Pt d)} {l : List (Pt d)} {i T m : ℕ}
    (hF : ∀ j < m, CellForced G l i (T + j)) : vTest d i T m ⊆ usedBy G l := by
  rintro x ⟨p, hp, rfl⟩
  simp only [box, mem_setOf_eq] at hp
  obtain ⟨j, hj⟩ : ∃ j : ℕ, p.2 = 2 * (T + j : ℕ) ∨ p.2 = 2 * (T + j : ℕ) + 1 :=
    ⟨(p.2 / 2 - T).toNat, by push_cast; omega⟩
  have hjm : j < m := by push_cast at hj; omega
  have hF' := (hF j hjm).2.1
  rcases hj with hj | hj
  · have : p = cellA i (T + j) := by simp only [cellA]; ext <;> simp <;> push_cast at hj <;> omega
    rw [this]; exact hF'.1
  · have : p = cellB i (T + j) := by simp only [cellB]; ext <;> simp <;> push_cast at hj <;> omega
    rw [this]; exact hF'.2.1

/-- A test rectangle inside an embedded planar set: its mass is its volume, and only the outputs
inside it count. -/
theorem test_props (hd : 2 ≤ d) (Lp : Set (ℤ × ℤ)) {a b c e : ℤ} (hab : a ≤ b) (hce : c ≤ e)
    (hsub : box a b c e ⊆ Lp) (O : Set (Pt d)) :
    mass (emb2 d '' Lp) (prect d a b c e hab hce) = (b + 1 - a).toNat * (e + 1 - c).toNat ∧
      (O ∩ emb2 d '' Lp ∩ (prect d a b c e hab hce).pts) = O ∩ emb2 d '' box a b c e := by
  rw [prect_pts hd]
  have himg : emb2 d '' box a b c e ⊆ emb2 d '' Lp := image_mono hsub
  refine ⟨?_, ?_⟩
  · rw [mass, prect_pts hd, inter_eq_right.2 himg, ncard_image_of_injective _ (emb2_inj hd),
      ncard_box]
  · rw [inter_assoc, inter_eq_right.2 himg]

/-- Even sizes reach every level. -/
theorem thr_even {h : ℕ → ℝ} (hh : IsThreshold h) (k : ℕ) :
    ∃ m : ℕ, 1 ≤ m ∧ (k : ℝ) * h (2 * m) ≤ 2 * m := by
  have h1 : 0 < h 1 := hh.1 1 le_rfl
  obtain ⟨_, ⟨N, hN1, rfl⟩, hN⟩ := not_bddAbove_iff.1 hh.2.2 (2 * k + 1 / h 1 + 1)
  simp only [mem_Ici] at hN1
  have hN2 : 2 ≤ N := by
    by_contra hlt
    have : N = 1 := by omega
    subst this
    simp only [Nat.cast_one] at hN
    have : (0 : ℝ) ≤ 2 * k := by positivity
    linarith
  have hhN : 0 < h N := hh.1 N hN1
  have hlt : (2 * k + 1 / h 1 + 1) * h N < N := by rwa [lt_div_iff₀ hhN] at hN
  refine ⟨N / 2, by omega, ?_⟩
  have hmono : h (2 * (N / 2)) ≤ h N :=
    hh.2.1 (mem_Ici.2 (by omega)) (mem_Ici.2 hN1) (Nat.mul_div_le N 2)
  have hk : (k : ℝ) * h N * 2 < N := by
    have : 0 ≤ (1 / h 1 + 1) * h N := by positivity
    nlinarith
  have hN4 : (N : ℝ) ≤ 4 * ((N / 2 : ℕ) : ℝ) := by
    have : N ≤ 4 * (N / 2) := by omega
    exact_mod_cast this
  have hkn : (0 : ℝ) ≤ k := by positivity
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hmono hkn]

theorem prefix_of_staged {α : Type*} (hs : ℕ → List α) (xs : List α) (hs0 : hs 0 = xs)
    (hsucc : ∀ k, ∃ r, hs (k + 1) = hs k ++ r) : ∀ k, ∃ E, hs k = xs ++ E := by
  intro k
  induction k with
  | zero => exact ⟨[], by simp [hs0]⟩
  | succ k ih =>
    obtain ⟨E, hE⟩ := ih
    obtain ⟨r, hr⟩ := hsucc k
    exact ⟨E ++ r, by rw [hr, hE, List.append_assoc]⟩

/-- A finite input history inside `ℕ²` lies in a cap. -/
theorem exists_cap (hd : 2 ≤ d) (l : List (Pt d)) (hl : ∀ x ∈ l, x ∈ K0d d) (n : ℕ) :
    ∃ ℓ, n ≤ ℓ ∧ ∀ x ∈ l, x ∈ emb2 d '' cappedStrip n ℓ := by
  obtain ⟨B, hB⟩ := ((List.finite_toSet l).image (fun x => max (crd 0 x) (crd 1 x))).bddAbove
  refine ⟨n + B.toNat, by omega, fun x hx => ?_⟩
  obtain ⟨p, hp, rfl⟩ := hl x hx
  have := hB (mem_image_of_mem _ hx)
  simp only [crd_emb2_0 hd, crd_emb2_1 hd] at this
  refine ⟨p, Or.inr ⟨⟨hp.1, ?_⟩, ⟨hp.2, ?_⟩⟩, rfl⟩ <;> push_cast <;> omega

theorem strip_mem_d (hd : 2 ≤ d) {n ℓ : ℕ} (hn : 1 ≤ n) (hnℓ : n ≤ ℓ) :
    emb2 d '' cappedStrip n ℓ ∈ family7d d ∧ emb2 d '' cappedStrip n ℓ ≠ K0d d :=
  ⟨⟨_, strip_mem hn hnℓ, rfl⟩, fun h => strip_ne_quad n ℓ ((image_injective.2 (emb2_inj hd)) h)⟩

theorem strip_sub_K0 {n ℓ : ℕ} : emb2 d '' cappedStrip n ℓ ⊆ K0d d :=
  image_mono (strip_sub_quad n ℓ)

theorem strip_infinite (hd : 2 ≤ d) {n ℓ : ℕ} (hn : 1 ≤ n) (hnℓ : n ≤ ℓ) :
    (emb2 d '' cappedStrip n ℓ).Infinite :=
  (col0_infinite (strip_mem hn hnℓ)).image (emb2_inj hd).injOn

end Tests

end SeparationAux

/-! ## Claim 7.6 and Lemma 7.5 -/

/-- **Claim 7.6** (unlabelled claim inside the proof of Lemma 7.5): fix an admissible `h`, a
generator eventually valid on the family that guarantees `y` at the capped strip `V_{n,ℓ}`, and
`v < y`. After any finite sequence of inputs from `V_{n,ℓ}` (repetitions allowed, as in the paper), finitely many further inputs from `V_{n,ℓ}` produce a finished horizontal test of length `2n` (every point input or
output) with at most `(1/2 - v)·2n` outputs. 
-/
theorem claim_horizontal_test {d : ℕ} (hd : 2 ≤ d) (h : ℕ → ℝ) (hh : IsThreshold h)
    (G : Generator (Pt d)) (hG : G ∈ ValidGen (family7d d)) {n ℓ : ℕ} (hn : 1 ≤ n) (hnℓ : n ≤ ℓ)
    {y v : ℝ} (hv : v < y) (hy : Guarantees (dH h) G (emb2 d '' cappedStrip n ℓ) y)
    (xs : List (Pt d)) (hxV : ∀ x ∈ xs, x ∈ emb2 d '' cappedStrip n ℓ) :
    ∃ ext : List (Pt d), (∀ x ∈ ext, x ∈ emb2 d '' cappedStrip n ℓ) ∧
      ∃ j : ℕ, hTest d n j ⊆ usedBy G (xs ++ ext) ∧
        ((hTest d n j ∩ outsOf G (xs ++ ext)).ncard : ℝ) ≤ (1 / 2 - v) * (2 * n) := open SeparationAux in by
  by_contra hcon
  push Not at hcon
  set V := emb2 d '' cappedStrip n ℓ with hVdef
  have hVinf : V.Infinite := strip_infinite hd hn hnℓ
  obtain ⟨e, he⟩ : ∃ e : ℕ → Pt d, range e = V := by
    obtain ⟨e, he⟩ := (Set.to_countable V).exists_eq_range hVinf.nonempty
    exact ⟨e, he.symm⟩
  choose mk hmk1 hmk2 using thr_even hh
  let step : ℕ → List (Pt d) → List (Pt d) := fun k l =>
    if hl : ∀ x ∈ l, x ∈ V then
      (block hd G hG hn hnℓ l hl n (mk k) le_rfl (hmk1 k)).choose else []
  have hstep : ∀ k l, (∀ x ∈ l, x ∈ V) → ∀ x ∈ step k l, x ∈ V := by
    intro k l hl x hx
    simp only [step, dif_pos hl] at hx
    exact (block hd G hG hn hnℓ l hl n (mk k) le_rfl (hmk1 k)).choose_spec.1 x hx
  obtain ⟨w, hs, hfull, hs0, hs_succ, hw, hsL, hlen⟩ := staged he xs hxV step hstep
  have hpre := prefix_of_staged hs xs hs0 (fun k => ⟨_, by rw [hs_succ, List.append_assoc]⟩)
  set O := G.outputSet w
  have hdel : deltaH h O V ≤ v := by
    refine deltaH_le_of_tests hh O V v fun k => ?_
    set l := hs k ++ [nextPt e (hs k)]
    have hl : ∀ x ∈ l, x ∈ V := by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hsL k x hx
      · rw [List.mem_singleton.1 hx]; exact nextPt_mem he _
    have hspec := (block hd G hG hn hnℓ l hl n (mk k) le_rfl (hmk1 k)).choose_spec
    obtain ⟨T, hF⟩ := hspec.2
    have hsk : hs (k + 1) = l ++ (block hd G hG hn hnℓ l hl n (mk k) le_rfl (hmk1 k)).choose := by
      rw [hs_succ]; show l ++ step k l = _; simp only [step, dif_pos hl]
    set L1 := hs (k + 1)
    rw [← hsk] at hF
    obtain ⟨E, hE⟩ := hpre (k + 1)
    have hEV : ∀ x ∈ E, x ∈ V := fun x hx => hsL (k + 1) x (by rw [hE]; exact List.mem_append_right _ hx)
    set m := mk k
    -- every horizontal test is dense
    have hH : ∀ j < m, (1 / 2 - v) * (2 * n) < ((hTest d n (T + j) ∩ outsOf G L1).ncard : ℝ) := by
      intro j hj
      have hu : hTest d n (T + j) ⊆ usedBy G L1 := hTest_used fun i h1 h2 => hF i h1 h2 j hj
      rw [show L1 = xs ++ E from hE] at hu ⊢
      exact hcon E hEV (T + j) hu
    have hcount := block_count hd hG.1 L1 n m T hF
    -- some vertical test is sparse
    obtain ⟨i, hi, hiv⟩ : ∃ i ∈ Finset.Icc 1 n,
        ((vTest d i T m ∩ outsOf G L1).ncard : ℝ) < 2 * m * v := by
      by_contra hall
      push Not at hall
      have hm0 : (Finset.range m).Nonempty := ⟨0, by simp; exact hmk1 k⟩
      have s1 : ∑ j ∈ Finset.range m, (1 / 2 - v) * (2 * n) <
          ∑ j ∈ Finset.range m, ((hTest d n (T + j) ∩ outsOf G L1).ncard : ℝ) :=
        Finset.sum_lt_sum_of_nonempty hm0 fun j hj => hH j (Finset.mem_range.1 hj)
      have s2 : ∑ i ∈ Finset.Icc 1 n, 2 * (m : ℝ) * v ≤
          ∑ i ∈ Finset.Icc 1 n, ((vTest d i T m ∩ outsOf G L1).ncard : ℝ) :=
        Finset.sum_le_sum hall
      have s3 : ((∑ j ∈ Finset.range m, (hTest d n (T + j) ∩ outsOf G L1).ncard : ℕ) : ℝ) +
          ((∑ i ∈ Finset.Icc 1 n, (vTest d i T m ∩ outsOf G L1).ncard : ℕ) : ℝ) ≤ (n : ℝ) * m := by
        exact_mod_cast hcount
      push_cast at s3
      simp only [Finset.sum_const, Finset.card_range, Nat.card_Icc, nsmul_eq_mul] at s1 s2
      simp only [add_tsub_cancel_right] at s2
      nlinarith
    have hi' := Finset.mem_Icc.1 hi
    have hab : 2 * (i : ℤ) ≤ 2 * i := le_rfl
    have hce : 2 * (T : ℤ) ≤ 2 * T + 2 * m - 1 := by have := hmk1 k; omega
    have hsub : box (2 * (i : ℤ)) (2 * i) (2 * (T : ℤ)) (2 * T + 2 * m - 1) ⊆ cappedStrip n ℓ := by
      intro p hp
      simp only [box, mem_setOf_eq] at hp
      left; simp only [mem_setOf_eq, mem_Icc]; omega
    obtain ⟨hmass, hcnt⟩ := test_props hd (cappedStrip n ℓ) hab hce hsub O
    have hsz : (2 * (i : ℤ) + 1 - 2 * i).toNat * (2 * (T : ℤ) + 2 * m - 1 + 1 - 2 * T).toNat =
        2 * m := by
      have e1 : 2 * (i : ℤ) + 1 - 2 * i = 1 := by ring
      have e2 : 2 * (T : ℤ) + 2 * m - 1 + 1 - 2 * T = ((2 * m : ℕ) : ℤ) := by push_cast; ring
      rw [e1, e2, Int.toNat_natCast]; simp
    refine ⟨prect d _ _ _ _ hab hce, ?_, ?_⟩
    · rw [hmass, prect_vol hd, hsz]; push_cast; exact hmk2 k
    · rw [hcnt, hmass, hsz]
      have hfin : O ∩ vTest d i T m = outsOf G L1 ∩ vTest d i T m :=
        outputSet_inter_eq hG.1 (hw (k + 1)) (vTest_used fun j hj => hF i hi'.1 hi'.2 j hj)
      have hmpos : (0 : ℝ) < ((2 * m : ℕ) : ℝ) := by have := hmk1 k; positivity
      rw [div_le_iff₀ hmpos]
      have : (O ∩ emb2 d '' box (2 * ↑i) (2 * ↑i) (2 * ↑T) (2 * ↑T + 2 * ↑m - 1)).ncard =
          (vTest d i T m ∩ outsOf G L1).ncard := by
        rw [show emb2 d '' box (2 * ↑i) (2 * ↑i) (2 * ↑T) (2 * ↑T + 2 * ↑m - 1) = vTest d i T m
          from rfl, hfin, inter_comm]
      rw [this]; push_cast; linarith
  have h1 := hy w hfull
  simp only [dH, EReal.coe_le_coe_iff] at h1
  linarith

/-- **Lemma 7.5** (`prop:tradeoff`): for the family of §7.2, an admissible `h` and a generator
eventually valid on the family that guarantees `x` at `K₀` and `y` at every other language,
`x + y ≤ 1/2`. -/
theorem prop_tradeoff {d : ℕ} (hd : 2 ≤ d) (h : ℕ → ℝ) (hh : IsThreshold h)
    (G : Generator (Pt d)) (hG : G ∈ ValidGen (family7d d)) (x y : ℝ)
    (hx : Guarantees (dH h) G (K0d d) x)
    (hy : ∀ L ∈ family7d d, L ≠ K0d d → Guarantees (dH h) G L y) : x + y ≤ 1 / 2 := open SeparationAux in by
  suffices H : ∀ v < y, x ≤ 1 / 2 - v by
    by_contra hc
    push Not at hc
    have := H ((y + 1 / 2 - x) / 2) (by linarith)
    linarith
  intro v hv
  set K := K0d d
  have hKinf : K.Infinite := (langClass_family7d hd).infinite K (K0d_mem d)
  obtain ⟨e, he⟩ : ∃ e : ℕ → Pt d, range e = K := by
    obtain ⟨e, he⟩ := (Set.to_countable K).exists_eq_range hKinf.nonempty
    exact ⟨e, he.symm⟩
  choose nk hnk1 hnk2 using thr_even hh
  choose ℓf hℓf1 hℓf2 using fun (l : List (Pt d)) (hl : ∀ x ∈ l, x ∈ K) (k : ℕ) =>
    exists_cap hd l hl (nk k)
  choose cext hcext1 hcext2 using fun (l : List (Pt d)) (hl : ∀ x ∈ l, x ∈ K) (k : ℕ) =>
    claim_horizontal_test hd h hh G hG (hnk1 k) (hℓf1 l hl k) hv
      (hy _ (strip_mem_d hd (hnk1 k) (hℓf1 l hl k)).1 (strip_mem_d hd (hnk1 k) (hℓf1 l hl k)).2)
      l (hℓf2 l hl k)
  let step : ℕ → List (Pt d) → List (Pt d) := fun k l =>
    if hl : ∀ x ∈ l, x ∈ K then cext l hl k else []
  have hstep : ∀ k l, (∀ x ∈ l, x ∈ K) → ∀ x ∈ step k l, x ∈ K := by
    intro k l hl x hx
    simp only [step, dif_pos hl] at hx
    exact strip_sub_K0 (hcext1 l hl k x hx)
  have hxs : ∀ x ∈ ([] : List (Pt d)), x ∈ K := by simp
  obtain ⟨w, hs, hfull, hs0, hs_succ, hw, hsL, hlen⟩ := staged he [] hxs step hstep
  set O := G.outputSet w
  have hdel : deltaH h O K ≤ 1 / 2 - v := by
    refine deltaH_le_of_tests hh O K _ fun k => ?_
    set l := hs k ++ [nextPt e (hs k)]
    have hl : ∀ x ∈ l, x ∈ K := by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hsL k x hx
      · rw [List.mem_singleton.1 hx]; exact nextPt_mem he _
    have hsk : hs (k + 1) = l ++ cext l hl k := by
      rw [hs_succ]; show l ++ step k l = _; simp only [step, dif_pos hl]
    obtain ⟨j, hju, hjc⟩ := hcext2 l hl k
    rw [← hsk] at hju hjc
    set n := nk k
    have hab : (2 : ℤ) ≤ 2 * n + 1 := by have := hnk1 k; omega
    have hce : 2 * (j : ℤ) ≤ 2 * j := le_rfl
    have hsub : box 2 (2 * (n : ℤ) + 1) (2 * (j : ℤ)) (2 * j) ⊆ quad := by
      intro p hp; simp only [box, mem_setOf_eq] at hp; simp only [quad, mem_setOf_eq]; omega
    obtain ⟨hmass, hcnt⟩ := test_props hd quad hab hce hsub O
    have hsz : (2 * (n : ℤ) + 1 + 1 - 2).toNat * (2 * (j : ℤ) + 1 - 2 * j).toNat = 2 * n := by
      have e1 : 2 * (n : ℤ) + 1 + 1 - 2 = ((2 * n : ℕ) : ℤ) := by push_cast; ring
      have e2 : 2 * (j : ℤ) + 1 - 2 * j = 1 := by ring
      rw [e1, e2, Int.toNat_natCast]; simp
    refine ⟨prect d _ _ _ _ hab hce, ?_, ?_⟩
    · rw [show K = emb2 d '' quad from rfl, hmass, prect_vol hd, hsz]; push_cast; exact hnk2 k
    · rw [show K = emb2 d '' quad from rfl, hcnt, hmass, hsz, ← hTest_eq]
      have hfin : O ∩ hTest d n j = outsOf G (hs (k + 1)) ∩ hTest d n j :=
        outputSet_inter_eq hG.1 (hw (k + 1)) hju
      have hmpos : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by have := hnk1 k; positivity
      rw [div_le_iff₀ hmpos, hfin, inter_comm]
      push_cast; linarith
  have h1 := hx w hfull
  simp only [dH, EReal.coe_le_coe_iff] at h1
  linarith

namespace SeparationAux

/-! ## The race, the individual upper bounds -/

section Upper
variable {d : ℕ}

/-- **The race** (ported from the one-dimensional library, Lemma 5.2 there). -/
theorem race {α : Type*} {G : Generator α} (hG : G.Fresh) {A : Set α} (hA : A.Finite)
    (h : List α) (hd : Disjoint (usedBy G h) A) :
    ∃ r : List α, (∀ x ∈ r, x ∈ A) ∧ A ⊆ usedBy G (h ++ r) ∧
      2 * (outsOf G (h ++ r) ∩ A).ncard ≤ A.ncard := by
  have hfinI : ∀ h : List α, ({x | x ∈ h} ∩ A).Finite := fun _ => hA.subset inter_subset_right
  have hfinO : ∀ h : List α, (outsOf G h ∩ A).Finite := fun _ => hA.subset inter_subset_right
  suffices H : ∀ m, ∀ h : List α, (A \ usedBy G h).ncard = m →
      Disjoint ({x | x ∈ h} ∩ A) (outsOf G h ∩ A) →
      (outsOf G h ∩ A).ncard ≤ ({x | x ∈ h} ∩ A).ncard →
      ∃ r : List α, (∀ x ∈ r, x ∈ A) ∧ A ⊆ usedBy G (h ++ r) ∧
        2 * (outsOf G (h ++ r) ∩ A).ncard ≤ A.ncard by
    have hO : outsOf G h ∩ A = ∅ :=
      eq_empty_of_forall_notMem fun x hx => disjoint_left.1 hd (Or.inr hx.1) hx.2
    refine H _ h rfl ?_ ?_
    · rw [hO]; exact disjoint_empty _
    · rw [hO]; simp
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro h hm hdisj hle
  by_cases hfull : A ⊆ usedBy G h
  · refine ⟨[], by simp, by simpa using hfull, ?_⟩
    simp only [List.append_nil]
    have hu : ({x | x ∈ h} ∩ A) ∪ (outsOf G h ∩ A) ⊆ A :=
      union_subset inter_subset_right inter_subset_right
    have h1 := ncard_union_eq hdisj (hfinI h) (hfinO h)
    have h2 := ncard_le_ncard hu hA
    omega
  · obtain ⟨x, hxA, hxu⟩ := not_subset.1 hfull
    set h' := h ++ [x] with hh'
    set y := G (h'.take (h.length + 1)) with hy
    have hy1 : y ∉ usedBy G h := out_not_used hG h [x] le_rfl (by simp)
    have hy2 : y ≠ x := by
      have htake : h'.take (h.length + 1) = h' := by simp [hh']
      have h1 := (fresh_list hG h' (t := h.length) (by simp [hh'])).1
      rw [htake] at h1
      intro hyx
      apply h1
      rw [← (show y = G h' by rw [hy, htake]), hyx]
      simp [hh']
    have hins : {z | z ∈ h'} ∩ A = insert x ({z | z ∈ h} ∩ A) := by
      ext z
      simp only [hh', mem_inter_iff, mem_setOf_eq, List.mem_append, List.mem_singleton,
        mem_insert_iff]
      constructor
      · rintro ⟨hz | rfl, hzA⟩
        · exact Or.inr ⟨hz, hzA⟩
        · exact Or.inl rfl
      · rintro (rfl | ⟨hz, hzA⟩)
        · exact ⟨Or.inr rfl, hxA⟩
        · exact ⟨Or.inl hz, hzA⟩
    have houts : outsOf G h' ⊆ insert y (outsOf G h) := by
      intro z hz
      rcases outsOf_append G h [x] hz with hz | ⟨j, hj, rfl⟩
      · exact Or.inr hz
      · simp only [List.length_singleton] at hj
        have : j = 0 := by omega
        subst this
        exact Or.inl rfl
    have hxI : x ∉ {z | z ∈ h} ∩ A := fun hx => hxu (Or.inl hx.1)
    have hcardI : ({z | z ∈ h'} ∩ A).ncard = ({z | z ∈ h} ∩ A).ncard + 1 := by
      rw [hins, ncard_insert_of_notMem hxI (hfinI h)]
    have hcardO : (outsOf G h' ∩ A).ncard ≤ (outsOf G h ∩ A).ncard + 1 := by
      calc (outsOf G h' ∩ A).ncard ≤ (insert y (outsOf G h ∩ A)).ncard := by
            refine ncard_le_ncard ?_ ((hfinO h).insert y)
            rintro z ⟨hz, hzA⟩
            rcases houts hz with rfl | hz
            · exact mem_insert _ _
            · exact Or.inr ⟨hz, hzA⟩
        _ ≤ _ := ncard_insert_le _ _
    have hdisj' : Disjoint ({z | z ∈ h'} ∩ A) (outsOf G h' ∩ A) := by
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
    have hlt : (A \ usedBy G h').ncard < m := by
      rw [← hm]
      refine ncard_lt_ncard ?_ (hA.diff)
      refine (ssubset_iff_of_subset (diff_subset_diff_right (usedBy_mono G h [x]))).2
        ⟨x, ⟨hxA, hxu⟩, fun hx => hx.2 (Or.inl (show x ∈ h ++ [x] by simp))⟩
    obtain ⟨r, hr, hAu, hcount⟩ := ihm _ hlt h' rfl hdisj' (by omega)
    refine ⟨x :: r, ?_, ?_, ?_⟩
    · intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hxA
      · exact hr z hz
    · simpa [hh'] using hAu
    · simpa [hh'] using hcount

/-- **No target has optimum above `1/2`** (§7.5): for `2 ≤ d`, a threshold `h`, a fresh
generator `G`, and `Kp ∈ family7`, there is a full enumeration `w` of `emb2 d '' Kp` with
`deltaH h (G.outputSet w) (emb2 d '' Kp) ≤ 1 / 2`. -/
theorem upper_half (hd : 2 ≤ d) (h : ℕ → ℝ) (hh : IsThreshold h) {G : Generator (Pt d)}
    (hG : G.Fresh) {Kp : Set (ℤ × ℤ)} (hKp : Kp ∈ family7) :
    ∃ w, IsFullEnumeration w (emb2 d '' Kp) ∧ deltaH h (G.outputSet w) (emb2 d '' Kp) ≤ 1 / 2 := by
  -- Finished column segments are internal evidence for the density estimate; their witnesses
  -- are not part of the theorem's exported conclusion.
  set K := emb2 d '' Kp
  have hKinf : K.Infinite := (col0_infinite hKp).image (emb2_inj hd).injOn
  obtain ⟨e, he⟩ : ∃ e : ℕ → Pt d, range e = K := by
    obtain ⟨e, he⟩ := (Set.to_countable K).exists_eq_range hKinf.nonempty
    exact ⟨e, he.symm⟩
  choose mk hmk hmkbound using thr_even hh
  let Nk : ℕ → ℕ := fun k => 2 * mk k
  have hNk1 : ∀ k, 1 ≤ Nk k := fun k => by dsimp [Nk]; have := hmk k; omega
  have hNk2 : ∀ k : ℕ, (k : ℝ) * h (Nk k) ≤ (Nk k : ℝ) := by
    intro k
    dsimp [Nk]
    push_cast
    exact hmkbound k
  choose Bf hBf using fun l : List (Pt d) => ((usedBy_finite G l).image (crd 1)).bddAbove
  let y0 : List (Pt d) → ℤ := fun l => max (Bf l) 0 + 1
  let Aseg : List (Pt d) → ℕ → Set (Pt d) := fun l k =>
    emb2 d '' box 0 0 (y0 l) (y0 l + Nk k - 1)
  have hAfin : ∀ l k, (Aseg l k).Finite := fun l k => (box_finite _ _ _ _).image _
  have hAdisj : ∀ l k, Disjoint (usedBy G l) (Aseg l k) := by
    intro l k
    rw [Set.disjoint_left]
    rintro x hxu ⟨p, hp, rfl⟩
    have := hBf l (mem_image_of_mem _ hxu)
    rw [crd_emb2_1 hd] at this
    simp only [box, mem_setOf_eq, y0] at hp
    omega
  have hAK : ∀ l k, Aseg l k ⊆ K := by
    rintro l k _ ⟨p, hp, rfl⟩
    simp only [box, mem_setOf_eq, y0] at hp
    exact mem_image_of_mem _ (col0_mem hKp (by omega) (by omega) (by omega))
  choose rr hrr1 hrr2 hrr3 using fun l k => race hG (hAfin l k) l (hAdisj l k)
  let step : ℕ → List (Pt d) → List (Pt d) := fun k l => rr l k
  have hstep : ∀ k l, (∀ x ∈ l, x ∈ K) → ∀ x ∈ step k l, x ∈ K :=
    fun k l _ x hx => hAK l k (hrr1 l k x hx)
  obtain ⟨w, hs, hfull, hs0, hs_succ, hw, hsL, hlen⟩ :=
    staged he [] (by simp) step hstep
  refine ⟨w, hfull, deltaH_le_of_tests hh _ K _ fun k => ?_⟩
  set l := hs k ++ [nextPt e (hs k)]
  have hsk : hs (k + 1) = l ++ rr l k := hs_succ k
  set N := Nk k
  have hab : (0 : ℤ) ≤ 0 := le_rfl
  have hce : y0 l ≤ y0 l + N - 1 := by have := hNk1 k; omega
  have hsub : box 0 0 (y0 l) (y0 l + N - 1) ⊆ Kp := by
    intro p hp; simp only [box, mem_setOf_eq, y0] at hp
    exact col0_mem hKp (by omega) (by omega) (by omega)
  obtain ⟨hmass, hcnt⟩ := test_props hd Kp hab hce hsub (G.outputSet w)
  have hsz : ((0 : ℤ) + 1 - 0).toNat * (y0 l + N - 1 + 1 - y0 l).toNat = N := by
    have e2 : y0 l + N - 1 + 1 - y0 l = (N : ℤ) := by ring
    rw [e2, Int.toNat_natCast]; simp
  refine ⟨prect d _ _ _ _ hab hce, ?_, ?_⟩
  · rw [hmass, prect_vol hd, hsz]; exact hNk2 k
  · rw [hcnt, hmass, hsz]
    have hfin : G.outputSet w ∩ Aseg l k = outsOf G (hs (k + 1)) ∩ Aseg l k :=
      outputSet_inter_eq hG (hw (k + 1)) (by rw [hsk]; exact hrr2 l k)
    have hc := hrr3 l k
    rw [← hsk] at hc
    have hAn : (Aseg l k).ncard = N := by
      simp only [Aseg]
      rw [ncard_image_of_injective _ (emb2_inj hd), ncard_box, hsz]
    have hmpos : (0 : ℝ) < (N : ℝ) := by have := hNk1 k; positivity
    rw [div_le_iff₀ hmpos]
    have : (G.outputSet w ∩ emb2 d '' box 0 0 (y0 l) (y0 l + ↑N - 1)).ncard =
        (outsOf G (hs (k + 1)) ∩ Aseg l k).ncard := by
      rw [show emb2 d '' box 0 0 (y0 l) (y0 l + ↑N - 1) = Aseg l k from rfl, hfin]
    rw [this]
    have : (2 * (outsOf G (hs (k + 1)) ∩ Aseg l k).ncard : ℝ) ≤ N := by
      rw [← hAn]; exact_mod_cast hc
    linarith

/-- **The full-grid optimum is at most `1/4`** (§7.5). -/
theorem upper_quarter (hd : 2 ≤ d) (h : ℕ → ℝ) (hh : IsThreshold h) {G : Generator (Pt d)}
    (hG : G ∈ ValidGen (family7d d)) :
    ∃ w, IsFullEnumeration w (K0d d) ∧ deltaH h (G.outputSet w) (K0d d) ≤ 1 / 4 := by
  set K := K0d d
  have hKinf : K.Infinite := (langClass_family7d hd).infinite K (K0d_mem d)
  obtain ⟨e, he⟩ : ∃ e : ℕ → Pt d, range e = K := by
    obtain ⟨e, he⟩ := (Set.to_countable K).exists_eq_range hKinf.nonempty
    exact ⟨e, he.symm⟩
  choose nk hnk1 hnk2 using thr_even hh
  choose ℓf hℓf1 hℓf2 using fun (l : List (Pt d)) (hl : ∀ x ∈ l, x ∈ K) (k : ℕ) =>
    exists_cap hd l hl (nk k)
  choose bext hbext1 hbext2 using fun (l : List (Pt d)) (hl : ∀ x ∈ l, x ∈ K) (k : ℕ) =>
    block hd G hG (hnk1 k) (hℓf1 l hl k) l (hℓf2 l hl k) (nk k) (nk k) le_rfl (hnk1 k)
  let step : ℕ → List (Pt d) → List (Pt d) := fun k l =>
    if hl : ∀ x ∈ l, x ∈ K then bext l hl k else []
  have hstep : ∀ k l, (∀ x ∈ l, x ∈ K) → ∀ x ∈ step k l, x ∈ K := by
    intro k l hl x hx
    simp only [step, dif_pos hl] at hx
    exact strip_sub_K0 (hbext1 l hl k x hx)
  obtain ⟨w, hs, hfull, hs0, hs_succ, hw, hsL, hlen⟩ := staged he [] (by simp) step hstep
  set O := G.outputSet w
  refine ⟨w, hfull, deltaH_le_of_tests hh O K _ fun k => ?_⟩
  set l := hs k ++ [nextPt e (hs k)]
  have hl : ∀ x ∈ l, x ∈ K := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hsL k x hx
    · rw [List.mem_singleton.1 hx]; exact nextPt_mem he _
  have hsk : hs (k + 1) = l ++ bext l hl k := by
    rw [hs_succ]; show l ++ step k l = _; simp only [step, dif_pos hl]
  obtain ⟨T, hF⟩ := hbext2 l hl k
  rw [← hsk] at hF
  set L1 := hs (k + 1)
  set n := nk k
  have hn1 := hnk1 k
  have hcount := block_count hd hG.1 L1 n n T hF
  have hmpos : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by positivity
  -- some test carries at most `n/2` outputs
  by_cases hhor : ∃ j < n, 2 * (hTest d n (T + j) ∩ outsOf G L1).ncard ≤ n
  · obtain ⟨j, hj, hjc⟩ := hhor
    have hab : (2 : ℤ) ≤ 2 * n + 1 := by omega
    have hce : 2 * ((T + j : ℕ) : ℤ) ≤ 2 * (T + j : ℕ) := le_rfl
    have hsub : box 2 (2 * (n : ℤ) + 1) (2 * ((T + j : ℕ) : ℤ)) (2 * (T + j : ℕ)) ⊆ quad := by
      intro p hp; simp only [box, mem_setOf_eq] at hp; simp only [quad, mem_setOf_eq]; omega
    obtain ⟨hmass, hcnt⟩ := test_props hd quad hab hce hsub O
    have hsz : (2 * (n : ℤ) + 1 + 1 - 2).toNat *
        (2 * ((T + j : ℕ) : ℤ) + 1 - 2 * (T + j : ℕ)).toNat = 2 * n := by
      have e1 : 2 * (n : ℤ) + 1 + 1 - 2 = ((2 * n : ℕ) : ℤ) := by push_cast; ring
      have e2 : 2 * ((T + j : ℕ) : ℤ) + 1 - 2 * (T + j : ℕ) = 1 := by ring
      rw [e1, e2, Int.toNat_natCast]; simp
    refine ⟨prect d _ _ _ _ hab hce, ?_, ?_⟩
    · rw [show K = emb2 d '' quad from rfl, hmass, prect_vol hd, hsz]; push_cast; exact hnk2 k
    · rw [show K = emb2 d '' quad from rfl, hcnt, hmass, hsz, ← hTest_eq]
      have hfin : O ∩ hTest d n (T + j) = outsOf G L1 ∩ hTest d n (T + j) :=
        outputSet_inter_eq hG.1 (hw (k + 1)) (hTest_used fun i h1 h2 => hF i h1 h2 j hj)
      rw [div_le_iff₀ hmpos, hfin, inter_comm]
      have : (2 * (hTest d n (T + j) ∩ outsOf G L1).ncard : ℝ) ≤ n := by exact_mod_cast hjc
      push_cast; linarith
  · push Not at hhor
    have hver : ∃ i ∈ Finset.Icc 1 n, 2 * (vTest d i T n ∩ outsOf G L1).ncard ≤ n := by
      by_contra hall
      push Not at hall
      have s1 : ∑ j ∈ Finset.range n, (n + 1) ≤
          ∑ j ∈ Finset.range n, 2 * (hTest d n (T + j) ∩ outsOf G L1).ncard :=
        Finset.sum_le_sum fun j hj => hhor j (Finset.mem_range.1 hj)
      have s2 : ∑ i ∈ Finset.Icc 1 n, (n + 1) ≤
          ∑ i ∈ Finset.Icc 1 n, 2 * (vTest d i T n ∩ outsOf G L1).ncard :=
        Finset.sum_le_sum fun i hi => hall i hi
      rw [← Finset.mul_sum] at s1 s2
      simp only [Finset.sum_const, Finset.card_range, Nat.card_Icc, smul_eq_mul,
        add_tsub_cancel_right] at s1 s2
      nlinarith
    obtain ⟨i, hi, hic⟩ := hver
    have hi' := Finset.mem_Icc.1 hi
    have hab : 2 * (i : ℤ) ≤ 2 * i := le_rfl
    have hce : 2 * (T : ℤ) ≤ 2 * T + 2 * n - 1 := by omega
    have hsub : box (2 * (i : ℤ)) (2 * i) (2 * (T : ℤ)) (2 * T + 2 * n - 1) ⊆ quad := by
      intro p hp; simp only [box, mem_setOf_eq] at hp; simp only [quad, mem_setOf_eq]; omega
    obtain ⟨hmass, hcnt⟩ := test_props hd quad hab hce hsub O
    have hsz : (2 * (i : ℤ) + 1 - 2 * i).toNat * (2 * (T : ℤ) + 2 * n - 1 + 1 - 2 * T).toNat =
        2 * n := by
      have e1 : 2 * (i : ℤ) + 1 - 2 * i = 1 := by ring
      have e2 : 2 * (T : ℤ) + 2 * n - 1 + 1 - 2 * T = ((2 * n : ℕ) : ℤ) := by push_cast; ring
      rw [e1, e2, Int.toNat_natCast]; simp
    refine ⟨prect d _ _ _ _ hab hce, ?_, ?_⟩
    · rw [show K = emb2 d '' quad from rfl, hmass, prect_vol hd, hsz]; push_cast; exact hnk2 k
    · rw [show K = emb2 d '' quad from rfl, hcnt, hmass, hsz]
      have hfin : O ∩ vTest d i T n = outsOf G L1 ∩ vTest d i T n :=
        outputSet_inter_eq hG.1 (hw (k + 1)) (vTest_used fun j hj => hF i hi'.1 hi'.2 j hj)
      have : (O ∩ emb2 d '' box (2 * ↑i) (2 * ↑i) (2 * ↑T) (2 * ↑T + 2 * ↑n - 1)).ncard =
          (vTest d i T n ∩ outsOf G L1).ncard := by
        rw [show emb2 d '' box (2 * ↑i) (2 * ↑i) (2 * ↑T) (2 * ↑T + 2 * ↑n - 1) = vTest d i T n
          from rfl, hfin, inter_comm]
      rw [div_le_iff₀ hmpos, this]
      have : (2 * (vTest d i T n ∩ outsOf G L1).ncard : ℝ) ≤ n := by exact_mod_cast hic
      push_cast; linarith

end Upper

/-! ## The two pairing generators and the separation for `δ_h` -/

section Witness
variable {d : ℕ}

/-- Vertical pairing (§7.3), for the bounded-width targets. -/
noncomputable def G1 (d : ℕ) : Generator (Pt d) := pairGen (fun _ => liftP pv) (fun _ => fbCol)
/-- Checkerboard pairing (§7.3), for the full grid. -/
noncomputable def G0 (d : ℕ) : Generator (Pt d) := pairGen (fun _ => liftP pc) (fun _ => fbCol)

theorem fixedPair_valid (hd : 2 ≤ d) (π : ℤ × ℤ → ℤ × ℤ)
    (hsat : ∀ S : Set (ℤ × ℤ), Sat S → ∀ p ∈ S, π p ∈ S) :
    pairGen (fun _ => liftP π) (fun _ => fbCol) ∈ ValidGen (family7d d) := by
  refine ⟨pairGen_fresh (fun _ => fbCol_inj hd), ?_⟩
  rintro K ⟨Kp, hKp, rfl⟩ w hw
  refine Set.Finite.subset Set.finite_empty fun t ht => ?_
  apply ht
  have hwt : w t ∈ emb2 d '' Kp := by
    have : w t ∈ range w := mem_range_self t
    rwa [show range w = emb2 d '' Kp from hw] at this
  rcases pairGen_out_cases _ _ w t with h | ⟨n, h⟩
  · rw [h]
    obtain ⟨p, hp, hpw⟩ := hwt
    rw [← hpw, liftP_emb2 hd]
    exact mem_image_of_mem _ (hsat _ (sat_family hKp) p hp)
  · rw [h]
    exact mem_image_of_mem _ (col0_mem hKp le_rfl (by norm_num) (by positivity))

theorem G1_valid (hd : 2 ≤ d) : G1 d ∈ ValidGen (family7d d) :=
  fixedPair_valid hd pv fun _ hS _ hp => sat_pv hS hp
theorem G0_valid (hd : 2 ≤ d) : G0 d ∈ ValidGen (family7d d) :=
  fixedPair_valid hd pc fun _ hS _ hp => sat_pc hS hp

/-- The pairing property in planar coordinates. -/
theorem cover_planar (hd : 2 ≤ d) {part : List (Pt d) → Pt d → Pt d}
    {fb : List (Pt d) → ℕ → Pt d} (w : ℕ → Pt d) (Kp : Set (ℤ × ℤ))
    (hw : IsFullEnumeration w (emb2 d '' Kp)) (π : ℤ × ℤ → ℤ × ℤ) (hπ : ∀ p, π (π p) = p)
    (hne : ∀ p, π p ≠ p) (T0 : ℕ)
    (hpart : ∀ t, T0 ≤ t → part (inputsUpTo w t) (w t) = liftP π (w t)) (E : Set (ℤ × ℤ))
    (hE : ∀ t < T0, ∀ q, w t = emb2 d q → q ∈ E) :
    ∀ p ∈ Kp, p ∉ E → π p ∉ E →
      emb2 d p ∈ Generator.outputSet (pairGen part fb) w ∨
        emb2 d (π p) ∈ Generator.outputSet (pairGen part fb) w := by
  intro p hp hpE hqE
  have := pairGen_cover (fb := fb) w (liftP π) T0 hpart (emb2 d p)
    (by rw [liftP_emb2 hd, liftP_emb2 hd, hπ])
    (by rw [liftP_emb2 hd]; exact fun h => hne p (emb2_inj hd h))
    (by rw [hw]; exact mem_image_of_mem _ hp)
    (fun t ht => ⟨fun h => hpE (hE t ht p h),
      fun h => hqE (hE t ht (π p) (by rw [h, liftP_emb2 hd]))⟩)
  rwa [liftP_emb2 hd] at this

theorem G1_guarantee (hd : 2 ≤ d) {h : ℕ → ℝ} (hh : IsThreshold h) {Kp : Set (ℤ × ℤ)}
    (hKp : Kp ∈ family7) (hne : Kp ≠ quad) : Guarantees (dH h) (G1 d) (emb2 d '' Kp) (1 / 2) := by
  intro w hw
  obtain ⟨W, hW⟩ := strip_width hKp hne
  have H := guarantee_planar hd hh Kp ((G1 d).outputSet w) pv pv_pv ∅ finite_empty
    (fun p hp _ h1 h2 => cover_planar hd w Kp hw pv pv_pv pv_ne 0 (fun t _ => rfl) ∅
      (fun t ht => absurd ht (Nat.not_lt_zero t)) p hp h1 h2)
    0 (2 * (W + 1).toNat) le_rfl (fun R => by
      obtain ⟨Z, a, b, c, e, hB⟩ := preimage_pts hd R
      rw [hB]
      have := cut_vertical Kp (sat_family hKp) W hW Z a b c e
      simp only [zero_mul, zero_add]
      exact_mod_cast this)
  simp only [dH, EReal.coe_le_coe_iff]
  linarith

theorem G0_guarantee (hd : 2 ≤ d) {h : ℕ → ℝ} (hh : IsThreshold h) :
    Guarantees (dH h) (G0 d) (K0d d) (1 / 4) := by
  intro w hw
  have H := guarantee_planar hd hh quad ((G0 d).outputSet w) pc pc_pc ∅ finite_empty
    (fun p hp _ h1 h2 => cover_planar hd w quad hw pc pc_pc pc_ne 0 (fun t _ => rfl) ∅
      (fun t ht => absurd ht (Nat.not_lt_zero t)) p hp h1 h2)
    (1 / 2) 6 (by norm_num) (fun R => by
      obtain ⟨Z, a, b, c, e, hB⟩ := preimage_pts hd R
      rw [hB]
      have := cut_checker Z a b c e
      have : (2 * ((quad ∩ {p | Z ∧ p ∈ box a b c e}) \ {p ∈ quad ∩ {p | Z ∧ p ∈ box a b c e} |
          pc p ∈ quad ∩ {p | Z ∧ p ∈ box a b c e}}).ncard : ℝ) ≤
          ((quad ∩ {p | Z ∧ p ∈ box a b c e}).ncard : ℝ) + 12 := by exact_mod_cast this
      linarith)
  simp only [dH, EReal.coe_le_coe_iff]
  rw [K0d_eq]
  linarith

theorem bG_le {D : Set (Pt d) → Set (Pt d) → EReal} {G : Generator (Pt d)} {L : Set (Pt d)}
    {w : ℕ → Pt d} (hw : IsFullEnumeration w L) : bG D G L ≤ D (G.outputSet w) L :=
  iInf_le (fun w : {w : ℕ → Pt d // IsFullEnumeration w L} => D (G.outputSet w.1) L) ⟨w, hw⟩

theorem bOpt_eq_of {D : Set (Pt d) → Set (Pt d) → EReal} {X : Set (Set (Pt d))} {L : Set (Pt d)}
    (val : ℝ) {Gs : Generator (Pt d)} (hGs : Gs ∈ ValidGen X) (hguar : Guarantees D Gs L val)
    (hup : ∀ G ∈ ValidGen X, ∃ w, IsFullEnumeration w L ∧ D (G.outputSet w) L ≤ val) :
    bOpt D X L = val := by
  refine le_antisymm (iSup_le fun G => ?_) (le_iSup_of_le ⟨Gs, hGs⟩ (le_iInf fun w => hguar w.1 w.2))
  obtain ⟨w, hw, hle⟩ := hup G.1 G.2
  exact (bG_le hw).trans hle

theorem ereal_quarter : ((1 / 4 : ℝ) : EReal) = 1 / 4 := by rw [EReal.coe_div]; rfl
theorem ereal_half : ((1 / 2 : ℝ) : EReal) = 1 / 2 := by rw [EReal.coe_div]; rfl

/-- The separation for every admissible threshold, with the witnesses fixed beforehand. -/
theorem sep_dH (hd : 2 ≤ d) (h : ℕ → ℝ) (hh : IsThreshold h) :
    SeparatesWith (dH h) (family7d d) (K0d d) (G0 d) (G1 d) := by
  refine ⟨G0_guarantee hd hh, ?_, fun G hG x y hx hy => prop_tradeoff hd h hh G hG x y hx hy, ?_, ?_⟩
  · rintro K ⟨Kp, hKp, rfl⟩ hne
    exact G1_guarantee hd hh hKp (fun h => hne (by rw [h]; rfl))
  · rw [← ereal_quarter]
    refine bOpt_eq_of _ (G0_valid hd) (G0_guarantee hd hh) fun G hG => ?_
    obtain ⟨w, hw, hle⟩ := upper_quarter hd h hh hG
    exact ⟨w, hw, EReal.coe_le_coe_iff.2 hle⟩
  · rintro K ⟨Kp, hKp, rfl⟩ hne
    have hne' : Kp ≠ quad := fun h => hne (by rw [h]; rfl)
    rw [← ereal_half]
    refine bOpt_eq_of _ (G1_valid hd) (G1_guarantee hd hh hKp hne') fun G hG => ?_
    obtain ⟨w, hw, hle⟩ := upper_half hd h hh hG.1 hKp
    exact ⟨w, hw, EReal.coe_le_coe_iff.2 hle⟩

/-- Transfer of the separation between density notions that agree on the outputs of valid
generators on full enumerations. -/
theorem sep_congr {X : Set (Set (Pt d))} {K0 : Set (Pt d)} {G₀ G₁ : Generator (Pt d)}
    (D D' : Set (Pt d) → Set (Pt d) → EReal)
    (hagree : ∀ G ∈ ValidGen X, ∀ K ∈ X, ∀ w, IsFullEnumeration w K →
      D (G.outputSet w) K = D' (G.outputSet w) K)
    (hK0 : K0 ∈ X) (hG0 : G₀ ∈ ValidGen X) (hG1 : G₁ ∈ ValidGen X)
    (H : SeparatesWith D X K0 G₀ G₁) : SeparatesWith D' X K0 G₀ G₁ := by
  have hguar : ∀ G ∈ ValidGen X, ∀ K ∈ X, ∀ x : ℝ, Guarantees D G K x ↔ Guarantees D' G K x := by
    intro G hG K hK x
    exact forall_congr' fun w => imp_congr_right fun hw => by rw [hagree G hG K hK w hw]
  have hbOpt : ∀ K ∈ X, bOpt D X K = bOpt D' X K := by
    intro K hK
    unfold bOpt bG
    exact iSup_congr fun G => iInf_congr fun w => hagree G.1 G.2 K hK w.1 w.2
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  refine ⟨(hguar _ hG0 _ hK0 _).1 h1, fun K hK hne => (hguar _ hG1 _ hK _).1 (h2 K hK hne),
    fun G hG x y hx hy => h3 G hG x y ((hguar _ hG _ hK0 _).2 hx)
      (fun K hK hne => (hguar _ hG _ hK _).2 (hy K hK hne)), ?_, ?_⟩
  · rw [← hbOpt _ hK0]; exact h4
  · intro K hK hne; rw [← hbOpt _ hK]; exact h5 K hK hne

theorem threshold_one : IsThreshold (fun _ => (1 : ℝ)) := by
  refine ⟨fun _ _ => one_pos, fun _ _ _ _ _ => le_rfl, ?_⟩
  rw [not_bddAbove_iff]
  intro B
  refine ⟨_, ⟨⌈B⌉₊ + 1, mem_Ici.2 (by omega), rfl⟩, ?_⟩
  simp only [div_one]; push_cast
  linarith [Nat.le_ceil B]

theorem threshold_filter {g : ℝ → ℝ} {τ : ℝ} (hτ : 0 < τ) (hg : GoodG g)
    (hB : ¬ BddAbove ((fun n : ℕ => (n : ℝ) / filterFn g τ n) '' Ici 1)) :
    IsThreshold (filterFn g τ) := by
  have hlog : ∀ n : ℕ, 0 < Real.log (2 + n) := fun n =>
    Real.log_pos (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  refine ⟨fun n hn => ?_, fun a ha b hb hab => ?_, hB⟩
  · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hgn := hg.1 n this
    exact mul_pos (by linarith) (Real.rpow_pos_of_pos (hlog n) _)
  · have ha' : (1 : ℝ) ≤ a := by exact_mod_cast (mem_Ici.1 ha)
    have hb' : (1 : ℝ) ≤ b := by exact_mod_cast (mem_Ici.1 hb)
    have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
    have h1 : g a ≤ g b := hg.2.1 (mem_Ici.2 ha') (mem_Ici.2 hb') hab'
    have h2 : Real.log (2 + a) ^ (1 + τ) ≤ Real.log (2 + b) ^ (1 + τ) :=
      Real.rpow_le_rpow (hlog a).le (Real.log_le_log (by linarith) (by linarith)) (by linarith)
    exact mul_le_mul h1 h2 (Real.rpow_pos_of_pos (hlog a) _).le (by linarith [hg.1 b hb'])

theorem filtered_eq {g : ℝ → ℝ} {τ : ℝ} (O K : Set (Pt d)) :
    filtered g τ (O ∩ K) K = deltaH (filterFn g τ) O K := by
  unfold filtered deltaH
  congr 1
  funext s
  unfold testInf
  rw [show O ∩ K ∩ K = O ∩ K by rw [inter_assoc, inter_self]]

theorem outputs_outside_finite {G : Generator (Pt d)} {K : Set (Pt d)} {w : ℕ → Pt d}
    (hv : G.EventuallyValid w K) : (G.outputSet w \ K).Finite := by
  refine (hv.image (G.out w)).subset ?_
  rintro _ ⟨⟨t, rfl⟩, hK⟩
  exact ⟨t, hK, rfl⟩

theorem family_nonneg : ∀ L ∈ family7d d, ∀ x ∈ L, ∀ i, 0 ≤ x i := by
  rintro L ⟨Lp, hLp, rfl⟩ x ⟨p, hp, rfl⟩ i
  have := family_sub_quad hLp hp
  simp only [quad, mem_setOf_eq] at this
  simp only [emb2]; split_ifs <;> omega

end Witness

/-! ## Remark 3: the strip-only family -/

section Orientation
variable {d : ℕ}

/-- `max(0, largest coordinate i among the inputs)`: the fold is seeded with `0`, so the value is
`0` for no inputs and is never negative. -/
def maxc (i : ℕ) (l : List (Pt d)) : ℤ := l.foldr (fun x m => max (crd i x) m) 0

theorem le_maxc (i : ℕ) {l : List (Pt d)} {x : Pt d} (hx : x ∈ l) : crd i x ≤ maxc i l := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    simp only [maxc, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_max_left _ _
    · exact (ih hx).trans (le_max_right _ _)

theorem maxc_le (i : ℕ) {l : List (Pt d)} {B : ℤ} (hB : 0 ≤ B) (h : ∀ x ∈ l, crd i x ≤ B) :
    maxc i l ≤ B := by
  induction l with
  | nil => simpa [maxc] using hB
  | cons a l ih =>
    simp only [maxc, List.foldr_cons] at ih ⊢
    exact max_le (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

/-- Vertical mode: the inputs reach higher than they reach right. -/
def vmode (l : List (Pt d)) : Prop := maxc 0 l < maxc 1 l

/-- The orientation-guessing generator of Remark 3. -/
noncomputable def Gor (d : ℕ) : Generator (Pt d) :=
  pairGen (fun l => if vmode l then liftP pv else liftP ph)
    (fun l => if vmode l then fbCol else fbRow)

theorem Gor_fresh (hd : 2 ≤ d) : (Gor d).Fresh := by
  refine pairGen_fresh fun l => ?_
  split_ifs
  · exact fbCol_inj hd
  · exact fbRow_inj hd

theorem mem_inputsUpTo (w : ℕ → Pt d) {s t : ℕ} (h : s ≤ t) : w s ∈ inputsUpTo w t := by
  simp only [inputsUpTo, List.mem_ofFn]
  exact ⟨⟨s, by omega⟩, rfl⟩

theorem inputsUpTo_sub {w : ℕ → Pt d} {K : Set (Pt d)} (hw : IsFullEnumeration w K) (t : ℕ) :
    ∀ x ∈ inputsUpTo w t, x ∈ K := by
  intro x hx
  simp only [inputsUpTo, List.mem_ofFn] at hx
  obtain ⟨s, rfl⟩ := hx
  rw [← hw]; exact mem_range_self _

theorem sat_swap {S : Set (ℤ × ℤ)} (hS : Sat S) : Sat (Prod.swap '' S) := by
  rintro p q h1 h2 ⟨r, hr, rfl⟩
  refine ⟨q.swap, hS r q.swap h2 h1 hr, Prod.swap_swap q⟩

theorem ph_swap (p : ℤ × ℤ) : ph p.swap = (pv p).swap := rfl

/-- Eventually the generator plays the correct orientation, on a vertical or a horizontal target
of bounded width `W`. -/
theorem eventually_mode (hd : 2 ≤ d) {Kp : Set (ℤ × ℤ)} (hKp : Kp ∈ family7) (hne : Kp ≠ quad)
    (vert : Bool) {w : ℕ → Pt d}
    (hw : IsFullEnumeration w (emb2 d '' (if vert then Kp else Prod.swap '' Kp))) :
    ∃ T1, ∀ t, T1 ≤ t → (vmode (inputsUpTo w t) ↔ vert = true) := by
  obtain ⟨W, hW⟩ := strip_width hKp hne
  have hW0 : 0 ≤ W := (hW (0, 0) (col0_mem hKp le_rfl (by norm_num) le_rfl)).2
  have hfar : (0, W + 1) ∈ Kp := col0_mem hKp le_rfl (by norm_num) (by omega)
  cases vert with
  | true =>
    simp only [if_true] at hw
    obtain ⟨t1, ht1⟩ : emb2 d (0, W + 1) ∈ range w := by rw [hw]; exact mem_image_of_mem _ hfar
    refine ⟨t1, fun t ht => ?_⟩
    simp only [iff_true, vmode]
    have h1 := le_maxc 1 (mem_inputsUpTo w ht)
    rw [ht1, crd_emb2_1 hd] at h1
    have h0 : maxc 0 (inputsUpTo w t) ≤ W := by
      refine maxc_le 0 hW0 fun x hx => ?_
      obtain ⟨p, hp, rfl⟩ := inputsUpTo_sub hw t x hx
      rw [crd_emb2_0 hd]; exact (hW p hp).2
    simp only at h1
    omega
  | false =>
    simp only [Bool.false_eq_true, if_false] at hw
    obtain ⟨t1, ht1⟩ : emb2 d (W + 1, 0) ∈ range w := by
      rw [hw]; exact mem_image_of_mem _ ⟨_, hfar, rfl⟩
    refine ⟨t1, fun t ht => ?_⟩
    simp only [Bool.false_eq_true, iff_false, vmode, not_lt]
    have h1 := le_maxc 0 (mem_inputsUpTo w ht)
    rw [ht1, crd_emb2_0 hd] at h1
    have h0 : maxc 1 (inputsUpTo w t) ≤ W := by
      refine maxc_le 1 hW0 fun x hx => ?_
      obtain ⟨q, ⟨p, hp, rfl⟩, rfl⟩ := inputsUpTo_sub hw t x hx
      rw [crd_emb2_1 hd]; exact (hW p hp).2
    simp only at h1
    omega

theorem Gor_eq : Gor d = pairGen (fun l => if vmode l then liftP pv else liftP ph)
    (fun l => if vmode l then fbCol else fbRow) := rfl

theorem Gor_valid (hd : 2 ≤ d) : Gor d ∈ ValidGen (stripFamily d) := by
  refine ⟨Gor_fresh hd, ?_⟩
  rintro K ⟨Lp, hLp, rfl⟩ w hw
  beta_reduce at hw ⊢
  rw [Gor_eq]
  rcases hLp with ⟨hKp, hne⟩ | ⟨Kp, ⟨hKp, hne⟩, rfl⟩
  · obtain ⟨T1, hT1⟩ := eventually_mode hd hKp hne true (w := w) (by simpa using hw)
    refine (Set.finite_lt_nat T1).subset fun t ht => ?_
    by_contra hlt
    simp only [mem_setOf_eq, not_lt] at hlt
    apply ht
    have hm := (hT1 t hlt).2 rfl
    have hwt : w t ∈ emb2 d '' Lp := by rw [← hw]; exact mem_range_self t
    rcases pairGen_out_cases _ _ w t with h | ⟨n, h⟩
    · rw [h, if_pos hm]
      obtain ⟨p, hp, hpw⟩ := hwt
      rw [← hpw, liftP_emb2 hd]
      exact mem_image_of_mem _ (sat_pv (sat_family hKp) hp)
    · rw [h, if_pos hm]
      exact mem_image_of_mem _ (col0_mem hKp le_rfl (by norm_num) (by positivity))
  · obtain ⟨T1, hT1⟩ := eventually_mode hd hKp hne false (w := w) (by simpa using hw)
    refine (Set.finite_lt_nat T1).subset fun t ht => ?_
    by_contra hlt
    simp only [mem_setOf_eq, not_lt] at hlt
    apply ht
    have hm : ¬ vmode (inputsUpTo w t) := fun h => by simpa using (hT1 t hlt).1 h
    have hwt : w t ∈ emb2 d '' (Prod.swap '' Kp) := by rw [← hw]; exact mem_range_self t
    rcases pairGen_out_cases _ _ w t with h | ⟨n, h⟩
    · rw [h, if_neg hm]
      obtain ⟨_, ⟨p, hp, rfl⟩, hpw⟩ := hwt
      rw [← hpw, liftP_emb2 hd, ph_swap]
      exact mem_image_of_mem _ ⟨_, sat_pv (sat_family hKp) hp, rfl⟩
    · rw [h, if_neg hm]
      exact mem_image_of_mem _ ⟨((0 : ℤ), (n : ℤ)),
        col0_mem hKp le_rfl (by norm_num) (by positivity), rfl⟩

theorem Gor_guarantee (hd : 2 ≤ d) {h : ℕ → ℝ} (hh : IsThreshold h) :
    ∀ K ∈ stripFamily d, Guarantees (dH h) (Gor d) K (1 / 2) := by
  rintro K ⟨Lp, hLp, rfl⟩ w hw
  have hEfin : ∀ T1, (emb2 d ⁻¹' (w '' Iio T1)).Finite := fun T1 =>
    ((Set.finite_Iio T1).image w).preimage (emb2_inj hd).injOn
  have hE : ∀ T1, ∀ t < T1, ∀ q, w t = emb2 d q → q ∈ emb2 d ⁻¹' (w '' Iio T1) :=
    fun T1 t ht q hq => ⟨t, ht, hq⟩
  simp only [dH, EReal.coe_le_coe_iff]
  rcases hLp with ⟨hKp, hne⟩ | ⟨Kp, ⟨hKp, hne⟩, rfl⟩
  · obtain ⟨T1, hT1⟩ := eventually_mode hd hKp hne true (w := w) (by simpa using hw)
    obtain ⟨W, hW⟩ := strip_width hKp hne
    have H := guarantee_planar hd hh Lp ((Gor d).outputSet w) pv pv_pv _ (hEfin T1)
      (fun p hp _ h1 h2 => cover_planar hd w Lp hw pv pv_pv pv_ne T1
        (fun t ht => by rw [if_pos ((hT1 t ht).2 rfl)]) _ (hE T1) p hp h1 h2)
      0 (2 * (W + 1).toNat) le_rfl (fun R => by
        obtain ⟨Z, a, b, c, e, hB⟩ := preimage_pts hd R
        rw [hB]
        have := cut_vertical Lp (sat_family hKp) W hW Z a b c e
        simp only [zero_mul, zero_add]
        exact_mod_cast this)
    linarith
  · obtain ⟨T1, hT1⟩ := eventually_mode hd hKp hne false (w := w) (by simpa using hw)
    obtain ⟨W, hW⟩ := strip_width hKp hne
    have hW' : ∀ p ∈ Prod.swap '' Kp, 0 ≤ p.2 ∧ p.2 ≤ W := by
      rintro _ ⟨p, hp, rfl⟩; exact hW p hp
    have H := guarantee_planar hd hh (Prod.swap '' Kp) ((Gor d).outputSet w) ph ph_ph _ (hEfin T1)
      (fun p hp _ h1 h2 => cover_planar hd w _ hw ph ph_ph ph_ne T1
        (fun t ht => by
          have : ¬ vmode (inputsUpTo w t) := fun h => by simpa using (hT1 t ht).1 h
          rw [if_neg this]) _ (hE T1) p hp h1 h2)
      0 (2 * (W + 1).toNat) le_rfl (fun R => by
        obtain ⟨Z, a, b, c, e, hB⟩ := preimage_pts hd R
        rw [hB]
        have := cut_horizontal _ (sat_swap (sat_family hKp)) W hW' Z a b c e
        simp only [zero_mul, zero_add]
        exact_mod_cast this)
    linarith

end Orientation

end SeparationAux

/-! ## Theorems 1.13, 7.1, 7.2 and Remark 3 -/

/-- The construction behind Theorem 7.2 (§7.2–7.3): the concrete family of §7.2 and `K₀ = ℕ²`
are the witnesses. Not a numbered statement; it fixes the objects that Remark 3 refers to. -/
theorem family7_witnesses (d : ℕ) (hd : 2 ≤ d) :
    LangClass (family7d d) ∧ K0d d ∈ family7d d ∧
    ∃ G₀ G₁ : Generator (Pt d), G₀ ∈ ValidGen (family7d d) ∧ G₁ ∈ ValidGen (family7d d) ∧
      ∀ h : ℕ → ℝ, IsThreshold h → SeparatesWith (dH h) (family7d d) (K0d d) G₀ G₁ := by
  exact ⟨SeparationAux.langClass_family7d hd, SeparationAux.K0d_mem d, SeparationAux.G0 d,
    SeparationAux.G1 d, SeparationAux.G0_valid hd, SeparationAux.G1_valid hd,
    fun h hh => SeparationAux.sep_dH hd h hh⟩

/-- **Theorem 1.13** (`thm:intro-higher-nonsimultaneous`), in a uniform form with exact optima:
`∀ d ≥ 2, ∃ (X, K₀, G₀, G₁), ∀` density notion (ordinary, every admissible filtered one, every
admissible `δ_h`): the guarantees, the trade-off, and the exact optima.
The generators precede the density notion in the quantifier order. 
-/
theorem thm_intro_higher_nonsimultaneous (d : ℕ) (hd : 2 ≤ d) :
    ∃ (X : Set (Set (Pt d))) (K₀ : Set (Pt d)) (G₀ G₁ : Generator (Pt d)),
      LangClass X ∧ K₀ ∈ X ∧ G₀ ∈ ValidGen X ∧ G₁ ∈ ValidGen X ∧
      SeparatesWith banach X K₀ G₀ G₁ ∧
      (∀ (g : ℝ → ℝ) (τ : ℝ), 0 < τ → GoodG g →
          ¬ BddAbove ((fun n : ℕ => (n : ℝ) / filterFn g τ n) '' Ici 1) →
          SeparatesWith (fun O K => ((filtered g τ (O ∩ K) K : ℝ) : EReal)) X K₀ G₀ G₁) ∧
      (∀ h : ℕ → ℝ, IsThreshold h → SeparatesWith (dH h) X K₀ G₀ G₁) := by
  obtain ⟨hX, hK, G₀, G₁, hG0, hG1, hsep⟩ := family7_witnesses d hd
  refine ⟨family7d d, K0d d, G₀, G₁, hX, hK, hG0, hG1, ?_, ?_, hsep⟩
  · refine SeparationAux.sep_congr (dH fun _ => (1 : ℝ)) banach ?_ hK hG0 hG1
      (hsep _ SeparationAux.threshold_one)
    intro G hG K hKX w hw
    exact (banach_eq_deltaH_one _ K (hX.infinite K hKX)
      (SeparationAux.outputs_outside_finite (hG.2 K hKX w hw))).symm
  · intro g τ hτ hg hB
    refine SeparationAux.sep_congr (dH (filterFn g τ)) _ ?_ hK hG0 hG1
      (hsep _ (SeparationAux.threshold_filter hτ hg hB))
    intro G _ K _ w _
    simp only [dH]
    rw [SeparationAux.filtered_eq]

/-- **Theorem 7.1** (`thm:general`), in uniform form: one family in `ℕ^d` and
one `c > 0` for every admissible threshold. -/
theorem thm_general (d : ℕ) (hd : 2 ≤ d) :
    ∃ (X : Set (Set (Pt d))) (c : ℝ), LangClass X ∧ (∀ L ∈ X, ∀ x ∈ L, ∀ i, 0 ≤ x i) ∧ 0 < c ∧
      ∀ h : ℕ → ℝ, IsThreshold h →
        ∀ G ∈ ValidGen X, ∃ L ∈ X, bG (dH h) G L ≤ bOpt (dH h) X L - (c : EReal) := by
  obtain ⟨hX, hK, G₀, G₁, -, -, hsep⟩ := family7_witnesses d hd
  refine ⟨family7d d, 1 / 16, hX, SeparationAux.family_nonneg, by norm_num, fun h hh G hG => ?_⟩
  obtain ⟨-, -, h3, h4, h5⟩ := hsep h hh
  by_contra hcon
  push Not at hcon
  have e1 : (1 / 4 : EReal) - ((1 / 16 : ℝ) : EReal) = ((3 / 16 : ℝ) : EReal) := by
    rw [← SeparationAux.ereal_quarter, ← EReal.coe_sub]; congr 1; norm_num
  have e2 : (1 / 2 : EReal) - ((1 / 16 : ℝ) : EReal) = ((7 / 16 : ℝ) : EReal) := by
    rw [← SeparationAux.ereal_half, ← EReal.coe_sub]; congr 1; norm_num
  have g0 : Guarantees (dH h) G (K0d d) (3 / 16) := by
    intro w hw
    have := hcon _ hK
    rw [h4, e1] at this
    exact this.le.trans (SeparationAux.bG_le hw)
  have g1 : ∀ K ∈ family7d d, K ≠ K0d d →
      Guarantees (dH h) G K (7 / 16) := by
    intro K hK hne w hw
    have := hcon K hK
    rw [h5 K hK hne, e2] at this
    exact this.le.trans (SeparationAux.bG_le hw)
  have := h3 G hG _ _ g0 g1
  norm_num at this


/-- **Theorem 7.2** (`thm:main-not-simul`), in a uniform form with exact optima: one family in
`ℕ^d`, one `L₀`, and two generators `G₀, G₁` eventually valid on the family, all chosen before
`h`; for every admissible `h`: the two guarantees, the exact optima `1/4` and `1/2`, and the
trade-off `x + y ≤ 1/2`. 
-/
theorem thm_main_not_simul (d : ℕ) (hd : 2 ≤ d) :
    ∃ (X : Set (Set (Pt d))) (L₀ : Set (Pt d)) (G₀ G₁ : Generator (Pt d)),
      LangClass X ∧ (∀ L ∈ X, ∀ x ∈ L, ∀ i, 0 ≤ x i) ∧ L₀ ∈ X ∧
      G₀ ∈ ValidGen X ∧ G₁ ∈ ValidGen X ∧
      ∀ h : ℕ → ℝ, IsThreshold h → SeparatesWith (dH h) X L₀ G₀ G₁ := by
  obtain ⟨hX, hK, G₀, G₁, hG0, hG1, hsep⟩ := family7_witnesses d hd
  exact ⟨family7d d, K0d d, G₀, G₁, hX, SeparationAux.family_nonneg, hK, hG0, hG1, hsep⟩


/-- The strip-only family of Remark 3 is a language class: nonempty, countable, every member
infinite (`d ≥ 2`). This independently establishes the family's non-vacuity;
`rem_orientation` invokes `SeparationAux.Gor_valid` and `SeparationAux.Gor_guarantee` directly. -/
theorem stripFamily_langClass (d : ℕ) (hd : 2 ≤ d) : LangClass (stripFamily d) :=
  open SeparationAux in
  { nonempty := ⟨_, cappedStrip 1 1, Or.inl ⟨strip_mem le_rfl le_rfl, strip_ne_quad 1 1⟩, rfl⟩
    countable := by
      refine Set.Countable.image ?_ _
      exact (family7_countable.mono diff_subset).union
        ((family7_countable.mono diff_subset).image _)
    infinite := by
      rintro L ⟨Lp, hLp, rfl⟩
      refine Set.Infinite.image (emb2_inj hd).injOn ?_
      rcases hLp with ⟨hLp, -⟩ | ⟨Kp, ⟨hKp, -⟩, rfl⟩
      · exact col0_infinite hLp
      · exact (col0_infinite hKp).image Prod.swap_injective.injOn }

/-- **Remark 3** (`sec:orientation`), secondary result: one generator, chosen before `h`,
guarantees `δ_h ≥ 1/2` at every language of the strip-only family, for every admissible `h`
(the family is a language class by `stripFamily_langClass`, so this is not vacuous). 
-/
theorem rem_orientation (d : ℕ) (hd : 2 ≤ d) :
    ∃ G ∈ ValidGen (stripFamily d), ∀ h : ℕ → ℝ, IsThreshold h →
      ∀ K ∈ stripFamily d, Guarantees (dH h) G K (1 / 2) := by
  exact ⟨SeparationAux.Gor d, SeparationAux.Gor_valid hd,
    fun h hh K hK => SeparationAux.Gor_guarantee hd hh K hK⟩


/-- **Lemma 7.4** (`lem:block`): for a generator eventually valid on the family of §7.2, a capped
strip `V_{k,ℓ}` and any finite sequence of adversary inputs from it (repetitions allowed, as in the
paper), the adversary can add finitely many inputs from `V_{k,ℓ}`
producing an `n × m` block of cells, in cell-columns
`1,…,n` and some `m` consecutive cell-rows, each of which is forced (`CellForced`). -/
theorem lem_block {d : ℕ} (hd : 2 ≤ d) (G : Generator (Pt d)) (hG : G ∈ ValidGen (family7d d))
    {k ℓ : ℕ} (hk : 1 ≤ k) (hkℓ : k ≤ ℓ) (xs : List (Pt d))
    (hxV : ∀ x ∈ xs, x ∈ emb2 d '' cappedStrip k ℓ) (n m : ℕ) (hn : 1 ≤ n) (hnk : n ≤ k)
    (hm : 1 ≤ m) :
    ∃ ext : List (Pt d), (∀ x ∈ ext, x ∈ emb2 d '' cappedStrip k ℓ) ∧
      ∃ T : ℕ, ∀ i, 1 ≤ i → i ≤ n → ∀ j < m, CellForced G (xs ++ ext) i (T + j) := by
  exact SeparationAux.block hd G hG hk hkℓ xs hxV n m hnk hm


end BanachDensityHD
