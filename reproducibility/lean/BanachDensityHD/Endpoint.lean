import BanachDensityHD.FiniteRank

/-!
# Section 10: the half-density endpoint

Kleinberg–Wei, *Characterizing Local Breadth in Language Generation*.
Historical source numbering is retained; current mappings are in the release registry.

-/

namespace BanachDensityHD

open Set Filter
open scoped Classical

/-- The strip `[a, a+N-1] × [b, b+s-1]` in the plane of coordinates `0, 1`, all other coordinates
equal to those of `base` (`base 0 = a`, `base 1 = b`): rows of length `N`, columns of length `s`. -/
def strip {d : ℕ} (base : Pt d) (s N : ℕ) : Set (Pt d) :=
  {x | ∀ i : Fin d, (i.val = 0 → x i ∈ Icc (base i) (base i + N - 1)) ∧
      (i.val = 1 → x i ∈ Icc (base i) (base i + s - 1)) ∧ (2 ≤ i.val → x i = base i)}

/-- The slice of `strip base s N` at first coordinate `c`. For `d ≥ 2`, it has `s`
points when `c` lies in the strip's first-coordinate interval, and is empty otherwise.
In smaller dimensions its size follows the coordinate predicate below. -/
def stripCol {d : ℕ} (base : Pt d) (s N : ℕ) (c : ℤ) : Set (Pt d) :=
  {x ∈ strip base s N | ∀ i : Fin d, i.val = 0 → x i = c}

/-- The slice of `strip base s N` at second coordinate `c`. For `d ≥ 2`, it has `N`
points when `c` lies in the strip's second-coordinate interval, and is empty otherwise.
In smaller dimensions its size follows the coordinate predicate below. -/
def stripRow {d : ℕ} (base : Pt d) (s N : ℕ) (c : ℤ) : Set (Pt d) :=
  {x ∈ strip base s N | ∀ i : Fin d, i.val = 1 → x i = c}

/-- A causal White responder: from Black's claims so far (in order, the current one last), its
reply, which may lie anywhere in `ℤ^d`. -/
abbrev Responder (d : ℕ) := List (Pt d) → Pt d

/-- A causal Black strategy: from White's replies so far, the next claim, or `none` to stop. -/
abbrev BlackStrat (d : ℕ) := List (Pt d) → Option (Pt d)

/-- White's replies are fresh: never a point of `U₀` (used before the strip game), never one of
Black's claims so far, never an earlier reply. -/
def FreshResponder {d : ℕ} (U₀ : Set (Pt d)) (ω : Responder d) : Prop :=
  ∀ bs : List (Pt d), bs ≠ [] → ω bs ∉ U₀ ∧ ω bs ∉ bs ∧
    ∀ i, 1 ≤ i → i < bs.length → ω (bs.take i) ≠ ω bs

/-- The play of `β` against `ω` for `k` rounds: Black's claims and White's replies (it stops
when `β` returns `none`). -/
def stripRun {d : ℕ} (β : BlackStrat d) (ω : Responder d) : ℕ → List (Pt d) × List (Pt d)
  | 0 => ([], [])
  | k + 1 =>
      let p := stripRun β ω k
      match β p.2 with
      | none => p
      | some x => (p.1 ++ [x], p.2 ++ [ω (p.1 ++ [x])])

namespace EndpointAux

section StripProof

variable {d : ℕ}

/-- The point of the strip in column `c` and row `r` (offsets from `base`). -/
def spt (base : Pt d) (c r : ℕ) : Pt d :=
  fun i => if i.val = 0 then base i + c else if i.val = 1 then base i + r else base i

theorem spt_inj (hd : 2 ≤ d) {base : Pt d} {c r c' r' : ℕ} (h : spt base c r = spt base c' r') :
    c = c' ∧ r = r' := by
  have h0 := congrFun h ⟨0, by omega⟩
  have h1 := congrFun h ⟨1, by omega⟩
  simp only [spt, if_true, show (1 : ℕ) ≠ 0 by omega, if_false] at h0 h1
  omega

theorem mem_strip (hd : 2 ≤ d) {base : Pt d} {s N : ℕ} {x : Pt d} :
    x ∈ strip base s N ↔ ∃ c < N, ∃ r < s, spt base c r = x := by
  constructor
  · intro hx
    have h0 := (hx ⟨0, by omega⟩).1 rfl
    have h1 := (hx ⟨1, by omega⟩).2.1 rfl
    simp only [Set.mem_Icc] at h0 h1
    refine ⟨(x ⟨0, by omega⟩ - base ⟨0, by omega⟩).toNat, by omega,
      (x ⟨1, by omega⟩ - base ⟨1, by omega⟩).toNat, by omega, ?_⟩
    funext i
    simp only [spt]
    split_ifs with hi0 hi1
    · have : i = ⟨0, by omega⟩ := Fin.ext hi0
      rw [this]; omega
    · have : i = ⟨1, by omega⟩ := Fin.ext hi1
      rw [this]; omega
    · exact ((hx i).2.2 (by omega)).symm
  · rintro ⟨c, hc, r, hr, rfl⟩ i
    simp only [spt, Set.mem_Icc]
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · rw [if_pos h]; omega
    · rw [if_neg (by omega), if_pos h]; omega
    · rw [if_neg (by omega), if_neg (by omega)]

theorem stripCol_eq (hd : 2 ≤ d) {base : Pt d} {s N c : ℕ} (hc : c < N) :
    stripCol base s N (base ⟨0, by omega⟩ + c) = (spt base c) '' Set.Iio s := by
  ext x
  simp only [stripCol, Set.mem_setOf_eq, Set.mem_image, Set.mem_Iio]
  constructor
  · rintro ⟨hx, hc0⟩
    obtain ⟨c', hc', r, hr, rfl⟩ := (mem_strip hd).1 hx
    have := hc0 ⟨0, by omega⟩ rfl
    simp only [spt, if_true] at this
    have hcc : c' = c := by omega
    subst hcc
    exact ⟨r, hr, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    refine ⟨(mem_strip hd).2 ⟨c, hc, r, hr, rfl⟩, fun i hi => ?_⟩
    have : i = ⟨0, by omega⟩ := Fin.ext hi
    rw [this]
    simp [spt]

theorem stripRow_eq (hd : 2 ≤ d) {base : Pt d} {s N r : ℕ} (hr : r < s) :
    stripRow base s N (base ⟨1, by omega⟩ + r) = (fun c => spt base c r) '' Set.Iio N := by
  ext x
  simp only [stripRow, Set.mem_setOf_eq, Set.mem_image, Set.mem_Iio]
  constructor
  · rintro ⟨hx, hr0⟩
    obtain ⟨c, hc, r', hr', rfl⟩ := (mem_strip hd).1 hx
    have := hr0 ⟨1, by omega⟩ rfl
    simp only [spt, show (1 : ℕ) ≠ 0 by omega, if_false, if_true] at this
    have hrr : r' = r := by omega
    subst hrr
    exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    refine ⟨(mem_strip hd).2 ⟨c, hc, r, hr, rfl⟩, fun i hi => ?_⟩
    have : i = ⟨1, by omega⟩ := Fin.ext hi
    rw [this]
    simp [spt]

theorem ncard_image_Iio {f : ℕ → Pt d} (hf : Function.Injective f) (n : ℕ) :
    (f '' Set.Iio n).ncard = n := by
  rw [Set.ncard_image_of_injective _ hf, ← Finset.coe_range, Set.ncard_coe_finset,
    Finset.card_range]

/-- The row weights `w_0 = 2^{s-2}`, `w_r = 2^{s-2} - 2^{r-1}` (rows numbered from `0`). -/
def wgt (s r : ℕ) : ℤ := if r = 0 then 2 ^ (s - 2) else 2 ^ (s - 2) - 2 ^ (r - 1)

theorem wgt_anti (s : ℕ) {r r' : ℕ} (h : r ≤ r') : wgt s r' ≤ wgt s r := by
  unfold wgt
  split_ifs with h1 h2 h2
  · omega
  · omega
  · have : (0 : ℤ) < 2 ^ (r' - 1) := by positivity
    linarith
  · have : (2 : ℤ) ^ (r - 1) ≤ 2 ^ (r' - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith

theorem wgt_nonneg {s r : ℕ} (hr : r < s) : 0 ≤ wgt s r := by
  unfold wgt
  split_ifs
  · positivity
  · have : (2 : ℤ) ^ (r - 1) ≤ 2 ^ (s - 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith

theorem wgt_zero_pos (s : ℕ) : 0 < wgt s 0 := by
  unfold wgt; simp

theorem wgt_step {s j : ℕ} (hj : 1 ≤ j) : wgt s j - wgt s (j + 1) = 2 ^ (j - 1) := by
  unfold wgt
  rw [if_neg (by omega), if_neg (by omega)]
  have : (2 : ℤ) ^ (j + 1 - 1) = 2 * 2 ^ (j - 1) := by
    rw [show j + 1 - 1 = (j - 1) + 1 by omega, pow_succ]; ring
  rw [this]; ring

theorem wgt_zero_sub {s j : ℕ} (hj : 1 ≤ j) : wgt s 0 - wgt s j = 2 ^ (j - 1) := by
  unfold wgt
  rw [if_pos rfl, if_neg (by omega)]
  ring

/-- Row `r` of the strip. -/
def rowSet (base : Pt d) (N r : ℕ) : Set (Pt d) := (fun c => spt base c r) '' Set.Iio N

/-- Sum the weights of all rows containing the point. For `d ≥ 2` the rows are
distinct, giving `w_r` on row `r` and `0` outside the strip. In dimension `1` row sets
can coincide and their contributions add; the displayed sum defines that extension. -/
noncomputable def wt (base : Pt d) (s N : ℕ) (x : Pt d) : ℤ :=
  ∑ r ∈ Finset.range s, if x ∈ rowSet base N r then wgt s r else 0

theorem wt_spt (hd : 2 ≤ d) {base : Pt d} {s N c r : ℕ} (hc : c < N) (hr : r < s) :
    wt base s N (spt base c r) = wgt s r := by
  unfold wt
  rw [Finset.sum_eq_single r]
  · rw [if_pos ⟨c, hc, rfl⟩]
  · intro r' _ hr'
    rw [if_neg]
    rintro ⟨c', _, h⟩
    exact hr' (spt_inj hd h).2
  · intro h; exact absurd (Finset.mem_range.2 hr) h

theorem wt_out {base : Pt d} {s N : ℕ} {x : Pt d} (hx : ¬ ∃ c < N, ∃ r < s, spt base c r = x) :
    wt base s N x = 0 := by
  unfold wt
  refine Finset.sum_eq_zero fun r hr => if_neg ?_
  rintro ⟨c, hc, h⟩
  exact hx ⟨c, hc, r, Finset.mem_range.1 hr, h⟩

theorem wt_le_wgt_zero (hd : 2 ≤ d) {base : Pt d} {s N : ℕ} (x : Pt d) :
    wt base s N x ≤ wgt s 0 := by
  by_cases hx : ∃ c < N, ∃ r < s, spt base c r = x
  · obtain ⟨c, hc, r, hr, rfl⟩ := hx
    rw [wt_spt hd hc hr]; exact wgt_anti s (Nat.zero_le _)
  · rw [wt_out hx]; exact (wgt_zero_pos s).le

/-- The weighted count of a duplicate-free list, row by row. -/
theorem sum_wt (base : Pt d) (s N : ℕ) {L : List (Pt d)} (hL : L.Nodup) :
    (L.map (wt base s N)).sum =
      ∑ r ∈ Finset.range s, wgt s r * ((rowSet base N r ∩ {x | x ∈ L}).ncard : ℤ) := by
  rw [← List.sum_toFinset _ hL]
  unfold wt
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 2
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x
  simp [and_comm]


/-! ### Black's strategy in the strip game (Lemma 10.2) -/

/-- Column `c` holds a point of the list `W` (used for both players' claims). -/
def colMeets (base : Pt d) (s : ℕ) (W : List (Pt d)) (c : ℕ) : Prop := ∃ r < s, spt base c r ∈ W

/-- Column `c` lies in `B`. -/
def colFull (base : Pt d) (s : ℕ) (B : List (Pt d)) (c : ℕ) : Prop := ∀ r < s, spt base c r ∈ B

/-- Column `c` is attacked: it holds a Black point and no White point. -/
def active (base : Pt d) (s N : ℕ) (B W : List (Pt d)) (c : ℕ) : Prop :=
  c < N ∧ colMeets base s B c ∧ ¬ colMeets base s W c

/-- Black continues an attacked column at its topmost unused point. -/
def ActMove (base : Pt d) (s N : ℕ) (B W : List (Pt d)) (x : Pt d) : Prop :=
  ∃ c r, active base s N B W c ∧ r < s ∧ x = spt base c r ∧ x ∉ B ∧ ∀ r' < r, spt base c r' ∈ B

/-- After all columns are protected: an unused point of the strip of least row (greatest weight). -/
def Ph2Move (base : Pt d) (s N : ℕ) (B W : List (Pt d)) (x : Pt d) : Prop :=
  ∃ c < N, ∃ r < s, x = spt base c r ∧ x ∉ B ∧ x ∉ W ∧
    ∀ c' < N, ∀ r' < s, spt base c' r' ∉ B → spt base c' r' ∉ W → r ≤ r'

/-- Black's positional rule: stop at a Black column; otherwise continue the attacked column, or
attack the top point of an unprotected column, or take an unused point of greatest weight; stop
when the strip is used up. -/
noncomputable def next (base : Pt d) (s N : ℕ) (B W : List (Pt d)) : Option (Pt d) :=
  if ∃ c < N, colFull base s B c then none
  else if h : ∃ x, ActMove base s N B W x then some (Classical.choose h)
  else if h : ∃ c < N, ¬ colMeets base s W c then some (spt base (Classical.choose h) 0)
  else if h : ∃ x, Ph2Move base s N B W x then some (Classical.choose h)
  else none

/-- Recompute `n` candidate claims from White's replies `ws`. After `next` first returns
`none`, the recursion continues with `getD 0` padding. It agrees with actual stopped-play
claims only before stopping; it does not itself stop. -/
noncomputable def claimsUpTo (base : Pt d) (s N : ℕ) (ws : List (Pt d)) : ℕ → List (Pt d)
  | 0 => []
  | n + 1 => claimsUpTo base s N ws n ++
      [(next base s N (claimsUpTo base s N ws n) (ws.take n)).getD 0]

/-- Black's causal strategy: recompute the own claims from White's replies, then apply `next`. -/
noncomputable def strat (base : Pt d) (s N : ℕ) (ws : List (Pt d)) : Option (Pt d) :=
  next base s N (claimsUpTo base s N ws ws.length) ws

variable {base : Pt d} {s N : ℕ}

theorem claimsUpTo_append (ws : List (Pt d)) (y : Pt d) :
    ∀ n ≤ ws.length, claimsUpTo base s N (ws ++ [y]) n = claimsUpTo base s N ws n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    simp only [claimsUpTo]
    rw [ih (by omega), List.take_append_of_le_length (by omega)]

theorem claims_append (ws : List (Pt d)) (y : Pt d) :
    claimsUpTo base s N (ws ++ [y]) (ws ++ [y]).length =
      claimsUpTo base s N ws ws.length ++
        [(next base s N (claimsUpTo base s N ws ws.length) ws).getD 0] := by
  rw [List.length_append, List.length_singleton]
  simp only [claimsUpTo]
  rw [claimsUpTo_append ws y _ le_rfl, List.take_left' rfl]

theorem act_exists {B W : List (Pt d)} {c : ℕ} (hc : active base s N B W c)
    (hnf : ¬ colFull base s B c) : ∃ x, ActMove base s N B W x := by
  have hex : ∃ r, r < s ∧ spt base c r ∉ B := by
    by_contra h
    push_neg at h
    exact hnf h
  refine ⟨spt base c (Nat.find hex), c, Nat.find hex, hc, (Nat.find_spec hex).1, rfl,
    (Nat.find_spec hex).2, fun r' hr' => ?_⟩
  have := Nat.find_min hex hr'
  push_neg at this
  exact this (by have := (Nat.find_spec hex).1; omega)

theorem ph2_exists {B W : List (Pt d)} (h : ∃ c < N, ∃ r < s, spt base c r ∉ B ∧ spt base c r ∉ W) :
    ∃ x, Ph2Move base s N B W x := by
  have hex : ∃ r, r < s ∧ ∃ c < N, spt base c r ∉ B ∧ spt base c r ∉ W := by
    obtain ⟨c, hc, r, hr, h1, h2⟩ := h
    exact ⟨r, hr, c, hc, h1, h2⟩
  obtain ⟨hrs, c, hc, h1, h2⟩ := Nat.find_spec hex
  refine ⟨spt base c (Nat.find hex), c, hc, Nat.find hex, hrs, rfl, h1, h2, ?_⟩
  intro c' hc' r' hr' h1' h2'
  by_contra hlt
  push_neg at hlt
  exact Nat.find_min hex hlt ⟨hr', c', hc', h1', h2'⟩

/-- Every claim of the rule is a legal point: an unused point of the strip. -/
theorem next_legal (hs : 2 ≤ s) {B W : List (Pt d)} {x : Pt d} (h : next base s N B W = some x) :
    (∃ c < N, ∃ r < s, spt base c r = x) ∧ x ∉ B ∧ x ∉ W := by
  unfold next at h
  split_ifs at h with hf hA hF hP
  · obtain ⟨c, r, ⟨hcN, -, hcW⟩, hr, hx, hxB, -⟩ := Classical.choose_spec hA
    cases h
    refine ⟨⟨c, hcN, r, hr, hx.symm⟩, hxB, fun hxW => hcW ⟨r, hr, hx ▸ hxW⟩⟩
  · have hc := Classical.choose_spec hF
    cases h
    set c := Classical.choose hF
    refine ⟨⟨c, hc.1, 0, by omega, rfl⟩, fun hB => ?_, fun hW => hc.2 ⟨0, by omega, hW⟩⟩
    exact hA (act_exists ⟨hc.1, ⟨0, by omega, hB⟩, hc.2⟩ fun hfull => hf ⟨c, hc.1, hfull⟩)
  · obtain ⟨c, hc, r, hr, hx, hxB, hxW, -⟩ := Classical.choose_spec hP
    cases h
    exact ⟨⟨c, hc, r, hr, hx.symm⟩, hxB, hxW⟩


theorem next_none {B W : List (Pt d)} (h : next base s N B W = none) :
    (∃ c < N, colFull base s B c) ∨
      ((∀ c < N, colMeets base s W c) ∧ ∀ c < N, ∀ r < s, spt base c r ∈ B ∨ spt base c r ∈ W) := by
  by_cases hf : ∃ c < N, colFull base s B c
  · exact Or.inl hf
  right
  unfold next at h
  rw [if_neg hf] at h
  split_ifs at h with hA hF hP
  push_neg at hF
  refine ⟨hF, fun c hc r hr => ?_⟩
  by_contra hn
  push_neg at hn
  exact hP (ph2_exists ⟨c, hc, r, hr, hn.1, hn.2⟩)

/-- The weighted Black-minus-White count. -/
noncomputable def Phi (base : Pt d) (s N : ℕ) (B W : List (Pt d)) : ℤ :=
  (B.map (wt base s N)).sum - (W.map (wt base s N)).sum

/-- The number of protected columns (holding a White point). -/
noncomputable def Prot (base : Pt d) (s N : ℕ) (W : List (Pt d)) : ℕ :=
  ((Finset.range N).filter (fun c => colMeets base s W c)).card

/-- The potential invariant of the strip game: with `R` completed runs, the weighted count is at
least `R` (minus `2^{j-1} - 1` during a run that has `j` Black points so far), and the protected
columns number at most `(s-1) R` (plus `j`). -/
def Pot (base : Pt d) (s N : ℕ) (B W : List (Pt d)) : Prop :=
  ((∀ c, ¬ active base s N B W c) ∧
    ∃ R : ℕ, (R : ℤ) ≤ Phi base s N B W ∧ Prot base s N W ≤ (s - 1) * R) ∨
  (∃ c j, active base s N B W c ∧ 1 ≤ j ∧ j < s ∧ (∀ r < s, spt base c r ∈ B ↔ r < j) ∧
     (∀ c', active base s N B W c' → c' = c) ∧
     ∃ R : ℕ, (R : ℤ) + 1 - 2 ^ (j - 1) ≤ Phi base s N B W ∧ Prot base s N W ≤ (s - 1) * R + j)

theorem phi_step (B W : List (Pt d)) (x y : Pt d) :
    Phi base s N (B ++ [x]) (W ++ [y]) = Phi base s N B W + wt base s N x - wt base s N y := by
  simp only [Phi, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  ring

theorem colMeets_append (W : List (Pt d)) (y : Pt d) (c : ℕ) :
    colMeets base s (W ++ [y]) c ↔ colMeets base s W c ∨ ∃ r < s, spt base c r = y := by
  unfold colMeets
  simp only [List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨r, hr, h | h⟩
    exacts [Or.inl ⟨r, hr, h⟩, Or.inr ⟨r, hr, h⟩]
  · rintro (⟨r, hr, h⟩ | ⟨r, hr, h⟩)
    exacts [⟨r, hr, Or.inl h⟩, ⟨r, hr, Or.inr h⟩]

theorem prot_le (W : List (Pt d)) : Prot base s N W ≤ N := by
  unfold Prot
  exact (Finset.card_filter_le _ _).trans (Finset.card_range N).le

theorem prot_full {W : List (Pt d)} (h : ∀ c < N, colMeets base s W c) : Prot base s N W = N := by
  unfold Prot
  rw [Finset.filter_true_of_mem (fun c hc => h c (Finset.mem_range.1 hc)), Finset.card_range]

theorem prot_step (hd : 2 ≤ d) (W : List (Pt d)) (y : Pt d) :
    Prot base s N (W ++ [y]) ≤ Prot base s N W + 1 := by
  unfold Prot
  by_cases hy : ∃ c' : ℕ, ∃ r' < s, spt base c' r' = y
  · obtain ⟨c', r', -, rfl⟩ := hy
    refine (Finset.card_le_card (t := insert c' ((Finset.range N).filter
      (fun c => colMeets base s W c))) ?_).trans (Finset.card_insert_le _ _)
    intro c hc
    rw [Finset.mem_filter, colMeets_append] at hc
    rw [Finset.mem_insert, Finset.mem_filter]
    rcases hc.2 with h | ⟨r, -, h⟩
    · exact Or.inr ⟨hc.1, h⟩
    · exact Or.inl (spt_inj hd h).1
  · refine (Finset.card_le_card ?_).trans (Nat.le_succ _)
    intro c hc
    rw [Finset.mem_filter, colMeets_append] at hc
    rw [Finset.mem_filter]
    rcases hc.2 with h | h
    · exact ⟨hc.1, h⟩
    · exact absurd ⟨c, h⟩ hy

/-- One round of the strip game keeps the potential invariant, unless a Black column appears. -/
theorem pot_step (hd : 2 ≤ d) (hs : 2 ≤ s) {B W : List (Pt d)} {x y : Pt d}
    (hpot : Pot base s N B W) (hnf : ¬ ∃ c < N, colFull base s B c)
    (hnext : next base s N B W = some x) (hyB : y ∉ B) (hyx : y ≠ x) (hyW : y ∉ W) :
    Pot base s N (B ++ [x]) (W ++ [y]) ∨ ∃ c < N, colFull base s (B ++ [x]) c := by
  have hmemB : ∀ z, z ∈ B ++ [x] ↔ z ∈ B ∨ z = x := fun z => by simp
  have hcolW := colMeets_append (base := base) (s := s) W y
  have hcolB := colMeets_append (base := base) (s := s) B x
  have hphi := phi_step (base := base) (s := s) (N := N) B W x y
  have hprot := prot_step (base := base) (s := s) (N := N) hd W y
  unfold next at hnext
  rw [if_neg hnf] at hnext
  split_ifs at hnext with hA hF hP
  · -- continue the attacked column
    obtain ⟨c, r, hact, hr, hx, hxB, hmin⟩ := Classical.choose_spec hA
    have hxx : Classical.choose hA = x := Option.some_injective _ hnext
    rw [hxx] at hx hxB
    rcases hpot with ⟨hnoact, -⟩ | ⟨c₀, j, hact0, hj1, hjs, hrows, huniq, R, hΦ, hP⟩
    · exact absurd hact (hnoact c)
    have hcc : c = c₀ := huniq c hact
    subst hcc
    have hrj : r = j := by
      rcases lt_trichotomy r j with h | h | h
      · exact absurd ((hrows r hr).2 h) (hx ▸ hxB)
      · exact h
      · exact absurd ((hrows j hjs).1 (hmin j h)) (lt_irrefl j)
    subst hrj
    by_cases hfull : r + 1 = s
    · right
      refine ⟨c, hact.1, fun r' hr' => (hmemB _).2 ?_⟩
      rcases Nat.lt_or_ge r' r with h | h
      · exact Or.inl ((hrows r' hr').2 h)
      · right; rw [hx, show r' = r by omega]
    · left
      by_cases hy : ∃ r' < s, spt base c r' = y
      · obtain ⟨r', hr', hyr⟩ := hy
        have hr'r : r + 1 ≤ r' := by
          rcases lt_trichotomy r' r with h | h | h
          · exact absurd (hyr ▸ (hrows r' hr').2 h) hyB
          · exact absurd (by rw [← hyr, hx, h]) hyx
          · omega
        refine Or.inl ⟨fun c' hc' => ?_, R + 1, ?_, ?_⟩
        · obtain ⟨hc'N, hc'B, hc'W⟩ := hc'
          by_cases hcc : c' = c
          · rw [hcc] at hc'W; exact hc'W ((hcolW c).2 (Or.inr ⟨r', hr', hyr⟩))
          · have hB' : colMeets base s B c' := by
              rcases (hcolB c').1 hc'B with h | ⟨r'', hr'', h⟩
              · exact h
              · exact absurd (spt_inj hd (h.trans hx)).1 hcc
            exact hcc (huniq c' ⟨hc'N, hB', fun h => hc'W ((hcolW c').2 (Or.inl h))⟩)
        · rw [hphi, hx, wt_spt hd hact.1 hr, ← hyr, wt_spt hd hact.1 hr']
          have h1 := wgt_anti s hr'r
          have h2 := wgt_step (s := s) hj1
          push_cast; linarith
        · have : (s - 1) * (R + 1) = (s - 1) * R + (s - 1) := by ring
          omega
      · refine Or.inr ⟨c, r + 1, ⟨hact.1, (hcolB c).2 (Or.inr ⟨r, hr, hx.symm⟩), fun h => ?_⟩,
          by omega, by omega, ?_, ?_, R, ?_, ?_⟩
        · rcases (hcolW c).1 h with h | h
          · exact hact.2.2 h
          · exact hy h
        · intro r' hr'
          rw [hmemB]
          constructor
          · rintro (h | h)
            · have := (hrows r' hr').1 h; omega
            · have := (spt_inj hd (h.trans hx)).2; omega
          · intro h
            rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
            · exact Or.inl ((hrows r' hr').2 h)
            · right; rw [hx, h]
        · intro c' hc'
          by_contra hcc
          obtain ⟨hc'N, hc'B, hc'W⟩ := hc'
          have hB' : colMeets base s B c' := by
            rcases (hcolB c').1 hc'B with h | ⟨r'', hr'', h⟩
            · exact h
            · exact absurd (spt_inj hd (h.trans hx)).1 hcc
          exact hcc (huniq c' ⟨hc'N, hB', fun h => hc'W ((hcolW c').2 (Or.inl h))⟩)
        · rw [hphi, hx, wt_spt hd hact.1 hr]
          have h1 := wt_le_wgt_zero hd (base := base) (s := s) (N := N) y
          have h2 := wgt_zero_sub (s := s) hj1
          have h3 : (2 : ℤ) ^ (r + 1 - 1) = 2 * 2 ^ (r - 1) := by
            rw [show r + 1 - 1 = (r - 1) + 1 by omega, pow_succ]; ring
          rw [h3]; linarith
        · omega
  · -- attack a fresh column
    have hc := Classical.choose_spec hF
    set c := Classical.choose hF with hcdef
    have hxx : spt base c 0 = x := Option.some_injective _ hnext
    have hnoact : ∀ c', ¬ active base s N B W c' := fun c' hc' =>
      hA (act_exists hc' fun hfull => hnf ⟨c', hc'.1, hfull⟩)
    rcases hpot with ⟨-, R, hΦ, hP⟩ | ⟨c₀, -, hact0, -⟩
    swap
    · exact absurd hact0 (hnoact c₀)
    have hcB : ¬ colMeets base s B c := fun h => hnoact c ⟨hc.1, h, hc.2⟩
    left
    by_cases hy : ∃ r' < s, spt base c r' = y
    · obtain ⟨r', hr', hyr⟩ := hy
      have hr'1 : 1 ≤ r' := by
        by_contra h0
        have : r' = 0 := by omega
        rw [this] at hyr
        exact hyx (hyr.symm.trans hxx)
      refine Or.inl ⟨fun c' hc' => ?_, R + 1, ?_, ?_⟩
      · obtain ⟨hc'N, hc'B, hc'W⟩ := hc'
        by_cases hcc : c' = c
        · rw [hcc] at hc'W; exact hc'W ((hcolW c).2 (Or.inr ⟨r', hr', hyr⟩))
        · have hB' : colMeets base s B c' := by
            rcases (hcolB c').1 hc'B with h | ⟨r'', hr'', h⟩
            · exact h
            · exact absurd (spt_inj hd (h.trans hxx.symm)).1 hcc
          exact hnoact c' ⟨hc'N, hB', fun h => hc'W ((hcolW c').2 (Or.inl h))⟩
      · rw [hphi, ← hxx, wt_spt hd hc.1 (by omega), ← hyr, wt_spt hd hc.1 hr']
        have h1 := wgt_anti s hr'1
        have h2 := wgt_zero_sub (s := s) (j := 1) le_rfl
        push_cast; norm_num at h2; linarith
      · have : (s - 1) * (R + 1) = (s - 1) * R + (s - 1) := by ring
        omega
    · refine Or.inr ⟨c, 1, ⟨hc.1, (hcolB c).2 (Or.inr ⟨0, by omega, hxx⟩), fun h => ?_⟩,
        le_rfl, by omega, ?_, ?_, R, ?_, ?_⟩
      · rcases (hcolW c).1 h with h | h
        · exact hc.2 h
        · exact hy h
      · intro r' hr'
        rw [hmemB]
        constructor
        · rintro (h | h)
          · exact absurd ⟨r', hr', h⟩ hcB
          · have := (spt_inj hd (h.trans hxx.symm)).2; omega
        · intro h
          right; rw [← hxx, show r' = 0 by omega]
      · intro c' hc'
        by_contra hcc
        obtain ⟨hc'N, hc'B, hc'W⟩ := hc'
        have hB' : colMeets base s B c' := by
          rcases (hcolB c').1 hc'B with h | ⟨r'', hr'', h⟩
          · exact h
          · exact absurd (spt_inj hd (h.trans hxx.symm)).1 hcc
        exact hnoact c' ⟨hc'N, hB', fun h => hc'W ((hcolW c').2 (Or.inl h))⟩
      · rw [hphi, ← hxx, wt_spt hd hc.1 (by omega)]
        have h1 := wt_le_wgt_zero hd (base := base) (s := s) (N := N) y
        simp only [pow_zero, Nat.sub_self]
        linarith
      · omega
  · -- all columns protected: an unused point of greatest weight
    push_neg at hF
    obtain ⟨c, hc, r, hr, hx, hxB, hxW, hmin⟩ := Classical.choose_spec hP
    have hxx : Classical.choose hP = x := Option.some_injective _ hnext
    rw [hxx] at hx hxB hxW
    have hnoact : ∀ c', ¬ active base s N B W c' := fun c' hc' => hc'.2.2 (hF c' hc'.1)
    rcases hpot with ⟨-, R, hΦ, hP'⟩ | ⟨c₀, -, hact0, -⟩
    swap
    · exact absurd hact0 (hnoact c₀)
    left; left
    refine ⟨fun c' hc' => hc'.2.2 ((hcolW c').2 (Or.inl (hF c' hc'.1))), R, ?_, ?_⟩
    · rw [hphi, hx, wt_spt hd hc hr]
      have : wt base s N y ≤ wgt s r := by
        by_cases hy : ∃ c' < N, ∃ r' < s, spt base c' r' = y
        · obtain ⟨c', hc', r', hr', rfl⟩ := hy
          rw [wt_spt hd hc' hr']
          exact wgt_anti s (hmin c' hc' r' hr' hyB hyW)
        · rw [wt_out hy]; exact wgt_nonneg hr
      linarith
    · have h1 : Prot base s N (W ++ [y]) ≤ N := prot_le _
      have h2 : Prot base s N W = N := prot_full hF
      omega

theorem stripRun_succ (β : List (Pt d) → Option (Pt d)) (ω : List (Pt d) → Pt d) (k : ℕ) :
    stripRun β ω (k + 1) = (match β (stripRun β ω k).2 with
      | none => stripRun β ω k
      | some x => ((stripRun β ω k).1 ++ [x], (stripRun β ω k).2 ++ [ω ((stripRun β ω k).1 ++ [x])])) := rfl

theorem stripRun_stab {β : List (Pt d) → Option (Pt d)} {ω : List (Pt d) → Pt d} {T : ℕ}
    (h : β (stripRun β ω T).2 = none) : ∀ k, stripRun β ω (T + k) = stripRun β ω T
  | 0 => rfl
  | k + 1 => by
    rw [← Nat.add_assoc, stripRun_succ, stripRun_stab h k, h]

theorem stripRun_snd (β : List (Pt d) → Option (Pt d)) (ω : List (Pt d) → Pt d) :
    ∀ k, (stripRun β ω k).2 =
      (List.range (stripRun β ω k).1.length).map (fun i => ω ((stripRun β ω k).1.take (i + 1)))
  | 0 => rfl
  | k + 1 => by
    have ih := stripRun_snd β ω k
    rw [stripRun_succ]
    rcases hb : β (stripRun β ω k).2 with _ | x
    · exact ih
    · simp only
      rw [ih]
      generalize (stripRun β ω k).1 = c
      rw [List.length_append, List.length_singleton, List.range_succ, List.map_append]
      congr 1
      · apply List.map_congr_left
        intro i hi
        rw [List.mem_range] at hi
        rw [List.take_append_of_le_length (by omega)]
      · simp [List.take_of_length_le]


/-- `W_s = ∑_r w_r`. -/
noncomputable def Wsum (s : ℕ) : ℤ := ∑ r ∈ Finset.range s, wgt s r

theorem Wsum_pos (hs : 2 ≤ s) : 0 < Wsum s := by
  unfold Wsum
  have h := Finset.single_le_sum (f := wgt s) (fun r hr => wgt_nonneg (Finset.mem_range.1 hr))
    (Finset.mem_range.2 (show 0 < s by omega))
  exact lt_of_lt_of_le (wgt_zero_pos s) h

theorem next_full {B W : List (Pt d)} (h : ∃ c < N, colFull base s B c) :
    next base s N B W = none := by
  unfold next; rw [if_pos h]

/-- At the end of the strip game, with every column protected and the strip used up, some row
has White count at most `(1/2 - γ_s) N`, `γ_s = 1 / (2 (s-1) W_s)`. -/
theorem final_row (hd : 2 ≤ d) (hs : 2 ≤ s) {B W : List (Pt d)} (hBn : B.Nodup) (hWn : W.Nodup)
    (hdisj : ∀ x ∈ B, x ∉ W) (hpot : Pot base s N B W) (hprot : ∀ c < N, colMeets base s W c)
    (hused : ∀ c < N, ∀ r < s, spt base c r ∈ B ∨ spt base c r ∈ W) :
    ∃ r < s, ((rowSet base N r ∩ {x | x ∈ W}).ncard : ℝ) ≤
      (1 / 2 - 1 / (2 * ((s : ℝ) - 1) * (Wsum s : ℝ))) * N := by
  have hnoact : ∀ c, ¬ active base s N B W c := fun c hc => hc.2.2 (hprot c hc.1)
  obtain ⟨R, hΦ, hP⟩ : ∃ R : ℕ, (R : ℤ) ≤ Phi base s N B W ∧ Prot base s N W ≤ (s - 1) * R := by
    rcases hpot with ⟨-, h⟩ | ⟨c, -, hc, -⟩
    · exact h
    · exact absurd hc (hnoact c)
  rw [prot_full hprot] at hP
  have hs1 : ((s - 1 : ℕ) : ℤ) = (s : ℤ) - 1 := by push_cast [Nat.cast_sub (show 1 ≤ s by omega)]; ring
  have hNphi : (N : ℤ) ≤ ((s : ℤ) - 1) * Phi base s N B W := by
    have h1 : (N : ℤ) ≤ ((s : ℤ) - 1) * R := by
      rw [← hs1]; exact_mod_cast hP
    have h2 : (0 : ℤ) ≤ (s : ℤ) - 1 := by
      have : (2 : ℤ) ≤ s := by exact_mod_cast hs
      linarith
    nlinarith
  set b : ℕ → ℤ := fun r => ((rowSet base N r ∩ {x | x ∈ B}).ncard : ℤ) with hb
  set w : ℕ → ℤ := fun r => ((rowSet base N r ∩ {x | x ∈ W}).ncard : ℤ) with hw
  have hphi : Phi base s N B W = ∑ r ∈ Finset.range s, wgt s r * (b r - w r) := by
    unfold Phi
    rw [sum_wt base s N hBn, sum_wt base s N hWn, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [hb, hw]; ring
  have hbw : ∀ r < s, b r + w r = N := by
    intro r hr
    have hU : (rowSet base N r ∩ {x | x ∈ B}) ∪ (rowSet base N r ∩ {x | x ∈ W}) =
        rowSet base N r := by
      ext z
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
      · intro hz
        obtain ⟨c, hc, rfl⟩ := hz
        rcases hused c hc r hr with h | h
        · exact Or.inl ⟨⟨c, hc, rfl⟩, h⟩
        · exact Or.inr ⟨⟨c, hc, rfl⟩, h⟩
    have hD : Disjoint (rowSet base N r ∩ {x | x ∈ B}) (rowSet base N r ∩ {x | x ∈ W}) :=
      Set.disjoint_left.2 fun z h1 h2 => hdisj z h1.2 h2.2
    have hfin : (rowSet base N r).Finite := (Set.finite_Iio N).image _
    have := Set.ncard_union_eq hD (hfin.subset Set.inter_subset_left)
      (hfin.subset Set.inter_subset_left)
    rw [hU, show (rowSet base N r).ncard = N from
      ncard_image_Iio (fun c c' h => (spt_inj hd h).1) N] at this
    simp only [hb, hw]
    exact_mod_cast this.symm
  have hWs := Wsum_pos hs
  obtain ⟨r, hr, hrow⟩ : ∃ r ∈ Finset.range s, (N : ℤ) ≤ ((s : ℤ) - 1) * Wsum s * (b r - w r) := by
    by_contra hcon
    push_neg at hcon
    have hlt : ∑ r ∈ Finset.range s, wgt s r * (((s : ℤ) - 1) * Wsum s * (b r - w r)) <
        ∑ r ∈ Finset.range s, wgt s r * N :=
      Finset.sum_lt_sum
        (fun r hr => mul_le_mul_of_nonneg_left (hcon r hr).le
          (wgt_nonneg (Finset.mem_range.1 hr)))
        ⟨0, Finset.mem_range.2 (by omega),
          mul_lt_mul_of_pos_left (hcon 0 (Finset.mem_range.2 (by omega))) (wgt_zero_pos s)⟩
    have e1 : ∑ r ∈ Finset.range s, wgt s r * (((s : ℤ) - 1) * Wsum s * (b r - w r)) =
        ((s : ℤ) - 1) * Wsum s * Phi base s N B W := by
      rw [hphi, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
    have e2 : ∑ r ∈ Finset.range s, wgt s r * (N : ℤ) = Wsum s * N := by
      rw [← Finset.sum_mul]; rfl
    rw [e1, e2] at hlt
    nlinarith
  rw [Finset.mem_range] at hr
  refine ⟨r, hr, ?_⟩
  have hbr : b r = N - w r := by have := hbw r hr; omega
  rw [hbr] at hrow
  have hK : (0 : ℝ) < ((s : ℝ) - 1) * (Wsum s : ℝ) := by
    have h1 : (0 : ℝ) < (s : ℝ) - 1 := by
      have : (2 : ℝ) ≤ s := by exact_mod_cast hs
      linarith
    have h2 : (0 : ℝ) < (Wsum s : ℝ) := by exact_mod_cast hWs
    exact mul_pos h1 h2
  have hrowR : (N : ℝ) ≤ ((s : ℝ) - 1) * (Wsum s : ℝ) * (N - 2 * (w r : ℝ)) := by
    have : ((N : ℤ) : ℝ) ≤ ((((s : ℤ) - 1) * Wsum s * (N - w r - w r) : ℤ) : ℝ) := by
      exact_mod_cast hrow
    push_cast at this
    linarith
  have hwr : ((rowSet base N r ∩ {x | x ∈ W}).ncard : ℝ) = (w r : ℝ) := by simp [hw]
  rw [hwr]
  set K := ((s : ℝ) - 1) * (Wsum s : ℝ) with hKdef
  have hγ : (1 / 2 - 1 / (2 * ((s : ℝ) - 1) * (Wsum s : ℝ))) * (N : ℝ) = (K * N - N) / (2 * K) := by
    have h1 : (s : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ s := by exact_mod_cast hs
      exact ne_of_gt (by linarith)
    have h2 : (Wsum s : ℝ) ≠ 0 := by exact_mod_cast hWs.ne'
    rw [hKdef]; field_simp
  rw [hγ, le_div_iff₀ (by positivity)]
  nlinarith

end StripProof

variable {d : ℕ}

/-- A column outcome. -/
def colAt (base : Pt d) (s N : ℕ) (C : List (Pt d)) : Prop :=
  ∃ c, (stripCol base s N c).ncard = s ∧ stripCol base s N c ⊆ {x | x ∈ C}

/-- A sparse-row outcome. -/
def rowAt (base : Pt d) (s N : ℕ) (γ : ℝ) (C Wr : List (Pt d)) : Prop :=
  ∃ c, (stripRow base s N c).ncard = N ∧ stripRow base s N c ⊆ {x | x ∈ C ∨ x ∈ Wr} ∧
     ((stripRow base s N c ∩ {x | x ∈ Wr}).ncard : ℝ) ≤ (1 / 2 - γ) * N

/-- The property of Black's strategy in `end_strip`. -/
def StripSpec (base : Pt d) (s N : ℕ) (γ : ℝ) (β : List (Pt d) → Option (Pt d)) : Prop :=
  ∀ (U₀ : Set (Pt d)), Disjoint U₀ (strip base s N) → ∀ ω : List (Pt d) → Pt d, FreshResponder U₀ ω →
    ∃ T ≤ s * N, β (stripRun β ω T).2 = none ∧
      (∀ k < T, ∀ x, β (stripRun β ω k).2 = some x →
          x ∈ strip base s N ∧ x ∉ (stripRun β ω k).1 ∧ x ∉ (stripRun β ω k).2) ∧
      (colAt base s N (stripRun β ω T).1 ∨ rowAt base s N γ (stripRun β ω T).1 (stripRun β ω T).2)

theorem stripRun_inv {β : List (Pt d) → Option (Pt d)} {ω : List (Pt d) → Pt d} {A : Set (Pt d)}
    {T : ℕ}
    (hleg : ∀ k < T, ∀ x, β (stripRun β ω k).2 = some x →
      x ∈ A ∧ x ∉ (stripRun β ω k).1 ∧ x ∉ (stripRun β ω k).2)
    (hω : ∀ bs : List (Pt d), bs ≠ [] → ω bs ∉ bs) :
    ∀ k ≤ T, ∀ x ∈ (stripRun β ω k).1, x ∈ A ∧ x ∉ (stripRun β ω k).2
  | 0, _ => by simp [stripRun]
  | k + 1, hk => by
    have ih := stripRun_inv hleg hω k (by omega)
    rw [stripRun_succ]
    rcases hb : β (stripRun β ω k).2 with _ | y
    · exact ih
    · obtain ⟨hyA, -, hy2⟩ := hleg k (by omega) y hb
      have hfr := hω ((stripRun β ω k).1 ++ [y]) (by simp)
      intro x hx
      simp only [List.mem_append, List.mem_singleton, not_or] at hx ⊢
      rcases hx with hx | hx
      · obtain ⟨h1, h2⟩ := ih x hx
        refine ⟨h1, h2, fun h => hfr ?_⟩
        rw [← h]; simp [hx]
      · subst hx
        refine ⟨hyA, hy2, fun h => hfr ?_⟩
        rw [← h]; simp

theorem ofFn_getD (L : List (Pt d)) (k : ℕ) (hk : k ≤ L.length) :
    List.ofFn (fun i : Fin k => L.getD i 0) = L.take k := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_ofFn, List.getElem_take]
    simp at h1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl

theorem om_fresh {G : Generator (Pt d)} (hG : G.Fresh) (P : List (Pt d)) :
    ∀ bs : List (Pt d), bs ≠ [] → G (P ++ bs) ∉ usedBy G P ∧ G (P ++ bs) ∉ bs ∧
      ∀ i, 1 ≤ i → i < bs.length → G (P ++ bs.take i) ≠ G (P ++ bs) := by
  intro bs hbs
  have hlen : 0 < bs.length := List.length_pos_iff.2 hbs
  have hLlen : (P ++ bs).length = P.length + bs.length := List.length_append
  have ht : (P ++ bs).length - 1 < (P ++ bs).length := by omega
  have htake : (P ++ bs).take ((P ++ bs).length - 1 + 1) = P ++ bs :=
    List.take_of_length_le (by omega)
  obtain ⟨f1, f2⟩ := SeparationAux.fresh_list hG (P ++ bs) ht
  rw [htake] at f1 f2
  refine ⟨?_, ?_, ?_⟩
  · rintro (hx | ⟨i, hi, hx⟩)
    · exact f1 (List.mem_append_left _ hx)
    · refine f2 i (by omega) ?_
      rw [List.take_append_of_le_length (by omega)]
      exact hx
  · intro hx
    exact f1 (List.mem_append_right _ hx)
  · intro i hi1 hi2
    have := f2 (P.length + i - 1) (by omega)
    rwa [show P.length + i - 1 + 1 = P.length + i by omega, List.take_length_add_append] at this

theorem exists_base (hd : 1 ≤ d) (U : Set (Pt d)) (hU : U.Finite) (s N : ℕ) :
    ∃ base : Pt d, Disjoint U (strip base s N) := by
  let i0 : Fin d := ⟨0, by omega⟩
  obtain ⟨M, hM⟩ := (hU.image (fun x : Pt d => x i0)).bddAbove
  refine ⟨fun _ => M + 1, Set.disjoint_left.2 fun x hxU hxS => ?_⟩
  have h1 := ((hxS i0).1 rfl).1
  have h2 : x i0 ≤ M := hM ⟨x, hxU, rfl⟩
  simp only at h1
  omega

theorem col_rect {base : Pt d} {s N : ℕ} {c : ℤ} (hs : 1 ≤ s)
    (hne : (stripCol base s N c).Nonempty) : ∃ R : Rect d, R.pts = stripCol base s N c := by
  obtain ⟨x0, hx0S, hx0c⟩ := hne
  let lo : Pt d := fun i => if i.val = 0 then c else base i
  let hi : Pt d := fun i => if i.val = 0 then c else if i.val = 1 then base i + s - 1 else base i
  have hle : lo ≤ hi := by
    intro i; simp only [lo, hi]; split_ifs <;> omega
  refine ⟨Rect.mk lo hi hle, ?_⟩
  have key : ∀ (x : Pt d) (i : Fin d), (lo i ≤ x i ∧ x i ≤ hi i) ↔
      (((i.val = 0 → x i ∈ Icc (base i) (base i + N - 1)) ∧
        (i.val = 1 → x i ∈ Icc (base i) (base i + s - 1)) ∧ (2 ≤ i.val → x i = base i)) ∧
        (i.val = 0 → x i = c)) := by
    intro x i
    have a1 := hx0S i
    have a2 := hx0c i
    simp only [lo, hi, Set.mem_Icc] at a1 a2 ⊢
    by_cases h0 : i.val = 0
    · have := a1.1 h0; have := a2 h0
      simp only [if_pos h0]; constructor
      · intro h; refine ⟨⟨fun _ => ⟨by omega, by omega⟩, fun h1 => by omega, fun h2 => by omega⟩,
          fun _ => by omega⟩
      · intro h; have := h.2 h0; omega
    · by_cases h1 : i.val = 1
      · simp only [if_neg h0, if_pos h1]
        constructor
        · intro h; exact ⟨⟨fun h' => absurd h' h0, fun _ => h, fun h2 => by omega⟩, fun h' => absurd h' h0⟩
        · intro h; exact h.1.2.1 h1
      · simp only [if_neg h0, if_neg h1]
        constructor
        · intro h; exact ⟨⟨fun h' => absurd h' h0, fun h' => absurd h' h1, fun _ => by omega⟩,
            fun h' => absurd h' h0⟩
        · intro h; have := h.1.2.2 (by omega); omega
  ext x
  simp only [Rect.pts, Rect.lo, Rect.hi, Set.mem_Icc, stripCol, strip, Set.mem_setOf_eq,
    Pi.le_def]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => ((key x i).1 ⟨h1 i, h2 i⟩).1, fun i => ((key x i).1 ⟨h1 i, h2 i⟩).2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => ((key x i).2 ⟨h1 i, h2 i⟩).1, fun i => ((key x i).2 ⟨h1 i, h2 i⟩).2⟩

theorem row_rect {base : Pt d} {s N : ℕ} {c : ℤ} (hN : 1 ≤ N)
    (hne : (stripRow base s N c).Nonempty) : ∃ R : Rect d, R.pts = stripRow base s N c := by
  obtain ⟨x0, hx0S, hx0c⟩ := hne
  let lo : Pt d := fun i => if i.val = 1 then c else base i
  let hi : Pt d := fun i => if i.val = 0 then base i + N - 1 else if i.val = 1 then c else base i
  have hle : lo ≤ hi := by
    intro i; simp only [lo, hi]; split_ifs <;> omega
  refine ⟨Rect.mk lo hi hle, ?_⟩
  have key : ∀ (x : Pt d) (i : Fin d), (lo i ≤ x i ∧ x i ≤ hi i) ↔
      (((i.val = 0 → x i ∈ Icc (base i) (base i + N - 1)) ∧
        (i.val = 1 → x i ∈ Icc (base i) (base i + s - 1)) ∧ (2 ≤ i.val → x i = base i)) ∧
        (i.val = 1 → x i = c)) := by
    intro x i
    have a1 := hx0S i
    have a2 := hx0c i
    simp only [lo, hi, Set.mem_Icc] at a1 a2 ⊢
    by_cases h1 : i.val = 1
    · have := a1.2.1 h1; have := a2 h1
      have h0 : i.val ≠ 0 := by omega
      simp only [if_pos h1, if_neg h0]; constructor
      · intro h; refine ⟨⟨fun h' => absurd h' h0, fun _ => ⟨by omega, by omega⟩, fun h2 => by omega⟩,
          fun _ => by omega⟩
      · intro h; have := h.2 h1; omega
    · by_cases h0 : i.val = 0
      · simp only [if_pos h0, if_neg h1]
        constructor
        · intro h; exact ⟨⟨fun _ => h, fun h' => absurd h' h1, fun h2 => by omega⟩, fun h' => absurd h' h1⟩
        · intro h; exact h.1.1 h0
      · simp only [if_neg h0, if_neg h1]
        constructor
        · intro h; exact ⟨⟨fun h' => absurd h' h0, fun h' => absurd h' h1, fun _ => by omega⟩,
            fun h' => absurd h' h1⟩
        · intro h; have := h.1.2.2 (by omega); omega
  ext x
  simp only [Rect.pts, Rect.lo, Rect.hi, Set.mem_Icc, stripRow, strip, Set.mem_setOf_eq,
    Pi.le_def]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => ((key x i).1 ⟨h1 i, h2 i⟩).1, fun i => ((key x i).1 ⟨h1 i, h2 i⟩).2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => ((key x i).2 ⟨h1 i, h2 i⟩).1, fun i => ((key x i).2 ⟨h1 i, h2 i⟩).2⟩

theorem testInf_le {h : ℕ → ℝ} (O : Set (Pt d)) (lam c : ℝ) (R : Rect d)
    (hR : lam * h R.vol ≤ R.vol) (hc : ((O ∩ R.pts).ncard : ℝ) ≤ c * R.vol) :
    testInf h O univ lam ≤ c := by
  have hmass : mass univ R = R.vol := by simp [mass, Rect.vol]
  have hv := BasicAux.rect_vol_pos R
  have hvpos : (0 : ℝ) < R.vol := by exact_mod_cast (show 0 < R.vol by omega)
  have hmem : ((O ∩ univ ∩ R.pts).ncard : ℝ) / mass univ R ∈ BasicAux.tests h O univ lam :=
    ⟨R, by rw [hmass]; exact hR, rfl⟩
  rw [BasicAux.testInf_eq, if_pos ⟨_, hmem⟩]
  refine (csInf_le (BasicAux.tests_bdd h O univ lam) hmem).trans ?_
  rw [hmass, Set.inter_univ, div_le_iff₀ hvpos]
  exact hc

/-- The data of the adversary's staged construction. -/
structure Sched (d : ℕ) where
  G : Generator (Pt d)
  e : ℕ → Pt d
  sh : ℕ → ℕ
  Nw : ℕ → ℕ
  bch : ℕ → List (Pt d) → Pt d
  Bn : ℕ → Pt d → List (Pt d) → Option (Pt d)

namespace Sched
variable (S : Sched d)

/-- One stage: input `e n`, then run the supplied `Bn` at the supplied base `bch`.
These fields of `Sched` are unconstrained data: freshness of the strip and validity of
Black's strip strategy are caller obligations, not guarantees of this definition. -/
def next (n : ℕ) (L : List (Pt d)) : List (Pt d) :=
  (L ++ [S.e n]) ++ (stripRun (S.Bn n (S.bch n (L ++ [S.e n]))) (fun bs => S.G ((L ++ [S.e n]) ++ bs))
    (S.sh n * S.Nw n)).1

/-- The inputs after `n` stages. -/
def stages : ℕ → List (Pt d)
  | 0 => []
  | n + 1 => S.next n (stages n)

def pre (n : ℕ) : List (Pt d) := S.stages n ++ [S.e n]
def base (n : ℕ) : Pt d := S.bch n (S.pre n)
def om (n : ℕ) : List (Pt d) → Pt d := fun bs => S.G (S.pre n ++ bs)
def run (n : ℕ) : List (Pt d) × List (Pt d) :=
  stripRun (S.Bn n (S.base n)) (S.om n) (S.sh n * S.Nw n)

theorem stages_succ (n : ℕ) : S.stages (n + 1) = S.pre n ++ (S.run n).1 := rfl

/-- The full input sequence. -/
def w (t : ℕ) : Pt d := (S.stages (t + 1)).getD t 0

theorem stages_prefix {n m : ℕ} (h : n ≤ m) : S.stages n <+: S.stages m := by
  induction m, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ m _ ih =>
    rw [stages_succ]
    exact ih.trans ((List.prefix_append _ _).trans (List.prefix_append _ _))

theorem le_length (n : ℕ) : n ≤ (S.stages n).length := by
  induction n with
  | zero => simp
  | succ n ih => rw [stages_succ]; simp [pre]; omega

theorem getD_prefix {l₁ l₂ : List (Pt d)} (h : l₁ <+: l₂) {i : ℕ} (hi : i < l₁.length) :
    l₁.getD i 0 = l₂.getD i 0 := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem w_eq {t m : ℕ} (ht : t < (S.stages m).length) : S.w t = (S.stages m).getD t 0 := by
  unfold w
  rcases le_total (t + 1) m with h | h
  · exact getD_prefix (S.stages_prefix h) (by have := S.le_length (t + 1); omega)
  · exact (getD_prefix (S.stages_prefix h) ht).symm

theorem out_eq {t m : ℕ} (ht : t < (S.stages m).length) :
    S.G.out S.w t = S.G ((S.stages m).take (t + 1)) := by
  unfold Generator.out inputsUpTo
  rw [← ofFn_getD _ _ (by omega)]
  congr 2
  funext i
  exact S.w_eq (by have := i.2; omega)

theorem stage_facts (hG : S.G.Fresh) (n : ℕ) (γ : ℝ)
    (hbase : Disjoint (usedBy S.G (S.pre n)) (strip (S.base n) (S.sh n) (S.Nw n)))
    (hβ : StripSpec (S.base n) (S.sh n) (S.Nw n) γ (S.Bn n (S.base n))) :
    (∀ x ∈ (S.run n).1, x ∈ strip (S.base n) (S.sh n) (S.Nw n) ∧ x ∉ (S.run n).2) ∧
    (colAt (S.base n) (S.sh n) (S.Nw n) (S.run n).1 ∨
      rowAt (S.base n) (S.sh n) (S.Nw n) γ (S.run n).1 (S.run n).2) := by
  obtain ⟨T, hT, hnone, hleg, hout⟩ := hβ _ hbase (S.om n) (om_fresh hG (S.pre n))
  have hrun : S.run n = stripRun (S.Bn n (S.base n)) (S.om n) T := by
    unfold run
    rw [show S.sh n * S.Nw n = T + (S.sh n * S.Nw n - T) by omega]
    exact stripRun_stab hnone _
  rw [hrun]
  exact ⟨fun x hx => stripRun_inv hleg (fun bs hbs => ((om_fresh hG (S.pre n)) bs hbs).2.1) T le_rfl x hx,
    hout⟩

theorem out_in_replies (hG : S.G.Fresh) (n : ℕ)
    (hbase : Disjoint (usedBy S.G (S.pre n)) (strip (S.base n) (S.sh n) (S.Nw n)))
    {p : Pt d} (hpS : p ∈ strip (S.base n) (S.sh n) (S.Nw n))
    (hpCW : p ∈ (S.run n).1 ∨ p ∈ (S.run n).2)
    (hpO : p ∈ S.G.outputSet S.w) : p ∈ (S.run n).2 := by
  obtain ⟨t, rfl⟩ := hpO
  have hQ : S.stages (n + 1) = S.pre n ++ (S.run n).1 := rfl
  have hQlen : (S.stages (n + 1)).length = (S.pre n).length + (S.run n).1.length := by
    rw [hQ, List.length_append]
  by_cases h1 : t < (S.pre n).length
  · exfalso
    have hout := S.out_eq (m := n + 1) (t := t) (by omega)
    rw [hQ, List.take_append_of_le_length (by omega)] at hout
    refine Set.disjoint_left.1 hbase ?_ hpS
    exact Or.inr ⟨t, h1, hout.symm⟩
  by_cases h2 : t < (S.stages (n + 1)).length
  · have hout := S.out_eq h2
    have hsnd : (S.run n).2 = (List.range (S.run n).1.length).map
        (fun i => S.om n ((S.run n).1.take (i + 1))) := stripRun_snd _ _ _
    rw [hsnd, List.mem_map]
    refine ⟨t - (S.pre n).length, List.mem_range.2 (by omega), ?_⟩
    rw [hout, hQ]
    have : t + 1 = (S.pre n).length + (t - (S.pre n).length + 1) := by omega
    rw [this, List.take_length_add_append]
    rfl
  · rcases hpCW with hpC | hpW
    · exfalso
      obtain ⟨j, hj, hjx⟩ := List.mem_iff_getElem.1 hpC
      have hw : S.w ((S.pre n).length + j) = S.G.out S.w t := by
        rw [S.w_eq (m := n + 1) (by omega), hQ, ← hjx]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
        simp [List.getElem?_eq_getElem hj]
      exact (hG S.w t).1 _ (by omega) hw
    · exact hpW

end Sched

end EndpointAux

open EndpointAux in
/-- **Lemma 10.2** (`end:strip`), as a causal Black strategy: for every `s ≥ 2` there is
`γ_s > 0` such that for every `N ≥ 1` and every strip, Black has one strategy `β` (depending only
on White's replies) with the following property against **every** fresh White responder `ω` and
every set `U₀` of earlier points disjoint from the strip: within `s·N` rounds Black stops; every
Black claim was legal (a point of the strip not used before, by either player); and at the stop
either some column of the strip (of length `s`) consists of Black points only (no White point),
or some row (of length `N`) is completely occupied and has at most `(1/2 - γ_s) N` White points. White may answer anywhere.
(Theorem 10.1 instantiates `ω` with the generator: `ω bs = G (prefix ++ bs)`.) -/
theorem end_strip {d : ℕ} (hd : 2 ≤ d) (s : ℕ) (hs : 2 ≤ s) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (N : ℕ), 1 ≤ N → ∀ base : Pt d, ∃ β : BlackStrat d,
      ∀ (U₀ : Set (Pt d)), Disjoint U₀ (strip base s N) → ∀ ω : Responder d, FreshResponder U₀ ω →
        ∃ T ≤ s * N, β (stripRun β ω T).2 = none ∧
          (∀ k < T, ∀ x, β (stripRun β ω k).2 = some x →
              x ∈ strip base s N ∧ x ∉ (stripRun β ω k).1 ∧ x ∉ (stripRun β ω k).2) ∧
          ((∃ c, (stripCol base s N c).ncard = s ∧
              stripCol base s N c ⊆ {x | x ∈ (stripRun β ω T).1}) ∨
           (∃ c, (stripRow base s N c).ncard = N ∧
              stripRow base s N c ⊆ {x | x ∈ (stripRun β ω T).1 ∨ x ∈ (stripRun β ω T).2} ∧
              ((stripRow base s N c ∩ {x | x ∈ (stripRun β ω T).2}).ncard : ℝ) ≤ (1 / 2 - γ) * N)) := by
  have hγ : (0 : ℝ) < 1 / (2 * ((s : ℝ) - 1) * (Wsum s : ℝ)) := by
    have h1 : (0 : ℝ) < (s : ℝ) - 1 := by
      have : (2 : ℝ) ≤ s := by exact_mod_cast hs
      linarith
    have h2 : (0 : ℝ) < (Wsum s : ℝ) := by exact_mod_cast Wsum_pos hs
    exact one_div_pos.2 (mul_pos (mul_pos two_pos h1) h2)
  refine ⟨_, hγ, fun N hN base => ⟨strat base s N, fun U₀ _ ω hω => ?_⟩⟩
  set β := strat base s N with hβdef
  have hclaims : ∀ k, (stripRun β ω k).1 =
      claimsUpTo base s N (stripRun β ω k).2 (stripRun β ω k).2.length := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [stripRun_succ]
      rcases hb : β (stripRun β ω k).2 with _ | x
      · exact ih
      · simp only
        rw [claims_append, ← ih]
        have : next base s N (stripRun β ω k).1 (stripRun β ω k).2 = some x := by
          rw [ih]; exact hb
        rw [this]; rfl
  have hβ : ∀ k, β (stripRun β ω k).2 = next base s N (stripRun β ω k).1 (stripRun β ω k).2 := by
    intro k; rw [hclaims k]; rfl
  have hstep : ∀ k x, next base s N (stripRun β ω k).1 (stripRun β ω k).2 = some x →
      stripRun β ω (k + 1) = ((stripRun β ω k).1 ++ [x], (stripRun β ω k).2 ++ [ω ((stripRun β ω k).1 ++ [x])]) := by
    intro k x h
    rw [stripRun_succ, hβ k, h]
  have hstop : ∀ k, next base s N (stripRun β ω k).1 (stripRun β ω k).2 = none →
      stripRun β ω (k + 1) = stripRun β ω k := by
    intro k h
    rw [stripRun_succ, hβ k, h]
  have hfy : ∀ k x, ω ((stripRun β ω k).1 ++ [x]) ∉ (stripRun β ω k).1 ∧
      ω ((stripRun β ω k).1 ++ [x]) ≠ x ∧ ω ((stripRun β ω k).1 ++ [x]) ∉ (stripRun β ω k).2 := by
    intro k x
    obtain ⟨-, h2, h3⟩ := hω ((stripRun β ω k).1 ++ [x]) (by simp)
    refine ⟨fun h => h2 (List.mem_append_left _ h), fun h => h2 (by simp [h]), fun h => ?_⟩
    rw [stripRun_snd] at h
    obtain ⟨i, hi, hiy⟩ := List.mem_map.1 h
    rw [List.mem_range] at hi
    refine h3 (i + 1) (by omega) (by simp; omega) ?_
    rw [List.take_append_of_le_length (by omega)]
    exact hiy
  -- the invariant
  have hinv : ∀ k, ((stripRun β ω k).1.Nodup ∧ (stripRun β ω k).2.Nodup ∧
      (∀ x ∈ (stripRun β ω k).1, x ∉ (stripRun β ω k).2) ∧
      (∀ x ∈ (stripRun β ω k).1, ∃ c < N, ∃ r < s, spt base c r = x)) ∧
      (Pot base s N (stripRun β ω k).1 (stripRun β ω k).2 ∨
        ∃ c < N, colFull base s (stripRun β ω k).1 c) := by
    intro k
    induction k with
    | zero =>
      refine ⟨⟨List.nodup_nil, List.nodup_nil, by simp [stripRun], by simp [stripRun]⟩,
        Or.inl (Or.inl ⟨?_, 0, ?_, ?_⟩)⟩
      · rintro c ⟨-, ⟨r, -, h⟩, -⟩; simp [stripRun] at h
      · simp [Phi, stripRun]
      · simp only [Prot, Nat.mul_zero, Nat.le_zero, Finset.card_eq_zero]
        refine Finset.filter_false_of_mem fun c _ => ?_
        rintro ⟨r, -, h⟩; simp [stripRun] at h
    | succ k ih =>
      rcases hn : next base s N (stripRun β ω k).1 (stripRun β ω k).2 with _ | x
      · rw [hstop k hn]; exact ih
      · rw [hstep k x hn]
        obtain ⟨⟨hBn, hWn, hdj, hBs⟩, hpot⟩ := ih
        obtain ⟨hxs, hxB, hxW⟩ := next_legal hs hn
        obtain ⟨hyB, hyx, hyW⟩ := hfy k x
        refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
        · rw [List.nodup_append]
          refine ⟨hBn, List.nodup_singleton _, fun a ha b hb => ?_⟩
          rw [List.mem_singleton] at hb; subst hb
          rintro rfl; exact hxB ha
        · rw [List.nodup_append]
          refine ⟨hWn, List.nodup_singleton _, fun a ha b hb => ?_⟩
          rw [List.mem_singleton] at hb; subst hb
          rintro rfl; exact hyW ha
        · intro z hz hz'
          rw [List.mem_append, List.mem_singleton] at hz hz'
          rcases hz with hz | rfl <;> rcases hz' with hz' | hz'
          · exact hdj z hz hz'
          · exact hyB (hz' ▸ hz)
          · exact hxW hz'
          · exact hyx hz'.symm
        · intro z hz
          rw [List.mem_append, List.mem_singleton] at hz
          rcases hz with hz | rfl
          · exact hBs z hz
          · exact hxs
        · have hnf : ¬ ∃ c < N, colFull base s (stripRun β ω k).1 c := fun h => by
            rw [next_full h] at hn; exact absurd hn (by simp)
          rcases hpot with hpot | hfull
          · exact pot_step hd hs hpot hnf hn hyB hyx hyW
          · exact absurd hfull hnf
  have hlen : ∀ k, (∀ k' < k, next base s N (stripRun β ω k').1 (stripRun β ω k').2 ≠ none) →
      (stripRun β ω k).1.length = k := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro h
      obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 (h k (by omega))
      rw [hstep k x hx, List.length_append, ih (fun k' hk' => h k' (by omega))]
      rfl
  have hbound : ∀ k, (stripRun β ω k).1.length ≤ s * N := by
    intro k
    obtain ⟨⟨hBn, -, -, hBs⟩, -⟩ := hinv k
    rw [← List.toFinset_card_of_nodup hBn]
    have hsub : (stripRun β ω k).1.toFinset ⊆
        ((Finset.range N) ×ˢ (Finset.range s)).image (fun p => spt base p.1 p.2) := by
      intro z hz
      obtain ⟨c, hc, r, hr, rfl⟩ := hBs z (List.mem_toFinset.1 hz)
      exact Finset.mem_image.2 ⟨(c, r), Finset.mem_product.2
        ⟨Finset.mem_range.2 hc, Finset.mem_range.2 hr⟩, rfl⟩
    refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
    rw [Finset.card_product, Finset.card_range, Finset.card_range, Nat.mul_comm]
  have hexT : ∃ k, next base s N (stripRun β ω k).1 (stripRun β ω k).2 = none := by
    by_contra h
    push_neg at h
    have h1 := hlen (s * N + 1) (fun k' _ => h k')
    have h2 := hbound (s * N + 1)
    omega
  have hcol : ∀ k, (∃ c < N, colFull base s (stripRun β ω k).1 c) →
      ∃ c, (stripCol base s N c).ncard = s ∧ stripCol base s N c ⊆ {x | x ∈ (stripRun β ω k).1} := by
    rintro k ⟨c, hc, hfull⟩
    refine ⟨base ⟨0, by omega⟩ + c, ?_, ?_⟩
    · rw [stripCol_eq hd hc]
      exact ncard_image_Iio (fun r r' h => (spt_inj hd h).2) s
    · rw [stripCol_eq hd hc]
      rintro _ ⟨r, hr, rfl⟩
      exact hfull r hr
  refine ⟨Nat.find hexT, ?_, ?_, ?_, ?_⟩
  · by_contra hT
    push_neg at hT
    have h1 := hlen (s * N + 1) (fun k' hk' => Nat.find_min hexT (by omega))
    have h2 := hbound (s * N + 1)
    omega
  · rw [hβ]; exact Nat.find_spec hexT
  · intro k _ x hx
    rw [hβ] at hx
    obtain ⟨hxs, hxB, hxW⟩ := next_legal hs hx
    exact ⟨(mem_strip hd).2 hxs, hxB, hxW⟩
  · rcases next_none (Nat.find_spec hexT) with hfull | ⟨hprot, hused⟩
    · exact Or.inl (hcol _ hfull)
    obtain ⟨⟨hBn, hWn, hdj, -⟩, hpot | hfull⟩ := hinv (Nat.find hexT)
    · obtain ⟨r, hr, hrow⟩ := final_row hd hs hBn hWn hdj hpot hprot hused
      right
      refine ⟨base ⟨1, by omega⟩ + r, ?_, ?_, ?_⟩
      · rw [stripRow_eq hd hr]
        exact ncard_image_Iio (fun c c' h => (spt_inj hd h).1) N
      · rw [stripRow_eq hd hr]
        rintro _ ⟨c, hc, rfl⟩
        exact Or.inl (hused c hc r hr) |>.elim id id
      · rw [stripRow_eq hd hr]
        exact hrow
    · exact Or.inl (hcol _ hfull)


/-- **Theorem 10.1** (`end:main`): for every positive finite-valued `h` with
`sup n / h(n) = ∞` and every fresh causal generator, some full enumeration of `ℤ^d` has
`δ_h(O, ℤ^d) < 1/2`. (No monotonicity of `h` is assumed, as in the paper.) -/
theorem end_main {d : ℕ} (hd : 2 ≤ d) (h : ℕ → ℝ) (hpos : ∀ n, 1 ≤ n → 0 < h n)
    (hsup : ¬ BddAbove ((fun n : ℕ => (n : ℝ) / h n) '' Ici 1))
    (G : Generator (Pt d)) (hG : G.Fresh) :
    ∃ w, IsFullEnumeration w (univ : Set (Pt d)) ∧ deltaH h (G.outputSet w) univ < 1 / 2 := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hex : ∀ B : ℝ, ∃ n : ℕ, 1 ≤ n ∧ B < (n : ℝ) / h n := by
    intro B
    by_contra hcon
    push_neg at hcon
    exact hsup ⟨B, by rintro _ ⟨n, hn, rfl⟩; exact hcon n hn⟩
  have hsJ : ∀ j : ℕ, ∃ n : ℕ, 2 ≤ n ∧ (j : ℝ) ≤ (n : ℝ) / h n := by
    intro j
    obtain ⟨n, hn1, hn⟩ := hex (max j (1 / h 1))
    refine ⟨n, ?_, le_trans (le_max_left _ _) hn.le⟩
    by_contra h2
    have h1 : n = 1 := by omega
    subst h1
    have := lt_of_le_of_lt (le_max_right _ _) hn
    simp at this
  have hNT : ∀ t : ℕ, ∃ n : ℕ, 1 ≤ n ∧ (t : ℝ) ≤ (n : ℝ) / h n := fun t => by
    obtain ⟨n, hn1, hn⟩ := hex t
    exact ⟨n, hn1, hn.le⟩
  choose sJ hsJ2 hsJr using hsJ
  choose NT hNT1 hNTr using hNT
  have SG := fun j => end_strip (d := d) hd (sJ j) (hsJ2 j)
  choose γ hγ hγβ using SG
  have hB : ∀ (n : ℕ) (base : Pt d), ∃ β,
      EndpointAux.StripSpec base (sJ n.unpair.1) (NT n) (γ n.unpair.1) β :=
    fun n base => hγβ n.unpair.1 (NT n) (hNT1 n) base
  choose Bn hBn using hB
  have hbase : ∀ (n : ℕ) (P : List (Pt d)), ∃ base,
      Disjoint (usedBy G P) (strip base (sJ n.unpair.1) (NT n)) :=
    fun n P => EndpointAux.exists_base hd1 _ (SeparationAux.usedBy_finite G P) _ _
  choose bch hbch using hbase
  obtain ⟨e, he⟩ := exists_surjective_nat (Pt d)
  let S : EndpointAux.Sched d := ⟨G, e, fun n => sJ n.unpair.1, NT, bch, Bn⟩
  have hfacts := fun n => S.stage_facts hG n (γ n.unpair.1) (hbch n (S.pre n)) (hBn n (S.base n))
  refine ⟨S.w, ?_, ?_⟩
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨n, rfl⟩ := he x
    refine ⟨(S.stages n).length, ?_⟩
    rw [S.w_eq (m := n + 1) (by rw [S.stages_succ]; simp [EndpointAux.Sched.pre])]
    rw [S.stages_succ]
    simp [EndpointAux.Sched.pre, List.getD_eq_getElem?_getD]
    rfl
  · have key : ∃ c : ℝ, c < 1 / 2 ∧ ∀ lam : ℝ, testInf h (G.outputSet S.w) univ lam ≤ c := by
      by_cases hA : ∃ j, ∀ M, ∃ n ≥ M, n.unpair.1 = j ∧
          ¬ EndpointAux.colAt (S.base n) (S.sh n) (S.Nw n) (S.run n).1
      · obtain ⟨j, hj⟩ := hA
        refine ⟨1 / 2 - γ j, by linarith [hγ j], fun lam => ?_⟩
        obtain ⟨n, hnM, hnj, hncol⟩ := hj ⌈lam⌉₊
        obtain ⟨c0, hcard, hsub, hW⟩ := (hfacts n).2.resolve_left hncol
        have hN1 : 1 ≤ S.Nw n := hNT1 n
        have hne : (stripRow (S.base n) (S.sh n) (S.Nw n) c0).Nonempty :=
          Set.nonempty_of_ncard_ne_zero (by omega)
        obtain ⟨R, hR⟩ := EndpointAux.row_rect hN1 hne
        have hvol : R.vol = S.Nw n := by rw [Rect.vol, hR, hcard]
        apply EndpointAux.testInf_le _ lam _ R
        · rw [hvol]
          have hhp : 0 < h (NT n) := hpos _ (hNT1 n)
          have h1 := (le_div_iff₀ hhp).1 (hNTr n)
          have h2 : lam ≤ (n : ℝ) := (Nat.le_ceil lam).trans (by exact_mod_cast hnM)
          show lam * h (NT n) ≤ (NT n : ℕ)
          nlinarith
        · rw [hvol, hR, ← hnj]
          refine le_trans ?_ hW
          have hsub2 : G.outputSet S.w ∩ stripRow (S.base n) (S.sh n) (S.Nw n) c0 ⊆
              stripRow (S.base n) (S.sh n) (S.Nw n) c0 ∩ {x | x ∈ (S.run n).2} := by
            rintro x ⟨hxO, hxR⟩
            exact ⟨hxR, S.out_in_replies hG n (hbch n (S.pre n)) hxR.1 (hsub hxR) hxO⟩
          exact_mod_cast Set.ncard_le_ncard hsub2
            ((List.finite_toSet _).subset Set.inter_subset_right)
      · push_neg at hA
        refine ⟨0, by norm_num, fun lam => ?_⟩
        obtain ⟨M, hM⟩ := hA ⌈lam⌉₊
        set n := Nat.pair ⌈lam⌉₊ M with hn
        have hnj : n.unpair.1 = ⌈lam⌉₊ := by simp [hn, Nat.unpair_pair]
        obtain ⟨c0, hcard, hsub⟩ := hM n (Nat.right_le_pair _ _) hnj
        have hs1 : 1 ≤ S.sh n := le_trans (by norm_num) (hsJ2 n.unpair.1)
        have hne : (stripCol (S.base n) (S.sh n) (S.Nw n) c0).Nonempty :=
          Set.nonempty_of_ncard_ne_zero (by omega)
        obtain ⟨R, hR⟩ := EndpointAux.col_rect hs1 hne
        have hvol : R.vol = S.sh n := by rw [Rect.vol, hR, hcard]
        apply EndpointAux.testInf_le _ lam _ R
        · rw [hvol]
          have hhp : 0 < h (sJ n.unpair.1) := hpos _ (le_trans (by norm_num) (hsJ2 _))
          have h1 := (le_div_iff₀ hhp).1 (hsJr n.unpair.1)
          have h2 : lam ≤ (n.unpair.1 : ℝ) := by rw [hnj]; exact Nat.le_ceil lam
          show lam * h (sJ n.unpair.1) ≤ (sJ n.unpair.1 : ℕ)
          nlinarith
        · have hempty : G.outputSet S.w ∩ R.pts = ∅ := by
            rw [hR]
            ext x
            simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
            intro hxO hxC
            have hxr := hsub hxC
            exact ((hfacts n).1 x hxr).2
              (S.out_in_replies hG n (hbch n (S.pre n)) hxC.1 (Or.inl hxr) hxO)
          rw [hempty, Set.ncard_empty]
          simp
    obtain ⟨c, hc, hle⟩ := key
    have := le_of_tendsto' (deltaH_tendsto h hpos (G.outputSet S.w) univ).1 hle
    linarith


/-- **Theorem 8.3** (`thm:overview`), combined: part (1) is `thm_overview_1` (every `τ > 0`; Theorem 9.2;
`PointRank` uses the finite-evidence topology), part (2) is `end_main` (Theorem 10.1). -/
theorem thm_overview {d : ℕ} (hd : 2 ≤ d) :
    (∀ (X : Set (Set (Pt d))), LangClass X → ∀ τ ε : ℝ, 0 < τ → 0 < ε → ε < 1 / 2 →
      ∃ G ∈ ValidGen X, ∀ K ∈ X, Nonvacuous (hTau τ) K → (∃ r, PointRank X K r) →
        Guarantees (dH (hTau τ)) G K (1 / 2 - ε)) ∧
    (∀ h : ℕ → ℝ, (∀ n, 1 ≤ n → 0 < h n) → ¬ BddAbove ((fun n : ℕ => (n : ℝ) / h n) '' Ici 1) →
      ∀ G : Generator (Pt d), G.Fresh →
        ∃ w, IsFullEnumeration w (univ : Set (Pt d)) ∧ deltaH h (G.outputSet w) univ < 1 / 2) := by
  exact ⟨fun X hX τ ε hτ hε0 hε => thm_overview_1 hd hX hτ hε0 hε,
    fun h hpos hsup G hG => end_main hd h hpos hsup G hG⟩



end BanachDensityHD

