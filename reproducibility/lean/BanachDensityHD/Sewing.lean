import BanachDensityHD.Forest

/-!
# Lemma 8.11 (`lem:sewing`): a dyadic partition of `ℤ^d` with a logarithmic sewing bound

Proof of `lem_sewing` (`BanachDensityHD/Characterization.lean`), following the
manuscript's proof (§8, "A spatial partition with a logarithmic sewing bound"):

* radii `r_j = 2^(2^j)`; the central board is `Q_2 = [-2,2]^d` (level `0`);
* for `j ≥ 0` the shell `Q_{r_{j+1}} \ Q_{r_j}` (level `j+1`) is split into `2d` boxes according to
  the first coordinate `i` with `|x_i| > r_j` and the sign of `x_i`.

For a rectangle `R` let `D` be its largest side difference `hi_k - lo_k`. A level `ℓ` with
`r_ℓ ≤ D` is *small*: each of its at most `2d` boards contributes at most `3d log r_ℓ`, and
`∑_{r_ℓ ≤ D} log r_ℓ ≤ 2 log D`. The sup norm varies by at most `D` across `R`, so at most two
*large* levels (`r_ℓ > D`) meet `R`; each of their at most `4d` boards contributes at most
`log(2 + V(R))`. Together: `(12d² + 4d) log(2 + V(R))`. The `h` bound follows since
`1 ≤ V(C ∩ R) ≤ V(R)` and `g` is nondecreasing on `[1, ∞)`.
-/

namespace BanachDensityHD

open Set Filter
open scoped Classical

namespace SewingAux

/-! ### Radii and the sup norm -/

/-- The radii `r_j = 2^(2^j)`. -/
def rad (j : ℕ) : ℕ := 2 ^ (2 ^ j)

theorem rad_zero : rad 0 = 2 := rfl

theorem rad_succ (j : ℕ) : rad (j + 1) = rad j ^ 2 := by
  unfold rad; rw [pow_succ, pow_mul]

theorem two_le_rad (j : ℕ) : 2 ≤ rad j := by
  unfold rad
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ (2 ^ j) := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_two_pow)

theorem rad_mono {j j' : ℕ} (h : j ≤ j') : rad j ≤ rad j' :=
  Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) h)

theorem rad_succ_ge (j : ℕ) : 2 * rad j ≤ rad (j + 1) := by
  rw [rad_succ, sq]; exact Nat.mul_le_mul_right _ (two_le_rad j)

/-- The sup norm `‖x‖_∞` as a natural number. -/
def nrm {d : ℕ} (x : Pt d) : ℕ := Finset.univ.sup fun k => (x k).natAbs

theorem abs_le_nrm {d : ℕ} (x : Pt d) (k : Fin d) : |x k| ≤ (nrm x : ℤ) := by
  rw [← Int.natCast_natAbs]
  exact_mod_cast Finset.le_sup (f := fun k => (x k).natAbs) (Finset.mem_univ k)

theorem nrm_le_iff {d : ℕ} (x : Pt d) (M : ℕ) : nrm x ≤ M ↔ ∀ k, |x k| ≤ (M : ℤ) := by
  unfold nrm
  rw [Finset.sup_le_iff]
  simp only [Finset.mem_univ, true_implies, ← Int.natCast_natAbs, Nat.cast_le]

theorem lt_nrm_iff {d : ℕ} (x : Pt d) (M : ℕ) : M < nrm x ↔ ∃ k, (M : ℤ) < |x k| := by
  rw [← not_le, nrm_le_iff]
  push_neg
  rfl

/-! ### The boards -/

/-- Board indices: `none` is the central board `[-2,2]^d`; `some (j, i, s)` is the box of the
level-`(j+1)` shell whose first coordinate outside `[-r_j, r_j]` is `i`, positive iff `s`. -/
abbrev Idx (d : ℕ) := Option (ℕ × Fin d × Bool)

/-- The level of a board index. -/
def lev {d : ℕ} : Idx d → ℕ
  | none => 0
  | some (j, _, _) => j + 1

/-- Lower corner of a board. -/
def blo {d : ℕ} : Idx d → Pt d
  | none => fun _ => -2
  | some (j, i, s) => fun k =>
      if k < i then -(rad j : ℤ) else if k = i then (if s then (rad j : ℤ) + 1 else -(rad (j + 1) : ℤ))
      else -(rad (j + 1) : ℤ)

/-- Upper corner of a board. -/
def bhi {d : ℕ} : Idx d → Pt d
  | none => fun _ => 2
  | some (j, i, s) => fun k =>
      if k < i then (rad j : ℤ) else if k = i then (if s then (rad (j + 1) : ℤ) else -(rad j : ℤ) - 1)
      else (rad (j + 1) : ℤ)

theorem blo_le_bhi {d : ℕ} (a : Idx d) : blo a ≤ bhi a := by
  intro k
  have h2 := two_le_rad 0
  rcases a with _ | ⟨j, i, s⟩
  · simp [blo, bhi]
  · have h1 := rad_succ_ge j
    have h0 := two_le_rad j
    have h1' : (2 * rad j : ℤ) ≤ rad (j + 1) := by exact_mod_cast h1
    have h0' : (2 : ℤ) ≤ rad j := by exact_mod_cast h0
    simp only [blo, bhi]
    split_ifs <;> omega

/-- The board with index `a`. -/
def board {d : ℕ} (a : Idx d) : Rect d := Rect.mk (blo a) (bhi a) (blo_le_bhi a)

theorem mem_board {d : ℕ} (a : Idx d) (x : Pt d) :
    x ∈ (board a).pts ↔ ∀ k, blo a k ≤ x k ∧ x k ≤ bhi a k := by
  simp only [board, Rect.pts, Rect.lo, Rect.hi, mem_Icc, Pi.le_def]
  exact ⟨fun h k => ⟨h.1 k, h.2 k⟩, fun h => ⟨fun k => (h k).1, fun k => (h k).2⟩⟩

theorem mem_none {d : ℕ} (x : Pt d) : x ∈ (board (none : Idx d)).pts ↔ ∀ k, |x k| ≤ 2 := by
  rw [mem_board]
  simp only [blo, bhi, abs_le]

/-- Membership in a shell board. -/
theorem mem_some {d : ℕ} (j : ℕ) (i : Fin d) (s : Bool) (x : Pt d) :
    x ∈ (board (some (j, i, s))).pts ↔
      (∀ k, k < i → |x k| ≤ (rad j : ℤ)) ∧
      ((rad j : ℤ) < |x i| ∧ |x i| ≤ (rad (j + 1) : ℤ) ∧ (s = true ↔ 0 < x i)) ∧
      (∀ k, i < k → |x k| ≤ (rad (j + 1) : ℤ)) := by
  have h0' : (2 : ℤ) ≤ rad j := by exact_mod_cast two_le_rad j
  rw [mem_board]
  constructor
  · intro h
    refine ⟨fun k hk => ?_, ?_, fun k hk => ?_⟩
    · have := h k
      simp only [blo, bhi, hk, ↓reduceIte] at this
      exact abs_le.2 this
    · have := h i
      simp only [blo, bhi, lt_irrefl, ↓reduceIte] at this
      cases s
      · simp only [Bool.false_eq_true, ↓reduceIte] at this
        simp only [Bool.false_eq_true, false_iff, not_lt]
        refine ⟨?_, ?_, by omega⟩
        · rw [abs_of_neg (by omega)]; omega
        · rw [abs_of_neg (by omega)]; omega
      · simp only [↓reduceIte] at this
        simp only [true_iff]
        refine ⟨?_, ?_, by omega⟩
        · rw [abs_of_pos (by omega)]; omega
        · rw [abs_of_pos (by omega)]; omega
    · have := h k
      simp only [blo, bhi, not_lt.2 hk.le, ne_of_gt hk, ↓reduceIte] at this
      exact abs_le.2 this
  · rintro ⟨h1, ⟨h2, h3, h4⟩, h5⟩ k
    rcases lt_trichotomy k i with hk | rfl | hk
    · simp only [blo, bhi, hk, ↓reduceIte]; exact abs_le.1 (h1 k hk)
    · simp only [blo, bhi, lt_irrefl, ↓reduceIte]
      cases s
      · simp only [Bool.false_eq_true, false_iff, not_lt] at h4
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [abs_of_nonpos h4] at h2 h3
        omega
      · simp only [true_iff] at h4
        simp only [↓reduceIte]
        rw [abs_of_pos h4] at h2 h3
        omega
    · simp only [blo, bhi, not_lt.2 hk.le, ne_of_gt hk, ↓reduceIte]
      exact abs_le.1 (h5 k hk)

/-- Every board lies in the cube `Q_{r_ℓ}` of its level. -/
theorem nrm_le_of_mem {d : ℕ} {a : Idx d} {x : Pt d} (hx : x ∈ (board a).pts) :
    nrm x ≤ rad (lev a) := by
  rw [nrm_le_iff]
  rcases a with _ | ⟨j, i, s⟩
  · intro k; rw [mem_none] at hx; exact hx k
  · rw [mem_some] at hx
    obtain ⟨h1, ⟨_, h3, _⟩, h5⟩ := hx
    have hm : (rad j : ℤ) ≤ rad (j + 1) := by exact_mod_cast rad_mono (Nat.le_succ j)
    intro k
    rcases lt_trichotomy k i with hk | rfl | hk
    · exact (h1 k hk).trans hm
    · exact h3
    · exact h5 k hk

/-- A point of a shell board of level `j+1` has sup norm above `r_j`. -/
theorem lt_nrm_of_mem {d : ℕ} {j : ℕ} {i : Fin d} {s : Bool} {x : Pt d}
    (hx : x ∈ (board (some (j, i, s))).pts) : rad j < nrm x := by
  rw [mem_some] at hx
  rw [lt_nrm_iff]; exact ⟨i, hx.2.1.1⟩

/-- Distinct board indices give disjoint boards. -/
theorem idx_unique {d : ℕ} {a b : Idx d} {x : Pt d} (ha : x ∈ (board a).pts)
    (hb : x ∈ (board b).pts) : a = b := by
  have key : ∀ (j : ℕ) (i : Fin d) (s : Bool), x ∈ (board (some (j, i, s))).pts →
      x ∉ (board (none : Idx d)).pts := by
    intro j i s h hn
    have h1 := lt_nrm_of_mem h
    have h2 := nrm_le_of_mem hn
    have := two_le_rad j
    simp only [lev, rad_zero] at h2
    omega
  have lvl : ∀ (j j' : ℕ) (i i' : Fin d) (s s' : Bool), x ∈ (board (some (j, i, s))).pts →
      x ∈ (board (some (j', i', s'))).pts → j ≤ j' := by
    intro j j' i i' s s' h h'
    by_contra hlt
    push Not at hlt
    have h1 := lt_nrm_of_mem h
    have h2 := nrm_le_of_mem h'
    have := rad_mono (show j' + 1 ≤ j by omega)
    simp only [lev] at h2
    omega
  have crd : ∀ (j : ℕ) (i i' : Fin d) (s s' : Bool), x ∈ (board (some (j, i, s))).pts →
      x ∈ (board (some (j, i', s'))).pts → ¬ i < i' := by
    intro j i i' s s' h h' hlt
    rw [mem_some] at h h'
    have := h'.1 i hlt
    have := h.2.1.1
    omega
  rcases a with _ | ⟨j, i, s⟩ <;> rcases b with _ | ⟨j', i', s'⟩
  · rfl
  · exact absurd ha (key _ _ _ hb)
  · exact absurd hb (key _ _ _ ha)
  · have hj : j = j' := le_antisymm (lvl _ _ _ _ _ _ ha hb) (lvl _ _ _ _ _ _ hb ha)
    subst hj
    have hi : i = i' := by
      rcases lt_trichotomy i i' with h | h | h
      · exact absurd h (crd _ _ _ _ _ ha hb)
      · exact h
      · exact absurd h (crd _ _ _ _ _ hb ha)
    subst hi
    have hs : s = s' := by
      rw [mem_some] at ha hb
      exact Bool.eq_iff_iff.2 (ha.2.1.2.2.trans hb.2.1.2.2.symm)
    subst hs
    rfl

/-- Every point lies in some board. -/
theorem exists_board {d : ℕ} (x : Pt d) : ∃ a : Idx d, x ∈ (board a).pts := by
  by_cases h2 : nrm x ≤ 2
  · exact ⟨none, (mem_none x).2 ((nrm_le_iff x 2).1 h2)⟩
  push Not at h2
  have hex : ∃ j, nrm x ≤ rad (j + 1) := by
    refine ⟨nrm x, ?_⟩
    unfold rad
    calc nrm x ≤ 2 ^ (nrm x + 1) := (Nat.lt_two_pow_self).le.trans
            (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _))
      _ ≤ 2 ^ (2 ^ (nrm x + 1)) := Nat.pow_le_pow_right (by norm_num) (Nat.lt_two_pow_self).le
  let j := Nat.find hex
  have hjup : nrm x ≤ rad (j + 1) := Nat.find_spec hex
  have hjlo : rad j < nrm x := by
    rcases hj : j with _ | j'
    · rw [rad_zero]; exact h2
    · have := Nat.find_min hex (show j' < j by omega)
      push Not at this
      exact this
  obtain ⟨k0, hk0⟩ := (lt_nrm_iff x _).1 hjlo
  let S : Finset (Fin d) := Finset.univ.filter fun k => (rad j : ℤ) < |x k|
  have hS : S.Nonempty := ⟨k0, by simp [S, hk0]⟩
  let i := S.min' hS
  have hi : (rad j : ℤ) < |x i| := by
    have := S.min'_mem hS
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this
  have hbelow : ∀ k, k < i → |x k| ≤ (rad j : ℤ) := by
    intro k hk
    by_contra hc
    push Not at hc
    have := S.min'_le k (by simp [S, hc])
    exact absurd hk (not_lt.2 this)
  have hall := (nrm_le_iff x _).1 hjup
  refine ⟨some (j, i, decide (0 < x i)), (mem_some _ _ _ x).2 ⟨hbelow, ⟨hi, hall i, ?_⟩,
    fun k _ => hall k⟩⟩
  simp

/-! ### Rectangles: volume, side, and the sup norm across a rectangle -/

theorem vol_eq {d : ℕ} (lo hi : Pt d) (R : Rect d) (hlo : R.lo = lo) (hhi : R.hi = hi) :
    R.vol = ∏ k, (hi k + 1 - lo k).toNat := by
  unfold Rect.vol Rect.pts
  rw [hlo, hhi, ← Finset.coe_Icc, ncard_coe_finset, Pi.card_Icc]
  simp only [Int.card_Icc]

/-- The largest side difference `D(R) = max_k (hi_k - lo_k)`. -/
def side {d : ℕ} (R : Rect d) : ℕ := Finset.univ.sup fun k => (R.hi k - R.lo k).toNat

theorem side_le_vol {d : ℕ} (R : Rect d) : side R ≤ R.vol := by
  rw [vol_eq R.lo R.hi R rfl rfl]
  unfold side
  rw [Finset.sup_le_iff]
  intro k _
  have hpos : ∀ k ∈ (Finset.univ : Finset (Fin d)), 1 ≤ (R.hi k + 1 - R.lo k).toNat := by
    intro k _; have : R.lo k ≤ R.hi k := R.le k; omega
  calc (R.hi k - R.lo k).toNat ≤ (R.hi k + 1 - R.lo k).toNat := by omega
    _ ≤ ∏ k, (R.hi k + 1 - R.lo k).toNat := Finset.single_le_prod hpos (Finset.mem_univ k)

/-- The sup norm varies by at most `D(R)` across `R`. -/
theorem nrm_lip {d : ℕ} (R : Rect d) {x y : Pt d} (hx : x ∈ R.pts) (hy : y ∈ R.pts) :
    nrm y ≤ nrm x + side R := by
  rw [nrm_le_iff]
  intro k
  have h1 := abs_le_nrm x k
  have h2 : ((R.hi k - R.lo k).toNat : ℤ) ≤ (side R : ℤ) := by
    exact_mod_cast Finset.le_sup (f := fun k => (R.hi k - R.lo k).toNat) (Finset.mem_univ k)
  have hxk : R.lo k ≤ x k ∧ x k ≤ R.hi k := ⟨hx.1 k, hx.2 k⟩
  have hyk : R.lo k ≤ y k ∧ y k ≤ R.hi k := ⟨hy.1 k, hy.2 k⟩
  push_cast
  rw [abs_le] at h1 ⊢
  omega

/-- Any set of points of sup norm at most `r` (a subset of the cube `Q_r = [-r, r]^d`) has at most
`(2r+1)^d` elements. -/
theorem ncard_le_cube {d : ℕ} (r : ℕ) (S : Set (Pt d)) (hS : ∀ x ∈ S, nrm x ≤ r) :
    S.ncard ≤ (2 * r + 1) ^ d := by
  have hsub : S ⊆ ((Finset.Icc (fun _ => -(r : ℤ)) (fun _ => (r : ℤ)) : Finset (Pt d)) : Set (Pt d)) := by
    intro x hx
    rw [Finset.coe_Icc, mem_Icc]
    have := (nrm_le_iff x r).1 (hS x hx)
    exact ⟨fun k => (abs_le.1 (this k)).1, fun k => (abs_le.1 (this k)).2⟩
  refine (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans (le_of_eq ?_)
  rw [ncard_coe_finset, Pi.card_Icc]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

theorem two_add_le {d : ℕ} (hd : 2 ≤ d) (r v : ℕ) (hr : 2 ≤ r) (hv : v ≤ (2 * r + 1) ^ d) :
    2 + v ≤ r ^ (3 * d) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  have h3 : 2 * r + 2 ≤ r ^ 3 := by
    have : r ^ 3 = r * r * r := by ring
    rw [this]; nlinarith
  have hA : (2 * r + 1) ^ e ≤ (2 * r + 2) ^ e := Nat.pow_le_pow_left (by omega) e
  have hB : 1 ≤ (2 * r + 1) ^ e := Nat.one_le_pow _ _ (by omega)
  calc 2 + v ≤ 2 + (2 * r + 1) ^ (e + 2) := by omega
    _ ≤ (2 * r + 2) ^ (e + 2) := by
        rw [pow_add, pow_add]
        nlinarith
    _ ≤ (r ^ 3) ^ (e + 2) := Nat.pow_le_pow_left h3 _
    _ = r ^ (3 * (e + 2)) := by rw [← pow_mul]

/-! ### The partition and the boards meeting a rectangle -/

/-- The partition `𝒫`: all boards. -/
def Pb (d : ℕ) : Set (Rect d) := range (board (d := d))

theorem board_injective {d : ℕ} : Function.Injective (board (d := d)) := by
  intro a b h
  have hx : blo a ∈ (board a).pts := Set.left_mem_Icc.2 (blo_le_bhi a)
  exact idx_unique hx (h ▸ hx)

/-- The indices of the boards meeting `R`. -/
def met {d : ℕ} (R : Rect d) : Set (Idx d) := {a | ((board a).pts ∩ R.pts).Nonempty}

theorem met_finite {d : ℕ} (R : Rect d) : (met R).Finite := by
  let idx : Pt d → Idx d := fun x => Classical.choose (exists_board x)
  refine ((BasicAux.rect_pts_finite R).image idx).subset ?_
  rintro a ⟨x, hxa, hxR⟩
  exact ⟨x, hxR, idx_unique (Classical.choose_spec (exists_board x)) hxa⟩

theorem metBoards_eq {d : ℕ} (R : Rect d) :
    {C ∈ Pb d | (C.pts ∩ R.pts).Nonempty} = board '' met R := by
  ext C
  constructor
  · rintro ⟨⟨a, rfl⟩, h⟩; exact ⟨a, h, rfl⟩
  · rintro ⟨a, h, rfl⟩; exact ⟨⟨a, rfl⟩, h⟩

theorem finsum_eq {d : ℕ} (R : Rect d) (F : Rect d → ℝ) :
    (∑ᶠ C ∈ {C ∈ Pb d | (C.pts ∩ R.pts).Nonempty}, F C) =
      ∑ a ∈ (met_finite R).toFinset, F (board a) := by
  rw [metBoards_eq, finsum_mem_image board_injective.injOn,
    finsum_mem_eq_finite_toFinset_sum _ (met_finite R)]

/-- `V(C ∩ R)` for the board `C` with index `a`. -/
noncomputable def vv {d : ℕ} (R : Rect d) (a : Idx d) : ℕ := ((board a).pts ∩ R.pts).ncard

theorem one_le_vv {d : ℕ} {R : Rect d} {a : Idx d} (ha : a ∈ met R) : 1 ≤ vv R a := by
  have := (Set.ncard_pos ((BasicAux.rect_pts_finite R).inter_of_right _)).2 ha
  unfold vv; omega

theorem vv_le_vol {d : ℕ} (R : Rect d) (a : Idx d) : vv R a ≤ R.vol :=
  Set.ncard_le_ncard Set.inter_subset_right (BasicAux.rect_pts_finite R)

theorem log_vv_le_rad {d : ℕ} (hd : 2 ≤ d) (R : Rect d) (a : Idx d) :
    Real.log (2 + (vv R a : ℝ)) ≤ 3 * d * Real.log (rad (lev a)) := by
  have hc : vv R a ≤ (2 * rad (lev a) + 1) ^ d :=
    ncard_le_cube _ _ fun x hx => nrm_le_of_mem hx.1
  have h := two_add_le hd _ _ (two_le_rad (lev a)) hc
  have h' : (2 + (vv R a : ℝ)) ≤ ((rad (lev a) : ℝ)) ^ (3 * d) := by exact_mod_cast h
  calc Real.log (2 + (vv R a : ℝ)) ≤ Real.log (((rad (lev a) : ℝ)) ^ (3 * d)) :=
        Real.log_le_log (by positivity) h'
    _ = 3 * d * Real.log (rad (lev a)) := by rw [Real.log_pow]; push_cast; ring

/-- At most two levels with `r_ℓ > D(R)` meet `R`: if level `lev a` is large, every met level is at
most `lev a + 1`. -/
theorem spread {d : ℕ} (R : Rect d) {a b : Idx d} (ha : a ∈ met R) (hb : b ∈ met R)
    (hlarge : side R < rad (lev a)) : lev b ≤ lev a + 1 := by
  by_contra hc
  push Not at hc
  obtain ⟨x, hxa, hxR⟩ := ha
  obtain ⟨y, hyb, hyR⟩ := hb
  rcases b with _ | ⟨j, i, s⟩
  · simp [lev] at hc
  have hc' : lev a + 1 < j + 1 := hc
  have h1 := nrm_le_of_mem hxa
  have h2 := lt_nrm_of_mem hyb
  have h3 := rad_mono (show lev a + 1 ≤ j by omega)
  have h4 := nrm_lip R hxR hyR
  have h5 := rad_succ (lev a)
  have h6 := two_le_rad (lev a)
  have h7 : 2 * rad (lev a) ≤ rad (lev a) ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right _ h6
  omega

/-- The small-level bound `∑_{ℓ ∈ S} log r_ℓ ≤ 2 log D` when every `r_ℓ ≤ D`.
For positive `D` this has the usual logarithmic interpretation. The totalized statement
also permits `S = ∅` and `D = 0`, where `Real.log 0 = 0`. -/
theorem sum_log_rad_le (S : Finset ℕ) (D : ℕ) (hS : ∀ ℓ ∈ S, rad ℓ ≤ D) :
    ∑ ℓ ∈ S, Real.log (rad ℓ) ≤ 2 * Real.log D := by
  have hlog : ∀ ℓ, Real.log (rad ℓ) = (2 ^ ℓ : ℕ) * Real.log 2 := by
    intro ℓ; unfold rad; push_cast; rw [Real.log_pow]; push_cast; ring
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.sum_empty]
    have := Real.log_natCast_nonneg D
    linarith
  simp only [hlog]
  rw [← Finset.sum_mul]
  have hlt : ∑ ℓ ∈ S, 2 ^ ℓ < 2 * 2 ^ (S.max' hne) := by
    rw [← pow_succ']
    exact Nat.geomSum_lt le_rfl fun ℓ hℓ => Nat.lt_succ_of_le (S.le_max' ℓ hℓ)
  have hJ := hS _ (S.max'_mem hne)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (∑ ℓ ∈ S, ((2 ^ ℓ : ℕ) : ℝ)) ≤ 2 * ((2 ^ (S.max' hne) : ℕ) : ℝ) := by
    rw [← Nat.cast_sum]; exact_mod_cast hlt.le
  have h2 : ((2 ^ (S.max' hne) : ℕ) : ℝ) * Real.log 2 ≤ Real.log D := by
    rw [← hlog]
    exact Real.log_le_log (by have := two_le_rad (S.max' hne); positivity) (by exact_mod_cast hJ)
  nlinarith

/-- The boards of one level: at most `2d` indices. -/
theorem card_fiber_le {d : ℕ} (hd : 2 ≤ d) (A : Finset (Idx d)) (ℓ : ℕ) :
    (A.filter fun a => lev a = ℓ).card ≤ 2 * d := by
  rcases ℓ with _ | j
  · have : (A.filter fun a => lev a = 0) ⊆ {none} := by
      intro a ha
      rw [Finset.mem_filter] at ha
      rcases a with _ | ⟨j, i, s⟩
      · simp
      · simp [lev] at ha
    exact (Finset.card_le_card this).trans (by simp; omega)
  · have : (A.filter fun a => lev a = j + 1) ⊆
        (Finset.univ : Finset (Fin d × Bool)).image fun p => some (j, p.1, p.2) := by
      intro a ha
      rw [Finset.mem_filter] at ha
      rcases a with _ | ⟨j', i, s⟩
      · simp [lev] at ha
      · simp only [lev, add_left_inj] at ha
        rw [ha.2]
        exact Finset.mem_image.2 ⟨(i, s), Finset.mem_univ _, rfl⟩
    refine (Finset.card_le_card this).trans (Finset.card_image_le.trans ?_)
    simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, mul_comm]

/-- The logarithmic sewing bound, as a finite sum over board indices. -/
theorem log_sum_le {d : ℕ} (hd : 2 ≤ d) (R : Rect d) :
    ∑ a ∈ (met_finite R).toFinset, Real.log (2 + (vv R a : ℝ)) ≤
      (12 * (d : ℝ) ^ 2 + 4 * d) * Real.log (2 + R.vol) := by
  set A := (met_finite R).toFinset with hA
  set D := side R
  set W := Real.log (2 + (R.vol : ℝ))
  have hW : 0 ≤ W := Real.log_nonneg (by have : (0 : ℝ) ≤ R.vol := (by positivity); linarith)
  have hdpos : (0 : ℝ) ≤ d := by positivity
  let c : ℕ → ℝ := fun ℓ => if rad ℓ ≤ D then 3 * d * Real.log (rad ℓ) else W
  have hc0 : ∀ ℓ, 0 ≤ c ℓ := by
    intro ℓ; simp only [c]; split_ifs
    · have := Real.log_natCast_nonneg (rad ℓ); positivity
    · exact hW
  set T := A.image lev
  -- fiberwise decomposition
  have hfib := Finset.sum_fiberwise_of_maps_to (s := A) (t := T) (g := lev)
    (fun a ha => Finset.mem_image_of_mem lev ha) (fun a => Real.log (2 + (vv R a : ℝ)))
  rw [← hfib]
  have hstep : ∀ ℓ ∈ T, ∑ a ∈ A with lev a = ℓ, Real.log (2 + (vv R a : ℝ)) ≤ 2 * d * c ℓ := by
    intro ℓ _
    have hle : ∀ a ∈ A.filter (fun a => lev a = ℓ), Real.log (2 + (vv R a : ℝ)) ≤ c ℓ := by
      intro a ha
      rw [Finset.mem_filter] at ha
      simp only [c]
      split_ifs
      · rw [← ha.2]; exact log_vv_le_rad hd R a
      · apply Real.log_le_log (by positivity)
        have hvol : (vv R a : ℝ) ≤ R.vol := by exact_mod_cast vv_le_vol R a
        linarith
    refine (Finset.sum_le_card_nsmul _ _ _ hle).trans ?_
    rw [nsmul_eq_mul]
    have := card_fiber_le hd A ℓ
    have : ((A.filter fun a => lev a = ℓ).card : ℝ) ≤ 2 * d := by exact_mod_cast this
    exact mul_le_mul_of_nonneg_right this (hc0 ℓ)
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.mul_sum]
  -- split the levels into small and large
  have hsplit : ∑ ℓ ∈ T, c ℓ =
      ∑ ℓ ∈ T.filter (fun ℓ => rad ℓ ≤ D), 3 * d * Real.log (rad ℓ) +
        ∑ ℓ ∈ T.filter (fun ℓ => ¬ rad ℓ ≤ D), W := by
    simp only [c]; rw [Finset.sum_ite]
  have hsmall : ∑ ℓ ∈ T.filter (fun ℓ => rad ℓ ≤ D), 3 * d * Real.log (rad ℓ) ≤ 3 * d * (2 * W) := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (sum_log_rad_le _ D fun ℓ hℓ => (Finset.mem_filter.1 hℓ).2).trans ?_
    have hD : (D : ℝ) ≤ R.vol := by exact_mod_cast side_le_vol R
    have : Real.log D ≤ W := by
      rcases Nat.eq_zero_or_pos D with h0 | hpos
      · rw [h0, Nat.cast_zero, Real.log_zero]; exact hW
      · exact Real.log_le_log (by exact_mod_cast hpos) (by linarith)
    linarith
  have hlarge : ∑ ℓ ∈ T.filter (fun ℓ => ¬ rad ℓ ≤ D), W ≤ 2 * W := by
    rw [Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hW
    set TL := T.filter (fun ℓ => ¬ rad ℓ ≤ D)
    have hcard : TL.card ≤ 2 := by
      rcases TL.eq_empty_or_nonempty with h | hne
      · rw [h]; simp
      have hm := TL.min'_mem hne
      have hsub : TL ⊆ {TL.min' hne, TL.min' hne + 1} := by
        intro ℓ hℓ
        have hle := TL.min'_le ℓ hℓ
        obtain ⟨hmT, hmL⟩ := Finset.mem_filter.1 hm
        obtain ⟨hℓT, _⟩ := Finset.mem_filter.1 hℓ
        obtain ⟨a, haA, hal⟩ := Finset.mem_image.1 hmT
        obtain ⟨b, hbA, hbl⟩ := Finset.mem_image.1 hℓT
        rw [Set.Finite.mem_toFinset] at haA hbA
        have := spread R haA hbA (by rw [hal]; omega)
        rw [hal, hbl] at this
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      exact (Finset.card_le_card hsub).trans Finset.card_le_two
    exact_mod_cast hcard
  rw [hsplit]
  nlinarith

/-- The `h` sewing bound, as a finite sum over board indices. -/
theorem h_sum_le {d : ℕ} (hd : 2 ≤ d) (R : Rect d) (g : ℝ → ℝ) (hg1 : ∀ x, 1 ≤ x → 1 ≤ g x)
    (hgm : MonotoneOn g (Ici 1)) :
    ∑ a ∈ (met_finite R).toFinset, hLog g (vv R a) ≤ (12 * (d : ℝ) ^ 2 + 4 * d) * hLog g R.vol := by
  have hV : (1 : ℝ) ≤ R.vol := by exact_mod_cast BasicAux.rect_vol_pos R
  have hgV := hg1 _ hV
  have hpt : ∀ a ∈ (met_finite R).toFinset,
      hLog g (vv R a) ≤ g R.vol * Real.log (2 + (vv R a : ℝ)) := by
    intro a ha
    rw [Set.Finite.mem_toFinset] at ha
    have h1 : (1 : ℝ) ≤ vv R a := by exact_mod_cast one_le_vv ha
    have h2 : (vv R a : ℝ) ≤ R.vol := by exact_mod_cast vv_le_vol R a
    unfold hLog
    exact mul_le_mul_of_nonneg_right (hgm (mem_Ici.2 h1) (mem_Ici.2 hV) h2)
      (Real.log_nonneg (by linarith))
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum]
  calc g R.vol * ∑ a ∈ (met_finite R).toFinset, Real.log (2 + (vv R a : ℝ))
      ≤ g R.vol * ((12 * (d : ℝ) ^ 2 + 4 * d) * Real.log (2 + R.vol)) :=
        mul_le_mul_of_nonneg_left (log_sum_le hd R) (by linarith)
    _ = (12 * (d : ℝ) ^ 2 + 4 * d) * hLog g R.vol := by unfold hLog; ring

end SewingAux



end BanachDensityHD
