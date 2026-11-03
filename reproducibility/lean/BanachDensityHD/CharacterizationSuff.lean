import BanachDensityHD.CharacterizationProofs

/-!
# Section 8.3–8.5: sufficiency

The generator of the sufficiency direction of Theorems 8.1(1) and 8.2, built on an abstract forest
datum (`Cfg`): vertices `i < N` with labels `lab i` and tree occurrences `occ i` (a root-to-vertex
path of decorations in a supplied protected tree), the parent scan of `Forest.lean` on the
protected sets of the occurrences, the boards of a sewing partition `Pb`, the stored winning
strategies of the board games, and fallback fresh outputs. The simulation hypotheses of
Lemma 8.12 (`lem_hd_help`) are proved for this generator; Lemma 8.12 then gives the local quota
on every non-exceptional board, and the sewing bounds give the density.

The sewing partition (Lemma 8.11) enters only as an explicit hypothesis (`Sew`).
-/

namespace BanachDensityHD

open Set Filter
open scoped Classical

namespace SuffAux

variable {d : ℕ}

/-! ## Lists of decorations

The default decoration and the `i`-th decoration of a list are `TreesAux.d0` and `TreesAux.dat`
(`Trees.lean`), with their lemmas `dat_eq`, `dat_take` and `dat_append`. -/

open TreesAux (d0 dat dat_eq dat_take dat_append)

/-- The last decoration of a path. -/
def lastOf (l : List (Deco d)) : Deco d := l.getLastD d0

theorem lastOf_eq_dat (l : List (Deco d)) (hl : l ≠ []) : lastOf l = dat l (l.length - 1) := by
  have := List.length_pos_iff.mpr hl
  rw [lastOf, CharAux.getLastD_eq_getLast _ _ hl, List.getLast_eq_getElem,
    dat_eq (q := l) (j := l.length - 1) (by omega)]

/-- `TreesAux.dat_append` for a prefix: entries of a prefix are entries of the longer list. -/
theorem dat_of_prefix {l l' : List (Deco d)} (h : l <+: l') (i : ℕ) (hi : i < l.length) :
    dat l i = dat l' i := by
  obtain ⟨r, rfl⟩ := h
  exact (dat_append hi).symm

theorem lastOf_append (l : List (Deco d)) (w : Deco d) : lastOf (l ++ [w]) = w := by
  simp [lastOf]

/-- The protected sets of the vertices, read from their occurrences. -/
def Pof (f : ℕ → List (Deco d)) (i : ℕ) : Set (Pt d) := ↑(lastOf (f i)).P

/-! ## The forest datum -/

/-- The data of the construction: the parent scan mode, the vertices `i < N`, their labels, their
tree occurrences, the quota of a decoration, the threshold, and the board partition. -/
structure Cfg (d : ℕ) where
  strict : Bool
  N : ℕ∞
  lab : ℕ → Set (Pt d)
  occ : ℕ → List (Deco d)
  qd : Deco d → ℝ
  h : ℕ → ℝ
  Pb : Set (Rect d)

/-- A path of decorations is usable for a board: nonempty, nonincreasing labels, and geometrically
feasible outside the box of its last radius. -/
def PathOK (h : ℕ → ℝ) (qd : Deco d → ℝ) (p : List (Deco d)) : Prop :=
  p ≠ [] ∧ Antitone (fun i : Fin (p.length - 1 + 1) => (dat p i).L) ∧
    GeomFeasible h (fun i : Fin (p.length - 1 + 1) => (dat p i).L) (fun i => qd (dat p i))
      (fun i => (dat p i).s) (lastOf p).a

/-- Languages of the levels of a path. -/
def Lsf (p : List (Deco d)) : Fin (p.length - 1 + 1) → Set (Pt d) := fun i => (dat p i).L
/-- Cutoffs of the levels of a path. -/
def ssf (p : List (Deco d)) : Fin (p.length - 1 + 1) → ℝ := fun i => (dat p i).s

namespace Cfg
variable (c : Cfg d)

/-- The protected set of vertex `i`: that of the last decoration of its occurrence. -/
def P : ℕ → Set (Pt d) := Pof c.occ

/-- The parent in the static forest (the parent scan of §8.3.2). -/
noncomputable def par : ℕ → Option ℕ := scanParent c.strict c.lab c.P

/-- The board containing a point. -/
noncomputable def boardOf (x : Pt d) : Rect d :=
  if hx : ∃ C ∈ c.Pb, x ∈ C.pts then Classical.choose hx else Rect.mk x x le_rfl

/-- The hypotheses on the forest datum. -/
structure Good : Prop where
  occ_ne : ∀ i : ℕ, (i : ℕ∞) < c.N → c.occ i ≠ []
  last_L : ∀ i : ℕ, (i : ℕ∞) < c.N → (lastOf (c.occ i)).L = c.lab i
  occ_par : ∀ j : ℕ, (j : ℕ∞) < c.N → ∀ p, c.par j = some p → ∃ w, c.occ j = c.occ p ++ [w]
  path_ok : ∀ i : ℕ, (i : ℕ∞) < c.N → ∀ p, p ≠ [] → p <+: c.occ i → PathOK c.h c.qd p
  P_sub : ∀ i : ℕ, (i : ℕ∞) < c.N → c.P i ⊆ c.lab i
  lab_inf : ∀ i : ℕ, (i : ℕ∞) < c.N → (c.lab i).Infinite
  inj : c.strict = true → ∀ i j : ℕ, (i : ℕ∞) < c.N → (j : ℕ∞) < c.N → c.lab i = c.lab j → i = j

/-! ### The board games -/

/-- Quotas of the levels of a path. -/
def qsf (p : List (Deco d)) : Fin (p.length - 1 + 1) → ℝ := fun i => c.qd (dat p i)

end Cfg

/-- The rectangles inside a board are finitely many. -/
theorem rects_in_finite (C : Rect d) (φ : Rect d → Prop) :
    {R : Rect d | R.pts ⊆ C.pts ∧ φ R}.Finite := by
  have hfin : (C.pts ×ˢ C.pts).Finite := (BasicAux.rect_pts_finite C).prod (BasicAux.rect_pts_finite C)
  refine (hfin.preimage (f := fun R : Rect d => (R.lo, R.hi)) ?_).subset ?_
  · rintro ⟨lo, hi, hle⟩ - ⟨lo', hi', hle'⟩ - h
    simp only [Rect.lo, Rect.hi, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · rintro R ⟨hR, -⟩
    exact ⟨hR (Set.left_mem_Icc.2 R.le), hR (Set.right_mem_Icc.2 R.le)⟩

/-- The rectangles inside a board satisfying `φ`, as a finset. -/
noncomputable def rectsIn (C : Rect d) (φ : Rect d → Prop) : Finset (Rect d) :=
  (rects_in_finite C φ).toFinset

theorem mem_rectsIn {C : Rect d} {φ : Rect d → Prop} {R : Rect d} :
    R ∈ rectsIn C φ ↔ R.pts ⊆ C.pts ∧ φ R := by
  simp [rectsIn]

/-- The initialization round of board `C`: its first input visit if one exists, and `0`
if the input sequence never visits `C`. -/
noncomputable def t0 (x : ℕ → Pt d) (C : Rect d) : ℕ :=
  if h : ∃ s, x s ∈ C.pts then Nat.find h else 0

namespace Cfg
variable (c : Cfg d)

/-- The rectangle families of the board game: at level `i`, all rectangles inside `C` meeting the
cutoff of level `i`. -/
noncomputable def rectsf (p : List (Deco d)) (C : Rect d) :
    Fin (p.length - 1 + 1) → Finset (Rect d) :=
  fun i => rectsIn C (fun R => ssf p i * c.h R.vol ≤ mass (Lsf p i) R)

/-- The finite stopping game of the board `C` with retained path `p`. -/
noncomputable def game (p : List (Deco d)) (C : Rect d) : StopGame d :=
  packetGame (Lsf p) (c.qsf p) (c.rectsf p C)

/-- The stored winning strategy (any strategy if the game is not feasible). -/
noncomputable def strat (p : List (Deco d)) (C : Rect d) : WStrategy d :=
  if hf : (c.game p C).Feasible then Classical.choose hf else fun _ => none

/-! ### The online quantities, as functions of the input sequence -/

/-- The current guess `Q_t`. -/
noncomputable def Q (x : ℕ → Pt d) (t : ℕ) : Option ℕ := guess c.N c.lab x t

/-- The greatest eligible index whose radius box misses `C`, with `Nat.findGreatest`
defaulting to `0` if no index qualifies (including an empty occurrence). The subsequent
`bpath` definition tests disjointness again before retaining the path. -/
noncomputable def cut (u : ℕ) (C : Rect d) : ℕ :=
  Nat.findGreatest (fun i => Disjoint C.pts (core d (dat (c.occ u) i).a)) ((c.occ u).length - 1)

/-- The retained path of board `C` (`none`: the board is fallback-only). -/
noncomputable def bpath (x : ℕ → Pt d) (C : Rect d) : Option (List (Deco d)) :=
  match c.Q x (t0 x C) with
  | none => none
  | some u =>
    if Disjoint C.pts (core d (dat (c.occ u) (c.cut u C)).a) then
      some ((c.occ u).take (c.cut u C + 1))
    else none

/-- The greatest index whose nonempty prefix of `p` is a prefix of the current guessed
occurrence. `Nat.findGreatest` returns `0` when there is no qualifying index, including
a missing guess or no common nonempty prefix. A common-ancestor interpretation requires
the relevant path invariants. -/
noncomputable def lca (x : ℕ → Pt d) (p : List (Deco d)) (t : ℕ) : ℕ :=
  Nat.findGreatest (fun i => ∃ u, c.Q x t = some u ∧ p.take (i + 1) <+: c.occ u) (p.length - 1)

/-- The pullback level `k` rounds after initialization. -/
noncomputable def levK (x : ℕ → Pt d) (p : List (Deco d)) (t₀ : ℕ) : ℕ → ℕ
  | 0 => p.length - 1
  | k + 1 => min (levK x p t₀ k) (c.lca x p (t₀ + k + 1))

/-- The pullback level at round `t`. -/
noncomputable def lev (x : ℕ → Pt d) (p : List (Deco d)) (t₀ t : ℕ) : ℕ := c.levK x p t₀ (t - t₀)

/-- The reply of the simulated game of board `C` at round `t`. -/
noncomputable def simOut (x : ℕ → Pt d) (C : Rect d) (t : ℕ) : Option (Pt d) :=
  match c.bpath x C with
  | none => none
  | some p => (simRun (c.game p C) (c.strat p C) x (c.lev x p (t0 x C)) (t0 x C)
      (t - t0 x C + 1)).2.2

end Cfg

/-- A point of `L` outside `S` (when one exists). -/
noncomputable def freshIn (L S : Set (Pt d)) : Pt d :=
  if h : ∃ y ∈ L, y ∉ S then Classical.choose h else 0

theorem freshIn_spec {L S : Set (Pt d)} (hL : L.Infinite) (hS : S.Finite) :
    freshIn L S ∈ L ∧ freshIn L S ∉ S := by
  have h : ∃ y ∈ L, y ∉ S := by
    by_contra hn
    push Not at hn
    exact hL (hS.subset hn)
  unfold freshIn
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- The points used before the output of round `t`: the inputs up to `t` and the earlier outputs. -/
def usedSet (x : ℕ → Pt d) (t : ℕ) (prev : List (Pt d)) : Set (Pt d) :=
  {p | ∃ i ≤ t, x i = p} ∪ {p | p ∈ prev}

theorem usedSet_finite (x : ℕ → Pt d) (t : ℕ) (prev : List (Pt d)) : (usedSet x t prev).Finite := by
  refine Set.Finite.union ?_ prev.finite_toSet
  exact ((Set.finite_le_nat t).image x).subset (by rintro p ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩)

namespace Cfg
variable (c : Cfg d)

/-- The language of the fallback outputs at round `t`. -/
noncomputable def fbLang (x : ℕ → Pt d) (t : ℕ) : Set (Pt d) :=
  match c.Q x t with
  | none => univ
  | some u => c.lab u

/-- The output of round `t`, given the earlier outputs `prev`. -/
noncomputable def step (x : ℕ → Pt d) (t : ℕ) (prev : List (Pt d)) : Pt d :=
  match c.simOut x (c.boardOf (x t)) t with
  | some y => if y ∉ usedSet x t prev then y else freshIn (c.fbLang x t) (usedSet x t prev)
  | none => freshIn (c.fbLang x t) (usedSet x t prev)

/-- The outputs of rounds `0, …, t-1`. -/
noncomputable def outs (x : ℕ → Pt d) : ℕ → List (Pt d)
  | 0 => []
  | t + 1 => outs x t ++ [c.step x t (outs x t)]

/-- The output of round `t` on the input sequence `x`. -/
noncomputable def Y (x : ℕ → Pt d) (t : ℕ) : Pt d := c.step x t (c.outs x t)

/-- **The generator.** -/
noncomputable def gen : Generator (Pt d) := fun l => c.Y (fun i => l.getD i 0) (l.length - 1)

end Cfg


/-! ## Basic facts: the parent scan, guesses, initialization -/

/-- The parent returned by the scan is a possible parent. -/
theorem scanParent_spec {strict : Bool} {lab P : ℕ → Set (Pt d)} {j p : ℕ}
    (h : scanParent strict lab P j = some p) : PossibleParent strict lab P p j := by
  have key : ∀ k, ∀ p, (List.range k).foldl (fun acc i =>
      if PossibleParent strict lab P i j then
        match acc with
        | none => some i
        | some p => if lab i ⊆ lab p then some i else some p
      else acc) none = some p → PossibleParent strict lab P p j := by
    intro k
    induction k with
    | zero => intro p hp; simp at hp
    | succ k ih =>
      intro p hp
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at hp
      split_ifs at hp with hk
      · rcases hA : (List.range k).foldl (fun acc i =>
            if PossibleParent strict lab P i j then
              match acc with
              | none => some i
              | some p => if lab i ⊆ lab p then some i else some p
            else acc) none with _ | p'
        · rw [hA] at hp; cases hp; exact hk
        · rw [hA] at hp
          simp only at hp
          split_ifs at hp
          · cases hp; exact hk
          · cases hp; exact ih _ hA
      · exact ih p hp
  exact key j p h

/-- A successful guess is a vertex `< N` containing every input so far. This statement
does not assert the minimality or other conditions of the separate `Critical` predicate. -/
theorem guess_spec {N : ℕ∞} {lab : ℕ → Set (Pt d)} {w : ℕ → Pt d} {t v : ℕ}
    (h : guess N lab w t = some v) : (v : ℕ∞) < N ∧ {x | x ∈ inputsUpTo w t} ⊆ lab v := by
  unfold guess at h
  simp only at h
  split_ifs at h with hex
  obtain ⟨i, hi, hc⟩ := hex
  cases h
  exact ⟨(Nat.findGreatest_spec hi hc).1, (Nat.findGreatest_spec hi hc).2.1⟩

theorem inputsUpTo_congr {x x' : ℕ → Pt d} {t : ℕ} (hag : ∀ i ≤ t, x i = x' i) :
    inputsUpTo x t = inputsUpTo x' t := by
  unfold inputsUpTo
  congr 1
  funext i
  exact hag i (by omega)

theorem guess_congr {N : ℕ∞} {lab : ℕ → Set (Pt d)} {x x' : ℕ → Pt d} {t : ℕ}
    (hag : ∀ i ≤ t, x i = x' i) : guess N lab x t = guess N lab x' t := by
  unfold guess
  rw [inputsUpTo_congr hag]

/-- The initialization round of a board that receives the input of round `t`. -/
theorem t0_spec {x : ℕ → Pt d} {C : Rect d} {t : ℕ} (ht : x t ∈ C.pts) :
    t0 x C ≤ t ∧ x (t0 x C) ∈ C.pts ∧ ∀ s < t0 x C, x s ∉ C.pts := by
  have h : ∃ s, x s ∈ C.pts := ⟨t, ht⟩
  unfold t0
  rw [dif_pos h]
  exact ⟨Nat.find_min' h ht, Nat.find_spec h, fun s hs => Nat.find_min h hs⟩

theorem t0_congr {x x' : ℕ → Pt d} {C : Rect d} {t : ℕ} (ht : x t ∈ C.pts)
    (hag : ∀ i ≤ t, x i = x' i) : t0 x C = t0 x' C := by
  have ht' : x' t ∈ C.pts := hag t le_rfl ▸ ht
  obtain ⟨h1, h2, h3⟩ := t0_spec ht
  obtain ⟨h1', h2', h3'⟩ := t0_spec ht'
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    exact h3 _ hlt (by rw [hag _ (by omega)]; exact h2')
  · by_contra hlt
    push Not at hlt
    exact h3' _ hlt (by rw [← hag _ (by omega)]; exact h2)

/-- `simRun` depends only on the inputs and pullback levels of its rounds. -/
theorem simRun_congr (S : StopGame d) (σ : WStrategy d) {x x' : ℕ → Pt d} {lev lev' : ℕ → ℕ}
    (t₀ : ℕ) : ∀ k, (∀ j < k, x (t₀ + j) = x' (t₀ + j) ∧ lev (t₀ + j) = lev' (t₀ + j)) →
      simRun S σ x lev t₀ k = simRun S σ x' lev' t₀ k
  | 0, _ => rfl
  | k + 1, h => by
    simp only [simRun]
    rw [simRun_congr S σ t₀ k (fun j hj => h j (by omega)), (h k (by omega)).1, (h k (by omega)).2]

namespace Cfg
variable (c : Cfg d)

theorem Q_congr {x x' : ℕ → Pt d} {t : ℕ} (hag : ∀ i ≤ t, x i = x' i) : c.Q x t = c.Q x' t :=
  guess_congr hag

theorem bpath_congr {x x' : ℕ → Pt d} {C : Rect d} {t : ℕ} (ht : x t ∈ C.pts)
    (hag : ∀ i ≤ t, x i = x' i) : c.bpath x C = c.bpath x' C := by
  have h0 := t0_congr ht hag
  have h1 := (t0_spec ht).1
  unfold bpath
  rw [← h0, c.Q_congr (fun i hi => hag i (by omega))]

theorem lca_congr {x x' : ℕ → Pt d} (p : List (Deco d)) {t : ℕ} (hag : ∀ i ≤ t, x i = x' i) :
    c.lca x p t = c.lca x' p t := by
  unfold lca
  rw [c.Q_congr hag]

theorem levK_congr {x x' : ℕ → Pt d} (p : List (Deco d)) (t₀ : ℕ) {t : ℕ}
    (hag : ∀ i ≤ t, x i = x' i) : ∀ k, t₀ + k ≤ t → c.levK x p t₀ k = c.levK x' p t₀ k
  | 0, _ => rfl
  | k + 1, hk => by
    simp only [levK]
    rw [levK_congr p t₀ hag k (by omega), c.lca_congr p (fun i hi => hag i (by omega))]

theorem lev_congr {x x' : ℕ → Pt d} (p : List (Deco d)) (t₀ : ℕ) {t s : ℕ}
    (hag : ∀ i ≤ t, x i = x' i) (hs : s ≤ t) : c.lev x p t₀ s = c.lev x' p t₀ s := by
  unfold lev
  rcases le_or_gt t₀ s with h | h
  · exact c.levK_congr p t₀ hag _ (by omega)
  · rw [show s - t₀ = 0 by omega]; rfl

theorem simOut_congr {x x' : ℕ → Pt d} {C : Rect d} {t : ℕ} (ht : x t ∈ C.pts)
    (hag : ∀ i ≤ t, x i = x' i) : c.simOut x C t = c.simOut x' C t := by
  have h0 := t0_congr ht hag
  have h1 := (t0_spec ht).1
  have h1' : t0 x' C ≤ t := h0 ▸ h1
  unfold simOut
  rw [c.bpath_congr ht hag, ← h0]
  rcases c.bpath x' C with _ | p
  · rfl
  · simp only
    rw [simRun_congr _ _ _ _ fun j hj => ⟨hag _ (by omega), c.lev_congr p _ hag (by omega)⟩]

/-! ## The outputs -/

theorem outs_length (x : ℕ → Pt d) : ∀ t, (c.outs x t).length = t
  | 0 => rfl
  | t + 1 => by simp [outs, outs_length x t]

theorem outs_getElem (x : ℕ → Pt d) : ∀ t i (hi : i < (c.outs x t).length), (c.outs x t)[i] = c.Y x i
  | 0, i, hi => by simp [outs] at hi
  | t + 1, i, hi => by
    have hl2 := c.outs_length x (t + 1)
    rw [hl2] at hi
    simp only [outs]
    have hl := c.outs_length x t
    rcases Nat.lt_or_ge i t with h | h
    · rw [List.getElem_append_left (by omega)]
      exact outs_getElem x t i (by omega)
    · have : i = t := by omega
      subst this
      rw [List.getElem_append_right (by omega)]
      simp [hl, Y]

theorem mem_outs (x : ℕ → Pt d) (t : ℕ) (p : Pt d) : p ∈ c.outs x t ↔ ∃ s < t, c.Y x s = p := by
  constructor
  · intro hp
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    exact ⟨i, by rwa [c.outs_length] at hi, (c.outs_getElem x t i hi).symm⟩
  · rintro ⟨s, hs, rfl⟩
    have hi : s < (c.outs x t).length := by rw [c.outs_length]; exact hs
    rw [← c.outs_getElem x t s hi]
    exact List.getElem_mem _

theorem usedSet_outs (x : ℕ → Pt d) (t : ℕ) :
    usedSet x t (c.outs x t) = {p | ∃ i ≤ t, x i = p} ∪ {p | ∃ s < t, c.Y x s = p} := by
  ext p
  simp only [usedSet, mem_union, mem_setOf_eq, c.mem_outs]

/-- Every point lies in its board (in the fallback case, the one-point rectangle). -/
theorem boardOf_mem (x : Pt d) : x ∈ (c.boardOf x).pts := by
  unfold boardOf
  split_ifs with h
  · exact (Classical.choose_spec h).2
  · exact ⟨le_rfl, le_rfl⟩

/-- When the boards cover the space, the board of a point is a board of `Pb` containing it.
(It is the only one when the boards are disjoint: `boardOf_eq`.) -/
theorem boardOf_spec (hcov : ∀ x : Pt d, ∃ C ∈ c.Pb, x ∈ C.pts) (x : Pt d) :
    c.boardOf x ∈ c.Pb ∧ x ∈ (c.boardOf x).pts := by
  have h := hcov x
  unfold boardOf
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem boardOf_eq (hcov : ∀ x : Pt d, ∃ C ∈ c.Pb, x ∈ C.pts)
    (hdisj : ∀ C ∈ c.Pb, ∀ C' ∈ c.Pb, C ≠ C' → Disjoint C.pts C'.pts) {x : Pt d} {C : Rect d}
    (hC : C ∈ c.Pb) (hx : x ∈ C.pts) : c.boardOf x = C := by
  obtain ⟨h1, h2⟩ := c.boardOf_spec hcov x
  by_contra hne
  exact Set.disjoint_left.1 (hdisj _ h1 _ hC hne) h2 hx

/-- Causality of the outputs. -/
theorem Y_congr {x x' : ℕ → Pt d} :
    ∀ t, (∀ i ≤ t, x i = x' i) → c.Y x t = c.Y x' t ∧ c.outs x t = c.outs x' t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro hag
    have houts : c.outs x t = c.outs x' t := by
      cases t with
      | zero => rfl
      | succ t =>
        obtain ⟨h1, h2⟩ := ih t (by omega) (fun i hi => hag i (by omega))
        show c.outs x t ++ [c.Y x t] = c.outs x' t ++ [c.Y x' t]
        rw [h1, h2]
    refine ⟨?_, houts⟩
    unfold Y step
    have hb : c.boardOf (x t) = c.boardOf (x' t) := by rw [hag t le_rfl]
    have hx := c.boardOf_mem (x t)
    have hu : usedSet x t (c.outs x t) = usedSet x' t (c.outs x' t) := by
      unfold usedSet
      rw [houts]
      congr 1
      ext p
      simp only [mem_setOf_eq]
      constructor
      · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, (hag i hi).symm⟩
      · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, hag i hi⟩
    have hf : c.fbLang x t = c.fbLang x' t := by
      unfold fbLang
      rw [c.Q_congr hag]
    rw [← hb, c.simOut_congr hx hag, hu, hf]

/-- The generator's output on a sequence is `Y`. -/
theorem gen_out (w : ℕ → Pt d) (t : ℕ) :
    c.gen.out w t = c.Y w t := by
  unfold Generator.out gen
  have hlen : (inputsUpTo w t).length = t + 1 := by simp [inputsUpTo]
  rw [hlen, Nat.add_sub_cancel]
  refine (c.Y_congr t fun i hi => ?_).1
  rw [List.getD_eq_getElem _ _ (by omega)]
  simp only [inputsUpTo, List.getElem_ofFn]

theorem gen_outputSet (w : ℕ → Pt d) :
    c.gen.outputSet w = range (c.Y w) := by
  unfold Generator.outputSet
  congr 1
  funext t
  exact c.gen_out w t

/-- The fallback language is infinite. -/
theorem fbLang_infinite (hd : 1 ≤ d) (hc : c.Good) (x : ℕ → Pt d) (t : ℕ) :
    (c.fbLang x t).Infinite := by
  unfold fbLang
  rcases hQ : c.Q x t with _ | u
  · simp only
    have hinj : Function.Injective (fun n : ℕ => (fun _ : Fin d => (n : ℤ))) := by
      intro m n hmn
      have := congrFun hmn ⟨0, by omega⟩
      simpa using this
    exact (Set.infinite_range_of_injective hinj).mono (subset_univ _)
  · simp only
    exact hc.lab_inf u (guess_spec hQ).1

/-- Freshness of the constructed generator; the sequence-coordinate form below is derived
through `gen_out`. This is the single freshness obligation. -/
theorem gen_fresh (hd : 1 ≤ d) (hc : c.Good) : c.gen.Fresh := by
  intro w t
  simp only [c.gen_out]
  have h : c.Y w t ∉ usedSet w t (c.outs w t) := by
    unfold Y step
    have hfb := freshIn_spec (c.fbLang_infinite hd hc w t) (usedSet_finite w t (c.outs w t))
    rcases c.simOut w (c.boardOf (w t)) t with _ | y
    · exact hfb.2
    · simp only
      split_ifs with h <;> first | exact h | exact hfb.2
  rw [c.usedSet_outs] at h
  simp only [mem_union, mem_setOf_eq, not_or, not_exists, not_and] at h
  exact ⟨h.1, h.2⟩

/-- **Freshness** of the outputs (`hfresh` of Lemma 8.12), the sequence-coordinate convenience
form of `gen_fresh`: no input up to `t` or earlier output equals the output at `t`. -/
theorem hfresh_of (hd : 1 ≤ d) (hc : c.Good) (w : ℕ → Pt d) :
    ∀ t, (∀ i ≤ t, w i ≠ c.Y w t) ∧ ∀ i < t, c.Y w i ≠ c.Y w t := by
  intro t
  simpa only [c.gen_out] using c.gen_fresh hd hc w t

end Cfg


/-! ## Paths, ancestors, levels -/

/-- Labels along a usable path are nonincreasing. -/
theorem PathOK.L_anti {h : ℕ → ℝ} {qd : Deco d → ℝ} {p : List (Deco d)} (hp : PathOK h qd p)
    {i j : ℕ} (hij : i ≤ j) (hj : j < p.length) : (dat p j).L ⊆ (dat p i).L := by
  have := hp.2.1 (show (⟨i, by omega⟩ : Fin (p.length - 1 + 1)) ≤ ⟨j, by omega⟩ from
    Fin.mk_le_mk.2 hij)
  exact this

/-- Every label of a usable path contains the last label. -/
theorem PathOK.last_sub {h : ℕ → ℝ} {qd : Deco d → ℝ} {p : List (Deco d)} (hp : PathOK h qd p)
    {i : ℕ} (hi : i < p.length) : (lastOf p).L ⊆ (dat p i).L := by
  rw [lastOf_eq_dat p hp.1]
  exact hp.L_anti (by omega) (by have := List.length_pos_iff.mpr hp.1; omega)

namespace Cfg
variable {c : Cfg d}

/-- The occurrence of an ancestor is a prefix of the occurrence of its descendant. -/
theorem anc_prefix (hc : c.Good) {a v : ℕ} (h : IsAncestor c.par a v) :
    (v : ℕ∞) < c.N → c.occ a <+: c.occ v := by
  induction h with
  | refl => intro _; exact List.prefix_refl _
  | @step u v _ hpv ih =>
    intro hv
    have hu : (u : ℕ∞) < c.N := lt_of_le_of_lt (by exact_mod_cast (scanParent_spec hpv).1.le) hv
    obtain ⟨w, hw⟩ := hc.occ_par v hv u hpv
    exact (ih hu).trans ⟨[w], hw.symm⟩

/-- Labels shrink from an ancestor to a descendant. -/
theorem lab_sub_of_prefix (hc : c.Good) {a v : ℕ} (ha : (a : ℕ∞) < c.N) (hv : (v : ℕ∞) < c.N)
    (h : c.occ a <+: c.occ v) : c.lab v ⊆ c.lab a := by
  have hpv := hc.path_ok v hv (c.occ v) (hc.occ_ne v hv) (List.prefix_refl _)
  have hne := hc.occ_ne a ha
  rw [← hc.last_L v hv, ← hc.last_L a ha, lastOf_eq_dat _ hne,
    dat_of_prefix h _ (by have := List.length_pos_iff.mpr hne; omega)]
  exact hpv.last_sub (by have := h.length_le; have := List.length_pos_iff.mpr hne; omega)

end Cfg

/-! ## The board games: generic simulation facts -/

section Sim
variable {S : StopGame d} {σ : WStrategy d}

theorem simStep_free (ms : List (BMove d)) (lvl : Fin (S.r + 1)) (b w : Set (Pt d)) (ℓ : ℕ)
    (x : Pt d) (hfree : S.Free ⟨⟨min ℓ lvl.val, by omega⟩, b, w⟩ x) :
    simStep S σ ms ⟨lvl, b, w⟩ ℓ x =
      (ms ++ List.replicate (lvl.val - min ℓ lvl.val) BMove.down ++ [BMove.claim x],
        S.afterClaim ⟨⟨min ℓ lvl.val, by omega⟩, b, w⟩ x
          (σ (ms ++ List.replicate (lvl.val - min ℓ lvl.val) BMove.down ++ [BMove.claim x])),
        σ (ms ++ List.replicate (lvl.val - min ℓ lvl.val) BMove.down ++ [BMove.claim x])) := by
  dsimp only [simStep, StopGame.State.level, StopGame.State.black, StopGame.State.white]
  exact if_pos hfree

theorem simStep_nfree (ms : List (BMove d)) (lvl : Fin (S.r + 1)) (b w : Set (Pt d)) (ℓ : ℕ)
    (x : Pt d) (hfree : ¬ S.Free ⟨⟨min ℓ lvl.val, by omega⟩, b, w⟩ x) :
    simStep S σ ms ⟨lvl, b, w⟩ ℓ x =
      (ms ++ List.replicate (lvl.val - min ℓ lvl.val) BMove.down,
        ⟨⟨min ℓ lvl.val, by omega⟩, b, w⟩, none) := by
  dsimp only [simStep, StopGame.State.level, StopGame.State.black, StopGame.State.white]
  exact if_neg hfree

theorem simRun_succ (x : ℕ → Pt d) (lev : ℕ → ℕ) (t₀ k : ℕ) :
    simRun S σ x lev t₀ (k + 1) =
      simStep S σ (simRun S σ x lev t₀ k).1 (simRun S σ x lev t₀ k).2.1 (lev (t₀ + k)) (x (t₀ + k)) :=
  rfl

/-- The simulated play is always legal for a winning strategy. -/
theorem sim_reach (hσ : S.Wins σ) (x : ℕ → Pt d) (lev : ℕ → ℕ) (t₀ : ℕ) :
    ∀ k, S.Reach σ (simRun S σ x lev t₀ k).1 (simRun S σ x lev t₀ k).2.1
  | 0 => StopGame.Reach.nil
  | k + 1 => by
    have hR := sim_reach hσ x lev t₀ k
    rw [simRun_succ]
    rcases hp : simRun S σ x lev t₀ k with ⟨ms, ⟨lvl, b, w⟩, o⟩
    rw [hp] at hR
    simp only
    have hdown := ForestAux.reach_downs hR (lvl.val - min (lev (t₀ + k)) lvl.val)
      (min (lev (t₀ + k)) lvl.val) (by omega)
    by_cases hfree : S.Free ⟨⟨min (lev (t₀ + k)) lvl.val, by omega⟩, b, w⟩ (x (t₀ + k))
    · rw [simStep_free _ _ _ _ _ _ hfree]
      exact StopGame.Reach.claim hdown hfree ((hσ _ _ hdown).1 _ hfree)
    · rw [simStep_nfree _ _ _ _ _ _ hfree]
      exact hdown

/-- The level after a round is the minimum of the previous level and the pullback level. -/
theorem sim_level (x : ℕ → Pt d) (lev : ℕ → ℕ) (t₀ k : ℕ) :
    (simRun S σ x lev t₀ (k + 1)).2.1.level.val =
      min (lev (t₀ + k)) (simRun S σ x lev t₀ k).2.1.level.val := by
  rw [simRun_succ]
  rcases simRun S σ x lev t₀ k with ⟨ms, ⟨lvl, b, w⟩, o⟩
  simp only
  by_cases hfree : S.Free ⟨⟨min (lev (t₀ + k)) lvl.val, by omega⟩, b, w⟩ (x (t₀ + k))
  · rw [simStep_free _ _ _ _ _ _ hfree]; rfl
  · rw [simStep_nfree _ _ _ _ _ _ hfree]; rfl

theorem sim_level_ge (x : ℕ → Pt d) (lev : ℕ → ℕ) (t₀ m : ℕ) (hm : m ≤ S.r) :
    ∀ k, (∀ j < k, m ≤ lev (t₀ + j)) → m ≤ (simRun S σ x lev t₀ k).2.1.level.val
  | 0, _ => by simp [simRun, StopGame.init, StopGame.State.level]; exact hm
  | k + 1, h => by
    rw [sim_level]
    exact le_min (h k (by omega)) (sim_level_ge x lev t₀ m hm k fun j hj => h j (by omega))

/-- A reply of the simulation: the input of that round is visible at the level after the round. -/
theorem sim_reply_input (x : ℕ → Pt d) (lev : ℕ → ℕ) (t₀ k : ℕ) {y : Pt d}
    (h : (simRun S σ x lev t₀ (k + 1)).2.2 = some y) :
    x (t₀ + k) ∈ S.visible (simRun S σ x lev t₀ (k + 1)).2.1.level := by
  rw [simRun_succ] at h ⊢
  rcases hp : simRun S σ x lev t₀ k with ⟨ms, ⟨lvl, b, w⟩, o⟩
  rw [hp] at h
  simp only at h ⊢
  by_cases hfree : S.Free ⟨⟨min (lev (t₀ + k)) lvl.val, by omega⟩, b, w⟩ (x (t₀ + k))
  · rw [simStep_free _ _ _ _ _ _ hfree]; exact hfree.1
  · rw [simStep_nfree _ _ _ _ _ _ hfree] at h; cases h

/-- A reply of the simulation is visible at the level after the round. -/
theorem sim_reply_vis (hσ : S.Wins σ) (x : ℕ → Pt d) (lev : ℕ → ℕ) (t₀ k : ℕ) {y : Pt d}
    (h : (simRun S σ x lev t₀ (k + 1)).2.2 = some y) :
    y ∈ S.visible (simRun S σ x lev t₀ (k + 1)).2.1.level := by
  have hR := sim_reach hσ x lev t₀ k
  rw [simRun_succ] at h ⊢
  rcases hp : simRun S σ x lev t₀ k with ⟨ms, ⟨lvl, b, w⟩, o⟩
  rw [hp] at hR h
  simp only at h ⊢
  have hdown := ForestAux.reach_downs hR (lvl.val - min (lev (t₀ + k)) lvl.val)
    (min (lev (t₀ + k)) lvl.val) (by omega)
  by_cases hfree : S.Free ⟨⟨min (lev (t₀ + k)) lvl.val, by omega⟩, b, w⟩ (x (t₀ + k))
  · rw [simStep_free _ _ _ _ _ _ hfree] at h ⊢
    have hleg := (hσ _ _ hdown).1 _ hfree
    simp only at h
    rw [h] at hleg
    exact hleg.1
  · rw [simStep_nfree _ _ _ _ _ _ hfree] at h; cases h

end Sim

/-! ## Board games of the construction -/

namespace Cfg
variable {c : Cfg d}

theorem support_sub (p : List (Deco d)) (C : Rect d) :
    packetSupport (Lsf p) (c.rectsf p C) ⊆ C.pts := by
  intro y hy
  simp only [packetSupport, mem_iUnion] at hy
  obtain ⟨i, R, hR, hy⟩ := hy
  exact (mem_rectsIn.1 hR).1 hy.2

theorem t0_min {x : ℕ → Pt d} {C : Rect d} {t : ℕ} (ht : t < t0 x C) : x t ∉ C.pts := by
  intro hx
  exact absurd (t0_spec hx).1 (by omega)

/-- The retained path of a board. -/
theorem bpath_spec {x : ℕ → Pt d} {C : Rect d} {p : List (Deco d)} (h : c.bpath x C = some p) :
    ∃ u, c.Q x (t0 x C) = some u ∧ p = (c.occ u).take (c.cut u C + 1) ∧
      Disjoint C.pts (core d (dat (c.occ u) (c.cut u C)).a) := by
  unfold bpath at h
  rcases hQ : c.Q x (t0 x C) with _ | u
  · rw [hQ] at h; cases h
  · rw [hQ] at h
    simp only at h
    split_ifs at h with hd
    cases h
    exact ⟨u, rfl, rfl, hd⟩

theorem cut_le (u : ℕ) (C : Rect d) : c.cut u C ≤ (c.occ u).length - 1 := Nat.findGreatest_le _

/-- The retained path is a usable path. -/
theorem bpath_ok (hc : c.Good) {x : ℕ → Pt d} {C : Rect d} {p : List (Deco d)}
    (h : c.bpath x C = some p) :
    ∃ u, c.Q x (t0 x C) = some u ∧ (u : ℕ∞) < c.N ∧ p <+: c.occ u ∧ PathOK c.h c.qd p ∧
      Disjoint C.pts (core d (lastOf p).a) := by
  obtain ⟨u, hQ, rfl, hd⟩ := bpath_spec h
  have hu := (guess_spec hQ).1
  have hne := hc.occ_ne u hu
  have hlen := List.length_pos_iff.mpr hne
  have hcut := cut_le (c := c) u C
  have hpne : (c.occ u).take (c.cut u C + 1) ≠ [] := by
    intro he
    rw [List.take_eq_nil_iff] at he
    rcases he with he | he
    · omega
    · exact hne he
  have hlast : lastOf ((c.occ u).take (c.cut u C + 1)) = dat (c.occ u) (c.cut u C) := by
    rw [lastOf, CharAux.getLastD_take _ _ _ (by omega),
      dat_eq (q := c.occ u) (j := c.cut u C) (by omega)]
  refine ⟨u, hQ, hu, List.take_prefix _ _, hc.path_ok u hu _ hpne (List.take_prefix _ _), ?_⟩
  rw [hlast]; exact hd

/-- The stored strategy of a board with a retained path wins its game. -/
theorem strat_wins (hc : c.Good) {x : ℕ → Pt d} {C : Rect d} {p : List (Deco d)}
    (h : c.bpath x C = some p) : (c.game p C).Wins (c.strat p C) := by
  obtain ⟨u, -, -, -, hok, hd⟩ := bpath_ok hc h
  have hfeas : (c.game p C).Feasible := by
    refine hok.2.2 (c.rectsf p C) fun i R hR => ?_
    obtain ⟨hRC, hcut⟩ := mem_rectsIn.1 hR
    exact ⟨Set.disjoint_of_subset_left hRC hd, hcut⟩
  unfold strat
  rw [dif_pos hfeas]
  exact Classical.choose_spec hfeas

/-- **Item 4 of the simulation** (`hout` of Lemma 8.12): a fresh reply of the stored strategy is
the actual output. -/
theorem hout_of (hcov : ∀ x : Pt d, ∃ C ∈ c.Pb, x ∈ C.pts)
    (hdisj : ∀ C ∈ c.Pb, ∀ C' ∈ c.Pb, C ≠ C' → Disjoint C.pts C'.pts) {w : ℕ → Pt d}
    {C : Rect d} (hC : C ∈ c.Pb) {p : List (Deco d)} (hb : c.bpath w C = some p) :
    ∀ k y', (simRun (c.game p C) (c.strat p C) w (c.lev w p (t0 w C)) (t0 w C) (k + 1)).2.2 =
        some y' → (∀ i ≤ t0 w C + k, w i ≠ y') → (∀ i < t0 w C + k, c.Y w i ≠ y') →
        c.Y w (t0 w C + k) = y' := by
  intro k y' hy h1 h2
  have hin := sim_reply_input _ _ _ _ hy
  have hwC : w (t0 w C + k) ∈ C.pts := support_sub p C hin.1
  have hbo : c.boardOf (w (t0 w C + k)) = C := c.boardOf_eq hcov hdisj hC hwC
  have hsim : c.simOut w C (t0 w C + k) = some y' := by
    unfold simOut
    rw [hb]
    simp only
    rw [show t0 w C + k - t0 w C + 1 = k + 1 by omega]
    exact hy
  have hnu : y' ∉ usedSet w (t0 w C + k) (c.outs w (t0 w C + k)) := by
    rw [c.usedSet_outs]
    simp only [mem_union, mem_setOf_eq, not_or, not_exists, not_and]
    exact ⟨h1, h2⟩
  unfold Y step
  rw [hbo, hsim]
  simp only
  rw [if_pos hnu]

end Cfg


/-! ## A fixed target: the boards that are initialized late and miss the core -/

theorem exists_bound {w : ℕ → Pt d} {A : Set (Pt d)} (hA : A.Finite)
    (hw : ∀ p ∈ A, ∃ s, w s = p) : ∃ M, ∀ p ∈ A, ∃ s ≤ M, w s = p := by
  let sf : Pt d → ℕ := fun p => if h : ∃ s, w s = p then Nat.find h else 0
  refine ⟨hA.toFinset.sup sf, fun p hp => ⟨sf p, Finset.le_sup (hA.mem_toFinset.2 hp), ?_⟩⟩
  have h := hw p hp
  simp only [sf, dif_pos h]
  exact Nat.find_spec h

theorem core_finite (a : ℝ) : (core d a).Finite := by
  refine (Set.finite_Icc (fun _ : Fin d => -(⌈a⌉₊ : ℤ)) (fun _ => (⌈a⌉₊ : ℤ))).subset ?_
  intro x hx
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have h1 := (abs_le.1 (hx i)).1
    have h2 : a ≤ (⌈a⌉₊ : ℝ) := Nat.le_ceil a
    have : (-(⌈a⌉₊ : ℤ) : ℝ) ≤ (x i : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · have h1 := (abs_le.1 (hx i)).2
    have h2 : a ≤ (⌈a⌉₊ : ℝ) := Nat.le_ceil a
    have : (x i : ℝ) ≤ ((⌈a⌉₊ : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this

namespace Cfg
variable {c : Cfg d}

section Target
variable (hc : c.Good) {z : ℕ} (hz : (z : ℕ∞) < c.N) {w : ℕ → Pt d} {T : ℕ}
  (hT : ∀ t ≥ T, ∃ v, c.Q w t = some v ∧ IsAncestor c.par z v)
include hc hz hT

omit hz in
theorem Q_after {t : ℕ} (ht : T ≤ t) :
    ∃ v, c.Q w t = some v ∧ (v : ℕ∞) < c.N ∧ c.occ z <+: c.occ v := by
  obtain ⟨v, hQ, ha⟩ := hT t ht
  have hv := (guess_spec hQ).1
  exact ⟨v, hQ, hv, anc_prefix hc ha hv⟩

/-- A board without inputs up to `T` and missing the core of `z` is initialized after `T`, and its
retained path passes through the occurrence of `z`. -/
theorem good_bpath {C : Rect d} (hTC : ∀ i ≤ T, w i ∉ C.pts)
    (hcore : Disjoint C.pts (core d (lastOf (c.occ z)).a)) {t : ℕ} (ht : w t ∈ C.pts) :
    T < t0 w C ∧ ∃ p, c.bpath w C = some p ∧ c.occ z <+: p := by
  obtain ⟨h1, h2, -⟩ := t0_spec ht
  have hT0 : T < t0 w C := by
    by_contra hle
    exact hTC _ (by omega) h2
  refine ⟨hT0, ?_⟩
  obtain ⟨v, hQ, hv, hpre⟩ := Q_after hc hT (t := t0 w C) hT0.le
  have hne := hc.occ_ne z hz
  have hlz := List.length_pos_iff.mpr hne
  have hlen := hpre.length_le
  have hpred : Disjoint C.pts (core d (dat (c.occ v) ((c.occ z).length - 1)).a) := by
    rw [← dat_of_prefix hpre _ (by omega), ← lastOf_eq_dat _ hne]
    exact hcore
  have hcut : (c.occ z).length - 1 ≤ c.cut v C := Nat.le_findGreatest (by omega) hpred
  have hcutP : Disjoint C.pts (core d (dat (c.occ v) (c.cut v C)).a) :=
    Nat.findGreatest_spec (P := fun i => Disjoint C.pts (core d (dat (c.occ v) i).a))
      (m := (c.occ z).length - 1) (by omega) hpred
  refine ⟨(c.occ v).take (c.cut v C + 1), ?_, List.prefix_take_iff.2 ⟨hpre, by omega⟩⟩
  unfold bpath
  rw [hQ]
  simp only
  rw [if_pos hcutP]

/-- After `T`, the lowest common ancestor stays at or below `z`. -/
theorem lca_ge {p : List (Deco d)} (hp : c.occ z <+: p) {t : ℕ} (ht : T ≤ t) :
    (c.occ z).length - 1 ≤ c.lca w p t ∧
      ∃ u, c.Q w t = some u ∧ p.take (c.lca w p t + 1) <+: c.occ u := by
  obtain ⟨v, hQ, hv, hpre⟩ := Q_after hc hT ht
  have hne := hc.occ_ne z hz
  have hlz := List.length_pos_iff.mpr hne
  have hlen := hp.length_le
  have htake : p.take ((c.occ z).length - 1 + 1) = c.occ z := by
    rw [show (c.occ z).length - 1 + 1 = (c.occ z).length by omega]
    exact (List.prefix_iff_eq_take.1 hp).symm
  have hpred : ∃ u, c.Q w t = some u ∧ p.take ((c.occ z).length - 1 + 1) <+: c.occ u :=
    ⟨v, hQ, by rw [htake]; exact hpre⟩
  exact ⟨Nat.le_findGreatest (by omega) hpred,
    Nat.findGreatest_spec (P := fun i => ∃ u, c.Q w t = some u ∧ p.take (i + 1) <+: c.occ u)
      (m := (c.occ z).length - 1) (by omega) hpred⟩

theorem levK_bounds {p : List (Deco d)} (hp : c.occ z <+: p) {t₀ : ℕ} (ht₀ : T ≤ t₀) :
    ∀ k, (c.occ z).length - 1 ≤ c.levK w p t₀ k ∧ c.levK w p t₀ k ≤ p.length - 1
  | 0 => by
    have := hp.length_le
    exact ⟨by simp only [levK]; omega, le_rfl⟩
  | k + 1 => by
    obtain ⟨ih1, ih2⟩ := levK_bounds hp ht₀ k
    have := (lca_ge hc hz hT hp (t := t₀ + k + 1) (by omega)).1
    simp only [levK]
    exact ⟨le_min ih1 this, (min_le_left _ _).trans ih2⟩

end Target

/-! ### The simulation hypotheses of Lemma 8.12 for the actual generator -/

theorem hpre_of {w : ℕ → Pt d} {C : Rect d} (p : List (Deco d)) :
    ∀ t < t0 w C, w t ∉ packetSupport (Lsf p) (c.rectsf p C) :=
  fun _ ht hU => t0_min ht (support_sub p C hU)

theorem hlev0_of (w : ℕ → Pt d) (p : List (Deco d)) (t₀ : ℕ) : c.lev w p t₀ t₀ = p.length - 1 := by
  simp [lev, levK]

theorem hlev_of (w : ℕ → Pt d) (p : List (Deco d)) (t₀ : ℕ) :
    ∀ t ≥ t₀, c.lev w p t₀ (t + 1) ≤ c.lev w p t₀ t := by
  intro t ht
  unfold lev
  rw [show t + 1 - t₀ = (t - t₀) + 1 by omega]
  simp only [levK]
  exact min_le_left _ _

/-- **Item 3a of the simulation** (`hvis` of Lemma 8.12) on a board initialized after `T`: from
the initialization round on, every input lies in the language of its pullback level (the premise of
`hvis`, that the input lies in the packet support, is not needed). -/
theorem hvis_of (hc : c.Good) {z : ℕ} (hz : (z : ℕ∞) < c.N) {w : ℕ → Pt d} {T : ℕ}
    (hT : ∀ t ≥ T, ∃ v, c.Q w t = some v ∧ IsAncestor c.par z v) {C : Rect d}
    {p : List (Deco d)} (hb : c.bpath w C = some p) (hp : c.occ z <+: p) (hT0 : T ≤ t0 w C) :
    ∀ t ≥ t0 w C, w t ∈ Lsf p ⟨min (c.lev w p (t0 w C) t) (p.length - 1), by omega⟩ := by
  intro t ht
  have hbd := levK_bounds hc hz hT hp hT0 (t - t0 w C)
  have hlv : c.lev w p (t0 w C) t = c.levK w p (t0 w C) (t - t0 w C) := rfl
  have hmin : min (c.lev w p (t0 w C) t) (p.length - 1) = c.lev w p (t0 w C) t := by
    rw [hlv]; exact min_eq_left hbd.2
  obtain ⟨u, j, hQ, hpu, hj⟩ : ∃ u j, c.Q w t = some u ∧ p.take (j + 1) <+: c.occ u ∧
      c.lev w p (t0 w C) t ≤ j := by
    rcases Nat.eq_zero_or_pos (t - t0 w C) with h0 | hpos
    · obtain ⟨u, hQ, -, hpu, -, -⟩ := bpath_ok hc hb
      have ht' : t = t0 w C := by omega
      subst ht'
      refine ⟨u, p.length - 1, hQ, ?_, ?_⟩
      · rw [List.take_of_length_le (by omega)]; exact hpu
      · rw [hlv, h0]; simp [levK]
    · obtain ⟨k, hk⟩ : ∃ k, t - t0 w C = k + 1 := ⟨t - t0 w C - 1, by omega⟩
      obtain ⟨-, u, hQ, hpu⟩ := lca_ge hc hz hT hp (t := t) (by omega)
      refine ⟨u, c.lca w p t, hQ, hpu, ?_⟩
      rw [hlv, hk]
      simp only [levK]
      rw [show t0 w C + k + 1 = t by omega]
      exact min_le_right _ _
  have hu := guess_spec hQ
  have hwu : w t ∈ c.lab u := hu.2 (SeparationAux.mem_inputsUpTo w le_rfl)
  have hlenp := hp.length_le
  have hne := hc.occ_ne z hz
  have hlz := List.length_pos_iff.mpr hne
  have hok := hc.path_ok u hu.1 (c.occ u) (hc.occ_ne u hu.1) (List.prefix_refl _)
  set lv := c.lev w p (t0 w C) t with hlvdef
  have hlvlt : lv < (p.take (j + 1)).length := by
    simp only [List.length_take]; omega
  show w t ∈ (dat p (min lv (p.length - 1))).L
  rw [hmin, ← dat_take (q := p) (n := j + 1) (j := lv) (by omega), dat_of_prefix hpu lv hlvlt]
  refine hok.last_sub (by have := hpu.length_le; omega) ?_
  rw [hc.last_L u hu.1]
  exact hwu

/-- **The local quota** on a non-exceptional board (Lemma 8.12 applied at the level of `z`). -/
theorem local_quota (hd : 1 ≤ d) (hc : c.Good) (hcov : ∀ x : Pt d, ∃ C ∈ c.Pb, x ∈ C.pts)
    (hdisj : ∀ C ∈ c.Pb, ∀ C' ∈ c.Pb, C ≠ C' → Disjoint C.pts C'.pts) {z : ℕ}
    (hz : (z : ℕ∞) < c.N) {w : ℕ → Pt d} (hw : IsFullEnumeration w (c.lab z)) {T : ℕ}
    (hT : ∀ t ≥ T, ∃ v, c.Q w t = some v ∧ IsAncestor c.par z v) {C : Rect d} (hC : C ∈ c.Pb)
    (hTC : ∀ i ≤ T, w i ∉ C.pts) (hcore : Disjoint C.pts (core d (lastOf (c.occ z)).a))
    {R' : Rect d} (hRC : R'.pts ⊆ C.pts)
    (hcut : (lastOf (c.occ z)).s * c.h R'.vol ≤ mass (c.lab z) R') :
    c.qd (lastOf (c.occ z)) * (mass (c.lab z) R' : ℝ) ≤
      ((range (c.Y w) ∩ c.lab z ∩ R'.pts).ncard : ℝ) := by
  by_cases hex : ∃ t, w t ∈ C.pts
  swap
  · have hm : mass (c.lab z) R' = 0 := by
      unfold mass
      rw [Set.ncard_eq_zero ((BasicAux.rect_pts_finite R').inter_of_right _)]
      ext q
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      intro hq hqR
      rw [← hw] at hq
      obtain ⟨s, rfl⟩ := hq
      exact hex ⟨s, hRC hqR⟩
    rw [hm]; simp
  obtain ⟨t, ht⟩ := hex
  obtain ⟨hT0, p, hb, hp⟩ := good_bpath hc hz hT hTC hcore ht
  obtain ⟨u, hQ, hu, hpu, hok, -⟩ := bpath_ok hc hb
  have hne := hc.occ_ne z hz
  have hlz := List.length_pos_iff.mpr hne
  have hlenp := hp.length_le
  set iz := (c.occ z).length - 1 with hiz
  have hnth : dat p iz = lastOf (c.occ z) := by
    rw [← dat_of_prefix hp iz (by omega), ← lastOf_eq_dat _ hne]
  let i : Fin (p.length - 1 + 1) := ⟨iz, by omega⟩
  have hLi : Lsf p i = c.lab z := by
    show (dat p iz).L = _
    rw [hnth, hc.last_L z hz]
  have hsi : ssf p i = (lastOf (c.occ z)).s := by show (dat p iz).s = _; rw [hnth]
  have hqi : c.qsf p i = c.qd (lastOf (c.occ z)) := by show c.qd (dat p iz) = _; rw [hnth]
  have hR' : R' ∈ c.rectsf p C i := by
    refine mem_rectsIn.2 ⟨hRC, ?_⟩
    rw [hsi, hLi]; exact hcut
  -- every visible point of level `iz` is eventually input
  have hAfin : (packetSupport (Lsf p) (c.rectsf p C) ∩ Lsf p i).Finite :=
    (BasicAux.rect_pts_finite C).subset (fun q hq => support_sub p C hq.1)
  obtain ⟨M, hM⟩ := exists_bound hAfin (fun q hq => by
    have : q ∈ c.lab z := hLi ▸ hq.2
    rw [← hw] at this
    obtain ⟨s, hs⟩ := this
    exact ⟨s, hs⟩)
  have hσ := strat_wins hc hb
  have hhelp := lem_hd_help (Lsf p) (c.qsf p) (c.rectsf p C) hok.2.1 (c.strat p C) hσ w (c.Y w)
    (c.lev w p (t0 w C)) (t0 w C) (hpre_of p) (hlev0_of w p _) (hlev_of w p _)
    (fun t ht _ => hvis_of hc hz hT hb hp hT0.le t ht) (hout_of hcov hdisj hC hb)
    (c.hfresh_of hd hc w) (M + 1)
  simp only at hhelp
  obtain ⟨-, -, h3⟩ := hhelp
  have hlevel : i ≤ (simRun (packetGame (Lsf p) (c.qsf p) (c.rectsf p C)) (c.strat p C) w
      (c.lev w p (t0 w C)) (t0 w C) (M + 1)).2.1.level := by
    refine sim_level_ge (S := packetGame (Lsf p) (c.qsf p) (c.rectsf p C)) _ _ _ iz
      (show iz ≤ p.length - 1 by omega) (M + 1) fun j _ => ?_
    have := (levK_bounds hc hz hT hp hT0.le ((t0 w C + j) - t0 w C)).1
    exact this
  have hall : ∀ q ∈ packetSupport (Lsf p) (c.rectsf p C) ∩ Lsf p i,
      ∃ t, t0 w C ≤ t ∧ t < t0 w C + (M + 1) ∧ w t = q := by
    intro q hq
    obtain ⟨s, hs, hsq⟩ := hM q hq
    refine ⟨s, ?_, by omega, hsq⟩
    by_contra hlt
    push Not at hlt
    exact t0_min hlt (hsq ▸ support_sub p C hq.1)
  have key := h3 i hlevel hall R' hR'
  rw [hqi, hLi] at key
  refine key.trans ?_
  have hfin : (range (c.Y w) ∩ c.lab z ∩ R'.pts).Finite :=
    (BasicAux.rect_pts_finite R').inter_of_right _
  exact_mod_cast Set.ncard_le_ncard (Set.inter_subset_inter_left _
    (Set.inter_subset_inter_left _ (by rintro q ⟨s, -, rfl⟩; exact ⟨s, rfl⟩))) hfin

end Cfg


/-! ## Sewing: from local quotas to a density bound -/

/-- The properties of the sewing partition used here (those of Lemma 8.11, for one threshold). -/
structure Sew (Pb : Set (Rect d)) (h : ℕ → ℝ) (cst : ℝ) : Prop where
  disj : ∀ C ∈ Pb, ∀ C' ∈ Pb, C ≠ C' → Disjoint C.pts C'.pts
  cover : ∀ x : Pt d, ∃ C ∈ Pb, x ∈ C.pts
  fin : ∀ R : Rect d, {C ∈ Pb | (C.pts ∩ R.pts).Nonempty}.Finite
  sum : ∀ R : Rect d,
    (∑ᶠ C ∈ {C ∈ Pb | (C.pts ∩ R.pts).Nonempty}, h (C.pts ∩ R.pts).ncard) ≤ cst * h R.vol

/-- A nonempty intersection of a board with a rectangle is a rectangle. The nonemptiness
hypothesis is required because every `Rect` has a point. -/
theorem rect_inter (C R : Rect d) (hne : (C.pts ∩ R.pts).Nonempty) :
    ∃ R' : Rect d, R'.pts = C.pts ∩ R.pts := by
  obtain ⟨x, hx1, hx2⟩ := hne
  have hle : C.lo ⊔ R.lo ≤ C.hi ⊓ R.hi :=
    sup_le (le_inf (hx1.1.trans hx1.2) (hx1.1.trans hx2.2))
      (le_inf (hx2.1.trans hx1.2) (hx2.1.trans hx2.2))
  refine ⟨Rect.mk (C.lo ⊔ R.lo) (C.hi ⊓ R.hi) hle, ?_⟩
  simp only [Rect.pts, Rect.lo, Rect.hi]
  exact (Set.Icc_inter_Icc).symm

/-- Counting a finite subset of a rectangle board by board. -/
theorem ncard_eq_sum_boards {Pb : Set (Rect d)}
    (hdisj : ∀ C ∈ Pb, ∀ C' ∈ Pb, C ≠ C' → Disjoint C.pts C'.pts)
    (hcov : ∀ x : Pt d, ∃ C ∈ Pb, x ∈ C.pts) {R : Rect d}
    (hfin : {C ∈ Pb | (C.pts ∩ R.pts).Nonempty}.Finite) {A : Set (Pt d)} (hA : A.Finite)
    (hAR : A ⊆ R.pts) : A.ncard = ∑ C ∈ hfin.toFinset, (A ∩ C.pts).ncard := by
  have heq : hA.toFinset = hfin.toFinset.biUnion (fun C => hA.toFinset.filter (· ∈ C.pts)) := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_filter, Set.Finite.mem_toFinset, mem_setOf_eq]
    constructor
    · intro hx
      obtain ⟨C, hC, hxC⟩ := hcov x
      exact ⟨C, ⟨hC, x, hxC, hAR hx⟩, hx, hxC⟩
    · rintro ⟨C, -, hx, -⟩; exact hx
  rw [Set.ncard_eq_toFinset_card A hA, heq, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun C _ => ?_
    rw [Set.ncard_eq_toFinset_card _ (hA.inter_of_left _)]
    congr 1
    ext x; simp
  · intro C hC C' hC' hne
    simp only [Set.Finite.coe_toFinset, mem_setOf_eq] at hC hC'
    show Disjoint _ _
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter] at hx hx'
    exact Set.disjoint_left.1 (hdisj C hC.1 C' hC'.1 hne) hx.2 hx'.2

/-- **The sewing count**, a relaxed bound sufficient for the limit in §8.3.5. Unlike
the displayed eq. (finalbound), the exceptional-board and sewing error terms here are
not multiplied by `q`; the hypotheses `q ≤ 1` and nonnegative errors permit this relaxation. -/
theorem sew_count {Pb : Set (Rect d)} {h : ℕ → ℝ} {cst : ℝ} (hs : Sew Pb h cst)
    (hh0 : ∀ n, 1 ≤ n → 0 ≤ h n) (O K : Set (Pt d)) (E : Finset (Rect d)) {q s : ℝ}
    (hq1 : q ≤ 1) (hs0 : 0 ≤ s)
    (hloc : ∀ C ∈ Pb, C ∉ E → ∀ R' : Rect d, R'.pts ⊆ C.pts → s * h R'.vol ≤ mass K R' →
      q * (mass K R' : ℝ) ≤ ((O ∩ K ∩ R'.pts).ncard : ℝ)) (R : Rect d) :
    q * (mass K R : ℝ) ≤ ((O ∩ K ∩ R.pts).ncard : ℝ) + (∑ C ∈ E, ((K ∩ C.pts).ncard : ℝ)) +
      s * (cst * h R.vol) := by
  set F := (hs.fin R).toFinset with hF
  have hRf := BasicAux.rect_pts_finite R
  have hm : (mass K R : ℝ) = ∑ C ∈ F, (((K ∩ R.pts) ∩ C.pts).ncard : ℝ) := by
    unfold mass
    rw [ncard_eq_sum_boards hs.disj hs.cover (hs.fin R) (hRf.inter_of_right K)
      Set.inter_subset_right]
    push_cast; rfl
  have ho : ∑ C ∈ F, (((O ∩ K ∩ R.pts) ∩ C.pts).ncard : ℝ) = ((O ∩ K ∩ R.pts).ncard : ℝ) := by
    rw [ncard_eq_sum_boards hs.disj hs.cover (hs.fin R) (hRf.inter_of_right _)
      Set.inter_subset_right]
    push_cast; rfl
  have hsumh : ∑ C ∈ F, h (C.pts ∩ R.pts).ncard ≤ cst * h R.vol := by
    have := hs.sum R
    rwa [finsum_mem_eq_finite_toFinset_sum _ (hs.fin R)] at this
  -- the bound board by board
  have hper : ∀ C ∈ F, q * (((K ∩ R.pts) ∩ C.pts).ncard : ℝ) ≤
      (((O ∩ K ∩ R.pts) ∩ C.pts).ncard : ℝ) +
        (if C ∈ E then ((K ∩ C.pts).ncard : ℝ) else 0) + s * h (C.pts ∩ R.pts).ncard := by
    intro C hC
    simp only [hF, Set.Finite.mem_toFinset, mem_setOf_eq] at hC
    obtain ⟨hCP, hne⟩ := hC
    obtain ⟨R', hR'⟩ := rect_inter C R hne
    have hvol : R'.vol = (C.pts ∩ R.pts).ncard := by unfold Rect.vol; rw [hR']
    have hhC : 0 ≤ h (C.pts ∩ R.pts).ncard := hh0 _ (by rw [← hvol]; exact BasicAux.rect_vol_pos R')
    have hmR' : mass K R' = ((K ∩ R.pts) ∩ C.pts).ncard := by
      unfold mass; rw [hR']; congr 1; ext x; simp only [mem_inter_iff]; tauto
    have hoR' : (O ∩ K ∩ R'.pts) = ((O ∩ K ∩ R.pts) ∩ C.pts) := by
      rw [hR']; ext x; simp only [mem_inter_iff]; tauto
    have hm0 : (0 : ℝ) ≤ (((K ∩ R.pts) ∩ C.pts).ncard : ℝ) := by positivity
    have hqm : q * (((K ∩ R.pts) ∩ C.pts).ncard : ℝ) ≤ (((K ∩ R.pts) ∩ C.pts).ncard : ℝ) := by
      nlinarith
    have ho0 : (0 : ℝ) ≤ (((O ∩ K ∩ R.pts) ∩ C.pts).ncard : ℝ) := by positivity
    have hsh : 0 ≤ s * h (C.pts ∩ R.pts).ncard := mul_nonneg hs0 hhC
    by_cases hCE : C ∈ E
    · rw [if_pos hCE]
      have : (((K ∩ R.pts) ∩ C.pts).ncard : ℝ) ≤ ((K ∩ C.pts).ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard
          (show (K ∩ R.pts) ∩ C.pts ⊆ K ∩ C.pts from fun x hx => ⟨hx.1.1, hx.2⟩)
          ((BasicAux.rect_pts_finite C).inter_of_right K)
      linarith
    · rw [if_neg hCE]
      by_cases hcut : s * h R'.vol ≤ mass K R'
      · have := hloc C hCP hCE R' (by rw [hR']; exact Set.inter_subset_left) hcut
        rw [hmR', hoR'] at this
        linarith
      · push Not at hcut
        rw [hmR', hvol] at hcut
        linarith
  have hE : ∑ C ∈ F, (if C ∈ E then ((K ∩ C.pts).ncard : ℝ) else 0) ≤
      ∑ C ∈ E, ((K ∩ C.pts).ncard : ℝ) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun C hC => (Finset.mem_filter.1 hC).2)
      fun _ _ _ => by positivity
  calc q * (mass K R : ℝ) = ∑ C ∈ F, q * (((K ∩ R.pts) ∩ C.pts).ncard : ℝ) := by
        rw [hm, Finset.mul_sum]
    _ ≤ ∑ C ∈ F, ((((O ∩ K ∩ R.pts) ∩ C.pts).ncard : ℝ) +
        (if C ∈ E then ((K ∩ C.pts).ncard : ℝ) else 0) + s * h (C.pts ∩ R.pts).ncard) :=
        Finset.sum_le_sum hper
    _ = ∑ C ∈ F, (((O ∩ K ∩ R.pts) ∩ C.pts).ncard : ℝ) +
        ∑ C ∈ F, (if C ∈ E then ((K ∩ C.pts).ncard : ℝ) else 0) +
        s * ∑ C ∈ F, h (C.pts ∩ R.pts).ncard := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by
        rw [ho]
        have := mul_le_mul_of_nonneg_left hsumh hs0
        linarith

/-- The sewing constant is nonnegative when `h` has a uniform positive lower bound
`h0` on `n ≥ 1`. A one-point rectangle meets a board, so the sum in `Sew.sum` is positive.
The stated hypothesis is stronger than pointwise positivity alone. -/
theorem cst_nonneg_of_sew {Pb : Set (Rect d)} {h : ℕ → ℝ} {cst : ℝ} (hs : Sew Pb h cst)
    {h0 : ℝ} (hh0 : 0 < h0) (hh : ∀ n, 1 ≤ n → h0 ≤ h n) : 0 ≤ cst := by
  let x : Pt d := 0
  let R : Rect d := Rect.mk x x le_rfl
  have hxR : x ∈ R.pts := ⟨le_rfl, le_rfl⟩
  obtain ⟨C, hC, hxC⟩ := hs.cover x
  have hmem : C ∈ {C ∈ Pb | (C.pts ∩ R.pts).Nonempty} := ⟨hC, ⟨x, hxC, hxR⟩⟩
  have hfin := hs.fin R
  have hpos : ∀ C ∈ {C ∈ Pb | (C.pts ∩ R.pts).Nonempty}, 0 < h (C.pts ∩ R.pts).ncard := by
    intro C' hC'
    have : 1 ≤ (C'.pts ∩ R.pts).ncard :=
      Nat.one_le_iff_ne_zero.2
        ((Set.ncard_pos ((BasicAux.rect_pts_finite R).inter_of_right _)).2 hC'.2).ne'
    exact hh0.trans_le (hh _ this)
  have hsum := hs.sum R
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hsum
  have hspos : 0 < ∑ C ∈ hfin.toFinset, h (C.pts ∩ R.pts).ncard :=
    Finset.sum_pos (fun C' hC' => hpos C' (hfin.mem_toFinset.1 hC')) ⟨C, hfin.mem_toFinset.2 hmem⟩
  have hhv : 0 < h R.vol := hh0.trans_le (hh _ (BasicAux.rect_vol_pos R))
  by_contra hneg
  push Not at hneg
  have : cst * h R.vol < 0 := mul_neg_of_neg_of_pos hneg hhv
  linarith

/-- A lower bound for `δ_h` from a counting bound with an additive error and an error
proportional to `h`. -/
theorem deltaH_ge {h : ℕ → ℝ} {h0 : ℝ} (hh0 : 0 < h0) (hh : ∀ n, 1 ≤ n → h0 ≤ h n)
    (O K : Set (Pt d)) {q B c1 : ℝ} (hq1 : q ≤ 1) (hc1 : 0 ≤ c1)
    (H : ∀ R : Rect d, q * (mass K R : ℝ) ≤ ((O ∩ K ∩ R.pts).ncard : ℝ) + B + c1 * h R.vol) :
    q ≤ deltaH h O K := by
  have hpos : ∀ n, 1 ≤ n → 0 < h n := fun n hn => lt_of_lt_of_le hh0 (hh n hn)
  have ht := (deltaH_tendsto h hpos O K).1
  have hmono := BasicAux.testInf_mono h hpos O K
  refine le_of_forall_sub_le fun ε hε => ?_
  set A : ℝ := |B| / h0 + c1 with hA
  have hA0 : 0 ≤ A := by positivity
  set lam : ℝ := A / ε + 1 with hlam
  have hlam0 : 0 < lam := by positivity
  refine le_trans ?_ (hmono.ge_of_tendsto ht lam)
  rw [BasicAux.testInf_eq]
  split_ifs with hne
  · refine le_csInf hne ?_
    rintro _ ⟨R, hR, rfl⟩
    have hv := BasicAux.rect_vol_pos R
    have hhR := hh _ hv
    have hm : lam * h0 ≤ mass K R := le_trans (mul_le_mul_of_nonneg_left hhR hlam0.le) hR
    have hmpos : 0 < (mass K R : ℝ) := lt_of_lt_of_le (by positivity) hm
    rw [le_div_iff₀ hmpos]
    -- `B + c1 h ≤ ε m`
    have e1 : ε * lam = A + ε := by rw [hlam]; field_simp
    have e2 : ε * (lam * h R.vol) ≤ ε * mass K R := mul_le_mul_of_nonneg_left hR hε.le
    have e3 : |B| ≤ |B| / h0 * h R.vol := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hh0]
      exact mul_le_mul_of_nonneg_left hhR (abs_nonneg B)
    have e4 : (A + ε) * h R.vol = |B| / h0 * h R.vol + c1 * h R.vol + ε * h R.vol := by
      rw [hA]; ring
    have e5 : 0 ≤ ε * h R.vol := mul_nonneg hε.le (hpos _ hv).le
    have e6 : B + c1 * h R.vol ≤ ε * mass K R := by
      have : ε * (lam * h R.vol) = (A + ε) * h R.vol := by rw [← e1]; ring
      nlinarith [le_abs_self B]
    have := H R
    nlinarith
  · linarith

namespace Cfg
variable {c : Cfg d}

/-- **Validity** on a fixed target (§8.3.5): only finitely many outputs lie outside `K`. -/
theorem valid (hd : 1 ≤ d) (hc : c.Good) (hcov : ∀ x : Pt d, ∃ C ∈ c.Pb, x ∈ C.pts)
    (hdisj : ∀ C ∈ c.Pb, ∀ C' ∈ c.Pb, C ≠ C' → Disjoint C.pts C'.pts) {z : ℕ}
    (hz : (z : ℕ∞) < c.N) {w : ℕ → Pt d} {T : ℕ}
    (hT : ∀ t ≥ T, ∃ v, c.Q w t = some v ∧ IsAncestor c.par z v) :
    {t | c.Y w t ∉ c.lab z}.Finite := by
  set Ex := {C ∈ c.Pb | (∃ i ≤ T, w i ∈ C.pts) ∨
    ¬ Disjoint C.pts (core d (lastOf (c.occ z)).a)} with hEx
  have hExfin : Ex.Finite := by
    refine (((Set.finite_Iic T).image w).union (core_finite (d := d) (lastOf (c.occ z)).a)).image c.boardOf |>.subset ?_
    rintro C ⟨hC, h | h⟩
    · obtain ⟨i, hi, hiC⟩ := h
      exact ⟨w i, Or.inl ⟨i, hi, rfl⟩, c.boardOf_eq hcov hdisj hC hiC⟩
    · obtain ⟨q, hq1, hq2⟩ := Set.not_disjoint_iff.1 h
      exact ⟨q, Or.inr hq2, c.boardOf_eq hcov hdisj hC hq1⟩
  set E := ⋃ C ∈ Ex, C.pts with hE
  have hEfin : E.Finite := hExfin.biUnion fun C _ => BasicAux.rect_pts_finite C
  have hfr := c.hfresh_of hd hc w
  have hinj : Function.Injective (c.Y w) := by
    intro s t hst
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hfr t).2 s h hst
    · exact (hfr s).2 t h hst.symm
  have hne := hc.occ_ne z hz
  have hlz := List.length_pos_iff.mpr hne
  have claim : ∀ t ≥ T, c.Y w t ∈ c.lab z ∨ c.Y w t ∈ E := by
    intro t ht
    obtain ⟨v, hQ, hv, hpre⟩ := Q_after hc hT ht
    have hfb : freshIn (c.fbLang w t) (usedSet w t (c.outs w t)) ∈ c.lab z := by
      have := (freshIn_spec (c.fbLang_infinite hd hc w t) (usedSet_finite w t (c.outs w t))).1
      have hfbL : c.fbLang w t = c.lab v := by unfold fbLang; rw [hQ]
      rw [hfbL] at this ⊢
      exact lab_sub_of_prefix hc hz hv hpre this
    obtain ⟨hCP, hwC⟩ := c.boardOf_spec hcov (w t)
    set C := c.boardOf (w t) with hCdef
    have hY : c.Y w t = c.step w t (c.outs w t) := rfl
    rcases hs : c.simOut w C t with _ | y
    · left
      rw [hY]; unfold step; rw [← hCdef, hs]; exact hfb
    · by_cases hyu : y ∉ usedSet w t (c.outs w t)
      swap
      · left
        rw [hY]; unfold step; rw [← hCdef, hs]; simp only; rw [if_neg hyu]; exact hfb
      have hYy : c.Y w t = y := by
        rw [hY]; unfold step; rw [← hCdef, hs]; simp only; rw [if_pos hyu]
      rw [hYy]
      unfold simOut at hs
      rcases hb : c.bpath w C with _ | p
      · rw [hb] at hs; cases hs
      rw [hb] at hs
      simp only at hs
      have hvis := sim_reply_vis (strat_wins hc hb) _ _ _ _ hs
      have hy1 : y ∈ packetSupport (Lsf p) (c.rectsf p C) := hvis.1
      by_cases hCEx : C ∈ Ex
      · right
        exact Set.mem_biUnion hCEx (support_sub p C hy1)
      left
      simp only [hEx, mem_setOf_eq, not_and, not_or, not_exists, not_not] at hCEx
      obtain ⟨hTC, hcore⟩ := hCEx hCP
      obtain ⟨hT0, p', hb', hp⟩ := good_bpath hc hz hT (fun i hi hiC => hTC i hi hiC) hcore hwC
      rw [hb] at hb'
      cases hb'
      obtain ⟨-, -, -, -, hok, -⟩ := bpath_ok hc hb
      have hlenp := hp.length_le
      set lvl := (simRun (c.game p C) (c.strat p C) w (c.lev w p (t0 w C)) (t0 w C)
        (t - t0 w C + 1)).2.1.level with hlvl
      have hge : (c.occ z).length - 1 ≤ lvl.val :=
        sim_level_ge (S := c.game p C) _ _ _ _ (show (c.occ z).length - 1 ≤ p.length - 1 by omega)
          _ fun j _ => (levK_bounds hc hz hT hp hT0.le ((t0 w C + j) - t0 w C)).1
      have hlt : lvl.val < p.length := by have := lvl.isLt; have : (c.game p C).r = p.length - 1 := rfl; omega
      have h1 : (dat p lvl.val).L ⊆ (dat p ((c.occ z).length - 1)).L := hok.L_anti hge hlt
      rw [← dat_of_prefix hp ((c.occ z).length - 1) (by omega), ← lastOf_eq_dat _ hne,
        hc.last_L z hz] at h1
      exact h1 hvis.2
  refine ((Set.finite_Iio T).union (hEfin.preimage hinj.injOn)).subset ?_
  intro t ht
  by_cases htT : t < T
  · exact Or.inl htT
  · right
    rcases claim t (by omega) with h | h
    · exact absurd h ht
    · exact h

/-- **Density** on a fixed target (§8.3.5). -/
theorem density (hd : 1 ≤ d) (hc : c.Good) {cst : ℝ} (hs : Sew c.Pb c.h cst)
    {h0 : ℝ} (hh0 : 0 < h0) (hh : ∀ n, 1 ≤ n → h0 ≤ c.h n) {z : ℕ} (hz : (z : ℕ∞) < c.N)
    {w : ℕ → Pt d} (hw : IsFullEnumeration w (c.lab z)) {T : ℕ}
    (hT : ∀ t ≥ T, ∃ v, c.Q w t = some v ∧ IsAncestor c.par z v)
    (hq1 : c.qd (lastOf (c.occ z)) ≤ 1)
    (hs0 : 0 ≤ (lastOf (c.occ z)).s) :
    c.qd (lastOf (c.occ z)) ≤ deltaH c.h (range (c.Y w)) (c.lab z) := by
  set Ex := {C ∈ c.Pb | (∃ i ≤ T, w i ∈ C.pts) ∨
    ¬ Disjoint C.pts (core d (lastOf (c.occ z)).a)} with hEx
  have hExfin : Ex.Finite := by
    refine (((Set.finite_Iic T).image w).union (core_finite (d := d) (lastOf (c.occ z)).a)).image c.boardOf |>.subset ?_
    rintro C ⟨hC, h | h⟩
    · obtain ⟨i, hi, hiC⟩ := h
      exact ⟨w i, Or.inl ⟨i, hi, rfl⟩, c.boardOf_eq hs.cover hs.disj hC hiC⟩
    · obtain ⟨q, hq1, hq2⟩ := Set.not_disjoint_iff.1 h
      exact ⟨q, Or.inr hq2, c.boardOf_eq hs.cover hs.disj hC hq1⟩
  refine deltaH_ge hh0 hh _ _ (B := ∑ C ∈ hExfin.toFinset, ((c.lab z ∩ C.pts).ncard : ℝ)) hq1
    (mul_nonneg hs0 (cst_nonneg_of_sew hs hh0 hh)) fun R => ?_
  have := sew_count hs (fun n hn => (hh0.trans_le (hh n hn)).le) (range (c.Y w)) (c.lab z)
    hExfin.toFinset hq1 hs0 (fun C hC hCE R' hRC hcut => ?_) R
  · rw [mul_assoc]; exact this
  simp only [Set.Finite.mem_toFinset, hEx, mem_setOf_eq, not_and, not_or, not_exists,
    not_not] at hCE
  obtain ⟨hTC, hcore⟩ := hCE hC
  exact local_quota hd hc hs.cover hs.disj hz hw hT hC (fun i hi hiC => hTC i hi hiC) hcore hRC hcut

/-- **The construction works on every vertex**: on every full enumeration of `L_z`, the
generator is eventually valid and guarantees the quota of `z`. -/
theorem gen_works (hd : 1 ≤ d) (hc : c.Good) {cst : ℝ} (hs : Sew c.Pb c.h cst)
    {h0 : ℝ} (hh0 : 0 < h0) (hh : ∀ n, 1 ≤ n → h0 ≤ c.h n) {z : ℕ} (hz : (z : ℕ∞) < c.N)
    {w : ℕ → Pt d} (hw : IsFullEnumeration w (c.lab z))
    (hq1 : c.qd (lastOf (c.occ z)) ≤ 1)
    (hs0 : 0 ≤ (lastOf (c.occ z)).s) :
    c.gen.EventuallyValid w (c.lab z) ∧
      c.qd (lastOf (c.occ z)) ≤ deltaH c.h (c.gen.outputSet w) (c.lab z) := by
  have hPz : (c.P z).Finite ∧ c.P z ⊆ c.lab z := ⟨Finset.finite_toSet _, hc.P_sub z hz⟩
  obtain ⟨T, hT⟩ := ForestAux.capture_gen c.strict c.N c.lab c.P hc.inj z hz hPz w hw
  have hT' : ∀ t ≥ T, ∃ v, c.Q w t = some v ∧ IsAncestor c.par z v := hT
  refine ⟨?_, ?_⟩
  · unfold Generator.EventuallyValid
    simp_rw [c.gen_out]
    exact valid hd hc hs.cover hs.disj hz hT'
  · rw [c.gen_outputSet]
    exact density hd hc hs hh0 hh hz hw hT' hq1 hs0

end Cfg

end SuffAux

end BanachDensityHD
