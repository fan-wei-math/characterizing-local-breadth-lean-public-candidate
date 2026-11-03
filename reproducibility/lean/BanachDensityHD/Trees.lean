import BanachDensityHD.Game

/-!
# Protected trees and geometric decorations

Kleinberg–Wei, *Characterizing Local Breadth in Language Generation*.
Historical source numbering is retained; current mappings are in the release registry.

-/

namespace BanachDensityHD

open Set Filter
open scoped Classical

/-! ## Protected trees (Definitions 8.5 and 8.14) -/

/-- The data at a vertex of a protected tree: language label, accuracy index (`1` for the
fixed-quota trees of Definition 8.5), protected set, cutoff, radius. -/
inductive Deco (d : ℕ)
  | mk (L : Set (Pt d)) (k : ℕ) (P : Finset (Pt d)) (s a : ℝ)

/-- The language label `L_v`. -/
def Deco.L {d : ℕ} : Deco d → Set (Pt d)
  | .mk L _ _ _ _ => L

/-- The accuracy index `k_v` (`1` in the fixed-quota trees of Definition 8.5). -/
def Deco.k {d : ℕ} : Deco d → ℕ
  | .mk _ k _ _ _ => k

/-- The protected set `P_v`. -/
def Deco.P {d : ℕ} : Deco d → Finset (Pt d)
  | .mk _ _ P _ _ => P

/-- The cutoff `s_v`. -/
def Deco.s {d : ℕ} : Deco d → ℝ
  | .mk _ _ _ s _ => s

/-- The radius `a_v`. -/
def Deco.a {d : ℕ} : Deco d → ℝ
  | .mk _ _ _ _ a => a

/-- A rooted tree, encoded by its set of root-to-vertex paths (nonempty lists of vertex data,
closed under nonempty prefixes, all starting at the root, countably many). Two children carrying
identical data are identified; this does not change which trees exist (their subtrees can be
merged). -/
inductive DTree (d : ℕ)
  | mk (paths : Set (List (Deco d))) (root : Deco d) (root_mem : [root] ∈ paths)
      (head : ∀ p ∈ paths, p.head? = some root)
      (prefix_closed : ∀ p ∈ paths, ∀ n, 1 ≤ n → p.take n ∈ paths)
      (countable : paths.Countable)

/-- The root-to-vertex paths of the tree. -/
def DTree.paths {d : ℕ} : DTree d → Set (List (Deco d))
  | .mk paths _ _ _ _ _ => paths

/-- The root's data. -/
def DTree.root {d : ℕ} : DTree d → Deco d
  | .mk _ root _ _ _ _ => root

/-- The labels, cutoffs, accuracy indices along a nonempty path, as functions on `Fin (r+1)`. -/
def pathFn {d : ℕ} {β : Type*} (f : Deco d → β) (p : List (Deco d)) (hp : p ≠ []) :
    Fin (p.length - 1 + 1) → β :=
  fun i => f (p.get ⟨i.val, by
    have := List.length_pos_iff.mpr hp; omega⟩)

/-- **Definition 8.5** (`def:protected-tree`): `T` is a `q`-protected tree rooted at `K`. -/
def IsProtectedTree {d : ℕ} (X : Set (Set (Pt d))) (h : ℕ → ℝ) (q : Set (Pt d) → ℝ)
    (K : Set (Pt d)) (T : DTree d) : Prop :=
  T.root.L = K ∧
  (∀ p ∈ T.paths, ∀ v ∈ p, v.L ∈ X ∧ ↑v.P ⊆ v.L ∧ 1 ≤ v.s ∧ 0 ≤ v.a ∧ v.k = 1) ∧
  (∀ p v w, p ++ [v, w] ∈ T.paths → w.L ⊂ v.L ∧ v.a < w.a) ∧
  -- condition 1: a child for every proper refinement containing the protected set
  (∀ p ∈ T.paths, ∀ (hp : p ≠ []), ∀ M ∈ X, ↑(p.getLast hp).P ⊆ M → M ⊂ (p.getLast hp).L →
      ∃ w : Deco (d), w.L = M ∧ p ++ [w] ∈ T.paths) ∧
  -- condition 2: geometric feasibility along every root-to-vertex path
  (∀ p ∈ T.paths, ∀ (hp : p ≠ []),
      GeomFeasible h (pathFn Deco.L p hp) (fun i => q (pathFn Deco.L p hp i))
        (pathFn Deco.s p hp) (p.getLast hp).a)

/-- The copy quota `q(L,k) = (α(L) - 1/k)_+` (§8.5). -/
noncomputable def copyQuota {d : ℕ} (α : Set (Pt d) → ℝ) (L : Set (Pt d)) (k : ℕ) : ℝ :=
  max (α L - 1 / k) 0

/-- The **monotone** copy relation, an alternative to the broad relation
`IsBroadCopyProtectedTree` in Definition 8.14:
a copy `(M,n)` is a compatible child of a vertex labelled `(L,k)` with protected set `P` iff
`P ⊆ M ⊆ L` and either `M ⊊ L` (any `n ≥ 1`) or `M = L` and `n > k`. -/
def CompatibleCopy {d : ℕ} (P : Set (Pt d)) (L : Set (Pt d)) (k : ℕ) (M : Set (Pt d)) (n : ℕ) :
    Prop :=
  1 ≤ n ∧ P ⊆ M ∧ M ⊆ L ∧ (M ⊂ L ∨ (M = L ∧ k < n))

/-- Alternative monotone formulation of **Definition 8.14** (the broad formulation
is `IsBroadCopyProtectedTree`): a protected tree on accuracy copies rooted at
`(K,k)`. Every edge goes to a compatible copy (proper refinement, or the same language with a
strictly larger accuracy index), radii strictly increase, every compatible copy of every vertex
is present as a child, and every root-to-vertex path — a *nonincreasing* chain of languages with
repeated languages kept — is geometrically feasible with the per-copy quotas
`q(L,k) = (α(L) - 1/k)_+`. -/
def IsCopyProtectedTree {d : ℕ} (X : Set (Set (Pt d))) (h : ℕ → ℝ) (α : Set (Pt d) → ℝ)
    (K : Set (Pt d)) (k : ℕ) (T : DTree d) : Prop :=
  T.root.L = K ∧ T.root.k = k ∧
  (∀ p ∈ T.paths, ∀ v ∈ p, v.L ∈ X ∧ ↑v.P ⊆ v.L ∧ 1 ≤ v.s ∧ 0 ≤ v.a ∧ 1 ≤ v.k) ∧
  (∀ p v w, p ++ [v, w] ∈ T.paths → CompatibleCopy (↑v.P) v.L v.k w.L w.k ∧ v.a < w.a) ∧
  (∀ p ∈ T.paths, ∀ (hp : p ≠ []), ∀ M ∈ X, ∀ n,
      CompatibleCopy (↑(p.getLast hp).P) (p.getLast hp).L (p.getLast hp).k M n →
      ∃ w : Deco d, w.L = M ∧ w.k = n ∧ p ++ [w] ∈ T.paths) ∧
  (∀ p ∈ T.paths, ∀ (hp : p ≠ []),
      GeomFeasible h (pathFn Deco.L p hp)
        (fun i => copyQuota α (pathFn Deco.L p hp i) (pathFn Deco.k p hp i))
        (pathFn Deco.s p hp) (p.getLast hp).a)


/-- **Definition 8.14** (`def:copy-protected-tree`) as written in the baseline manuscript: a
protected tree on accuracy copies rooted at `(K,k)`, with the **broad** copy relation. It is
Definition 8.5 except that the vertices carry copy labels `(L_v, k_v)` with `k_v ≥ 1`, equal
underlying languages are allowed along edges (`L_w ⊆ L_v`, radii still strictly increasing), and a
stop at `(L_v, k_v)` uses the quota `q(L_v, k_v) = (α(L_v) - 1/k_v)_+`. For every copy `(M,n)` with
`n ≥ 1`, `M ∈ 𝒳` and `P_v ⊆ M ⊆ L_v`, the vertex has a child labelled `(M,n)`; equal-language
children `(L_v, n)` are required for every `n ≥ 1`, including `n ≤ k_v`. As in Definition 8.5,
children are not otherwise restricted. Every root-to-vertex path (a nonincreasing chain of
languages, repeated languages kept, each copy with its own quota and cutoff) is geometrically
feasible outside the box of its last vertex's radius. Repeated labels are distinct occurrences, so
branches may be infinite; only finite paths are tested. -/
def IsBroadCopyProtectedTree {d : ℕ} (X : Set (Set (Pt d))) (h : ℕ → ℝ) (α : Set (Pt d) → ℝ)
    (K : Set (Pt d)) (k : ℕ) (T : DTree d) : Prop :=
  T.root.L = K ∧ T.root.k = k ∧
  (∀ p ∈ T.paths, ∀ v ∈ p, v.L ∈ X ∧ ↑v.P ⊆ v.L ∧ 1 ≤ v.s ∧ 0 ≤ v.a ∧ 1 ≤ v.k) ∧
  (∀ p v w, p ++ [v, w] ∈ T.paths → w.L ⊆ v.L ∧ v.a < w.a) ∧
  (∀ p ∈ T.paths, ∀ (hp : p ≠ []), ∀ M ∈ X, ∀ n, 1 ≤ n →
      ↑(p.getLast hp).P ⊆ M → M ⊆ (p.getLast hp).L →
      ∃ w : Deco d, w.L = M ∧ w.k = n ∧ p ++ [w] ∈ T.paths) ∧
  (∀ p ∈ T.paths, ∀ (hp : p ≠ []),
      GeomFeasible h (pathFn Deco.L p hp)
        (fun i => copyQuota α (pathFn Deco.L p hp i) (pathFn Deco.k p hp i))
        (pathFn Deco.s p hp) (p.getLast hp).a)


namespace TreesAux

/-- The core boxes are nested: `Q_a ⊆ Q_{a'}` for `a ≤ a'`. -/
lemma core_mono {d : ℕ} {a a' : ℝ} (ha : a ≤ a') : core d a ⊆ core d a' :=
  fun _ hx i => (hx i).trans ha

/-- The number of down-moves in a history. -/
def dcount {d : ℕ} : List (BMove d) → ℕ
  | [] => 0
  | .down :: t => dcount t + 1
  | .claim _ :: t => dcount t

lemma dcount_append {d : ℕ} (l1 l2 : List (BMove d)) :
    dcount (l1 ++ l2) = dcount l1 + dcount l2 := by
  induction l1 with
  | nil => simp [dcount]
  | cons m t ih => cases m <;> simp [dcount, ih]; omega

/-- Translation of a history of a longer game into a history of a shorter game, along the level
map `cN` (on levels as natural numbers); `ℓ` is the current level of the longer game. A claim is
kept; a down-move from level `ℓ` becomes `cN ℓ - cN (ℓ - 1)` down-moves. -/
def tr {d : ℕ} (cN : ℕ → ℕ) : ℕ → List (BMove d) → List (BMove d)
  | _, [] => []
  | ℓ, .claim x :: t => .claim x :: tr cN ℓ t
  | ℓ, .down :: t => List.replicate (cN ℓ - cN (ℓ - 1)) .down ++ tr cN (ℓ - 1) t

lemma tr_append {d : ℕ} (cN : ℕ → ℕ) (l1 l2 : List (BMove d)) (ℓ : ℕ) :
    tr cN ℓ (l1 ++ l2) = tr cN ℓ l1 ++ tr cN (ℓ - dcount l1) l2 := by
  induction l1 generalizing ℓ with
  | nil => simp [tr, dcount]
  | cons m t ih =>
    cases m with
    | claim x => simp [tr, dcount, ih]
    | down =>
      simp only [List.cons_append, tr, ih, dcount, List.append_assoc]
      congr 3
      omega

/-- Down-moves are always legal and leave the claimed points unchanged: from a reachable state at
level `lvl`, descending to any level `t ≤ lvl` reaches the state at level `t` with the same claims. -/
lemma reach_descend {d : ℕ} {S : StopGame d} {σ : WStrategy d} {ms : List (BMove d)}
    {lvl : Fin (S.r + 1)} {B W : Set (Pt d)} (hR : S.Reach σ ms ⟨lvl, B, W⟩)
    (t : Fin (S.r + 1)) (ht : t ≤ lvl) :
    S.Reach σ (ms ++ List.replicate (lvl.val - t.val) .down) ⟨t, B, W⟩ := by
  exact StopGame.Reach.downs hR (lvl.val - t.val) t.val
    (by have : t.val ≤ lvl.val := ht; omega)

/-- **Collapsing levels.** A chain `Ls'` (levels `0, …, m`) whose levels are mapped to the
levels of a feasible chain `Ls` (levels `0, …, r`) by `home` (same language and cutoff, quota at
most) and by a monotone `c` with `home ≤ c`, `c` sending the top level to the top level and every
level to a level of the same language, is feasible outside every larger box. White plays the
shorter chain's strategy on the history translated along `c`; at a stop on level `k` of the longer
game, Black in the shorter game may descend from `c k` to `home k` without changing the state,
where the requirements of `k` hold. -/
theorem collapse {d m r : ℕ} (h : ℕ → ℝ) (Ls' : Fin (m + 1) → Set (Pt d))
    (qs' ss' : Fin (m + 1) → ℝ) (Ls : Fin (r + 1) → Set (Pt d)) (qs ss : Fin (r + 1) → ℝ)
    (a a' : ℝ) (home c : Fin (m + 1) → Fin (r + 1))
    (hL : ∀ k, Ls (home k) = Ls' k) (hLc : ∀ k, Ls (c k) = Ls' k)
    (hq : ∀ k, qs' k ≤ qs (home k)) (hs : ∀ k, ss (home k) = ss' k)
    (hhc : ∀ k, home k ≤ c k) (hc : Monotone c) (hlast : c (Fin.last m) = Fin.last r)
    (ha : a ≤ a') (hF : GeomFeasible h Ls qs ss a) : GeomFeasible h Ls' qs' ss' a' := by
  intro rects' hrects'
  let rects : Fin (r + 1) → Finset (Rect d) :=
    fun i => (Finset.univ.filter (fun k => home k = i)).biUnion rects'
  have hmem : ∀ i R, R ∈ rects i ↔ ∃ k, home k = i ∧ R ∈ rects' k := by
    intro i R; simp [rects]
  obtain ⟨σ, hσ⟩ := hF rects (by
    intro i R hR
    obtain ⟨k, rfl, hk⟩ := (hmem i R).1 hR
    obtain ⟨h1, h2⟩ := hrects' k R hk
    refine ⟨h1.mono_right (core_mono ha), ?_⟩
    rw [hs, hL]; exact h2)
  have hU : packetSupport Ls rects = packetSupport Ls' rects' := by
    ext x
    simp only [packetSupport, Set.mem_iUnion, exists_prop, hmem]
    constructor
    · rintro ⟨i, R, ⟨k, rfl, hk⟩, hx⟩; exact ⟨k, R, hk, by rwa [← hL]⟩
    · rintro ⟨k, R, hk, hx⟩; exact ⟨home k, R, ⟨k, rfl, hk⟩, by rwa [hL]⟩
  have hvis : ∀ k, (packetGame Ls qs rects).visible (c k) = (packetGame Ls' qs' rects').visible k := by
    intro k; simp only [StopGame.visible, packetGame, StopGame.vis, hU, hLc]
  have hvish : ∀ k, (packetGame Ls qs rects).visible (home k) =
      (packetGame Ls' qs' rects').visible k := by
    intro k; simp only [StopGame.visible, packetGame, StopGame.vis, hU, hL]
  have hfree : ∀ (k : Fin (m + 1)) (B W : Set (Pt d)) y,
      (packetGame Ls qs rects).Free ⟨c k, B, W⟩ y ↔ (packetGame Ls' qs' rects').Free ⟨k, B, W⟩ y := by
    intro k B W y
    simp only [StopGame.Free, StopGame.State.level, StopGame.State.black, StopGame.State.white]
    rw [hvis]
  have hleg : ∀ (k : Fin (m + 1)) (B W : Set (Pt d)) rep,
      (packetGame Ls qs rects).LegalReply ⟨c k, B, W⟩ rep ↔
        (packetGame Ls' qs' rects').LegalReply ⟨k, B, W⟩ rep := by
    intro k B W rep
    cases rep with
    | none => simp [StopGame.LegalReply]
    | some y => exact hfree k B W y
  let cN : ℕ → ℕ := fun ℓ => if hℓ : ℓ < m + 1 then (c ⟨ℓ, hℓ⟩).val else r
  have hcN : ∀ k : Fin (m + 1), cN k.val = (c k).val := by
    intro k; simp only [cN]; split_ifs with hk
    · rfl
    · exact absurd k.isLt hk
  let τ : WStrategy d := fun ms => σ (tr cN m ms)
  have hτ : ∀ ms, τ ms = σ (tr cN m ms) := fun _ => rfl
  have hsim : ∀ ms st', (packetGame Ls' qs' rects').Reach τ ms st' →
      (packetGame Ls qs rects).Reach σ (tr cN m ms) ⟨c st'.level, st'.black, st'.white⟩ ∧
        st'.level.val + dcount ms = m := by
    intro ms st' hR
    induction hR with
    | nil =>
      refine ⟨?_, ?_⟩
      · have e : (⟨c (packetGame Ls' qs' rects').init.level,
            (packetGame Ls' qs' rects').init.black, (packetGame Ls' qs' rects').init.white⟩ :
              (packetGame Ls qs rects).State) = (packetGame Ls qs rects).init := by
          simp only [StopGame.init, StopGame.State.level, StopGame.State.black,
            StopGame.State.white]
          exact congrArg (fun z => (⟨z, ∅, ∅⟩ : (packetGame Ls qs rects).State)) hlast
        rw [e]; exact StopGame.Reach.nil
      · simp [StopGame.init, StopGame.State.level, dcount, packetGame, StopGame.r]
    | @claim ms st x hR hfr hlg ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have e : tr cN m (ms ++ [.claim x]) = tr cN m ms ++ [.claim x] := by
        rw [tr_append]; simp [tr]
      refine ⟨?_, ?_⟩
      · rw [hτ, e]
        rw [hτ, e] at hlg
        exact StopGame.Reach.claim ih1 ((hfree _ _ _ _).2 hfr) ((hleg _ _ _ _).2 hlg)
      · simpa [dcount_append, dcount, StopGame.afterClaim, StopGame.State.level] using ih2
    | @down ms st i hR hi ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hci : c i ≤ c st.level := hc (Fin.le_def.2 (by omega))
      have e : tr cN m (ms ++ [.down]) =
          tr cN m ms ++ List.replicate ((c st.level).val - (c i).val) .down := by
        rw [tr_append]
        simp only [tr, List.append_nil]
        have h1 : m - dcount ms = st.level.val := by omega
        have h2 : st.level.val - 1 = i.val := by omega
        rw [h1, h2, show cN st.level.val = (c st.level).val from hcN st.level,
          show cN i.val = (c i).val from hcN i]
      refine ⟨?_, ?_⟩
      · rw [e]
        exact reach_descend (S := packetGame Ls qs rects) ih1 (c i) hci
      · have hr : (packetGame Ls' qs' rects').r = m := rfl
        simp only [dcount_append, dcount, StopGame.State.level]
        omega
  refine ⟨τ, fun ms st' hR => ?_⟩
  obtain ⟨hR1, -⟩ := hsim ms st' hR
  obtain ⟨hw1, -⟩ := hσ _ _ hR1
  refine ⟨fun x hx => ?_, fun hstop R hRm => ?_⟩
  · have := hw1 x ((hfree _ _ _ _).2 hx)
    have e : tr cN m (ms ++ [.claim x]) = tr cN m ms ++ [.claim x] := by
      rw [tr_append]; simp [tr]
    rw [hτ, e]
    exact (hleg _ _ _ _).1 this
  · have hd := reach_descend (S := packetGame Ls qs rects) hR1 (home st'.level) (hhc _)
    obtain ⟨-, hw2⟩ := hσ _ _ hd
    have hst : (packetGame Ls qs rects).visible (home st'.level) ⊆ st'.black ∪ st'.white := by
      exact (hvish _).le.trans hstop
    have := hw2 hst R ((hmem _ R).2 ⟨_, rfl, hRm⟩)
    simp only [StopGame.quota, StopGame.L, packetGame, StopGame.State.level,
      StopGame.State.white] at this ⊢
    have key : ∀ (k : Fin (m + 1)) (W : Set (Pt d)),
        qs (home k) * ((Ls (home k) ∩ R.pts).ncard : ℝ) ≤ ((W ∩ Ls (home k) ∩ R.pts).ncard : ℝ) →
        qs' k * ((Ls' k ∩ R.pts).ncard : ℝ) ≤ ((W ∩ Ls' k ∩ R.pts).ncard : ℝ) := by
      intro k W hk
      rw [hL] at hk
      exact (mul_le_mul_of_nonneg_right (hq _) (Nat.cast_nonneg _)).trans hk
    exact key _ _ this

end TreesAux


namespace TreesAux

lemma succAbove_val {n : ℕ} (p : Fin (n + 2)) (i : Fin (n + 1)) :
    (p.succAbove i).val = if i.val < p.val then i.val else i.val + 1 := by
  unfold Fin.succAbove
  split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_def]

end TreesAux

/-- **Duplicate-level insertion**, proved as a corollary of `TreesAux.collapse`. Insert into a
chain, at any position `p`, a new level whose language and
cutoff are those of an existing level `j` and whose quota `q'` is at most `qs j`, such that the
longer chain is still nonincreasing (so the new level lies in `j`'s block of equal languages). If
the original chain is geometrically feasible outside `Q_a`, the longer chain is geometrically
feasible outside `Q_{a'}` for every `a' ≥ a`.

The proof applies `TreesAux.collapse` to an **arbitrary** packet `rects'` on the longer chain,
with a map sending the inserted level to `j`. The construction establishes:
* a corresponding packet on the original chain, obtained by merging the inserted level's
  rectangles into a suitable existing level of the same language (they meet that level's cutoff
  condition, since the cutoff is the same and `a ≤ a'`);
* that the two packets have the same support `U` and corresponding visible sets `U ∩ Lᵢ` (this is
  not automatic and must be checked for the merged packet);
* one causal White strategy for the longer game that, at **every** stopping level (the inserted
  level included), meets every requirement enforced there, with the quotas and cutoffs of the
  levels as given; inserting the level must not change which stopping requirements are
  enforced at the other levels. -/
theorem GeomFeasible.insert_dup {d r : ℕ} (h : ℕ → ℝ) (Ls : Fin (r + 1) → Set (Pt d))
    (qs ss : Fin (r + 1) → ℝ) (a a' : ℝ) (p : Fin (r + 2)) (j : Fin (r + 1)) (q' : ℝ)
    (hanti : Antitone (Fin.insertNth (α := fun _ => Set (Pt d)) p (Ls j) Ls))
    (hq' : q' ≤ qs j) (ha : a ≤ a') (hF : GeomFeasible h Ls qs ss a) :
    GeomFeasible h (Fin.insertNth (α := fun _ => Set (Pt d)) p (Ls j) Ls)
      (Fin.insertNth (α := fun _ => ℝ) p q' qs) (Fin.insertNth (α := fun _ => ℝ) p (ss j) ss)
      a' := by
  open TreesAux in
  set Ls' := Fin.insertNth (α := fun _ => Set (Pt d)) p (Ls j) Ls with hLs'
  have hp := p.isLt
  have hj := j.isLt
  let home : Fin (r + 2) → Fin (r + 1) := fun k =>
    if hk : k.val < p.val then ⟨k.val, by omega⟩ else if k = p then j else ⟨k.val - 1, by omega⟩
  have home_val : ∀ k : Fin (r + 2), (home k).val =
      if k.val < p.val then k.val else if k.val = p.val then j.val else k.val - 1 := by
    intro k
    simp only [home, Fin.ext_iff]
    split_ifs <;> simp
  have home_p : home p = j := by
    simp [home]
  have home_s : ∀ i, home (p.succAbove i) = i := by
    intro i
    apply Fin.ext
    rw [home_val, succAbove_val]
    split_ifs <;> omega
  let cN : ℕ → ℕ := fun ℓ => if ℓ < p.val then ℓ else if ℓ ≤ j.val + 1 then j.val else ℓ - 1
  let c : Fin (r + 2) → Fin (r + 1) := fun k => ⟨cN k.val, by
    have := k.isLt; simp only [cN]; split_ifs <;> omega⟩
  have hblock : ∀ x : Fin (r + 2), min p.val (p.succAbove j).val ≤ x.val →
      x.val ≤ max p.val (p.succAbove j).val → Ls' x = Ls j := by
    intro x h1 h2
    have eP : Ls' p = Ls j := by simp [hLs']
    have eJ : Ls' (p.succAbove j) = Ls j := by simp [hLs']
    rcases le_total p.val (p.succAbove j).val with hPJ | hPJ
    · have a1 : p ≤ x := Fin.le_def.2 (by omega)
      have a2 : x ≤ p.succAbove j := Fin.le_def.2 (by omega)
      exact Set.Subset.antisymm (eP ▸ hanti a1) (eJ ▸ hanti a2)
    · have a1 : x ≤ p := Fin.le_def.2 (by omega)
      have a2 : p.succAbove j ≤ x := Fin.le_def.2 (by omega)
      exact Set.Subset.antisymm (eJ ▸ hanti a2) (eP ▸ hanti a1)
  refine collapse h Ls' _ _ Ls qs ss a a' home c ?_ ?_ ?_ ?_ ?_ ?_ ?_ ha hF
  · intro k
    rcases Fin.eq_self_or_eq_succAbove p k with rfl | ⟨i, rfl⟩
    · rw [home_p]; simp [hLs']
    · rw [home_s]; simp [hLs']
  · intro k
    have e1 : Ls (c k) = Ls' (p.succAbove (c k)) := by simp [hLs']
    rw [e1]
    have key : (p.succAbove (c k)).val = k.val ∨
        (min p.val (p.succAbove j).val ≤ k.val ∧ k.val ≤ max p.val (p.succAbove j).val ∧
          min p.val (p.succAbove j).val ≤ (p.succAbove (c k)).val ∧
          (p.succAbove (c k)).val ≤ max p.val (p.succAbove j).val) := by
      have := k.isLt
      simp only [succAbove_val, c, cN]
      split_ifs <;> omega
    rcases key with e | ⟨h1, h2, h3, h4⟩
    · rw [Fin.ext e]
    · rw [hblock _ h3 h4, hblock _ h1 h2]
  · intro k
    rcases Fin.eq_self_or_eq_succAbove p k with rfl | ⟨i, rfl⟩
    · rw [home_p]; simpa using hq'
    · rw [home_s]; simp
  · intro k
    rcases Fin.eq_self_or_eq_succAbove p k with rfl | ⟨i, rfl⟩
    · rw [home_p]; simp
    · rw [home_s]; simp
  · intro k
    rw [Fin.le_def, home_val]
    simp only [c, cN]
    split_ifs <;> omega
  · intro x y hxy
    rw [Fin.le_def] at hxy ⊢
    simp only [c, cN]
    split_ifs <;> omega
  · apply Fin.ext
    simp only [c, cN, Fin.val_last]
    split_ifs <;> omega


namespace TreesAux

/-! ### Helpers for the bridge `copyTree_broad_iff_monotone` -/

lemma dtree_prefix {d : ℕ} (T : DTree d) : ∀ p ∈ T.paths, ∀ n, 1 ≤ n → p.take n ∈ T.paths := by
  cases T with
  | mk paths root root_mem head prefix_closed countable => exact prefix_closed

lemma dtree_head {d : ℕ} (T : DTree d) : ∀ p ∈ T.paths, p.head? = some T.root := by
  cases T with
  | mk paths root root_mem head prefix_closed countable => exact head

lemma dtree_root_mem {d : ℕ} (T : DTree d) : [T.root] ∈ T.paths := by
  cases T with
  | mk paths root root_mem head prefix_closed countable => exact root_mem

lemma dtree_countable {d : ℕ} (T : DTree d) : T.paths.Countable := by
  cases T with
  | mk paths root root_mem head prefix_closed countable => exact countable

@[simp] lemma mk_L {d : ℕ} (L : Set (Pt d)) (k : ℕ) (P : Finset (Pt d)) (s a : ℝ) :
    (Deco.mk L k P s a).L = L := rfl
@[simp] lemma mk_k {d : ℕ} (L : Set (Pt d)) (k : ℕ) (P : Finset (Pt d)) (s a : ℝ) :
    (Deco.mk L k P s a).k = k := rfl
@[simp] lemma mk_P {d : ℕ} (L : Set (Pt d)) (k : ℕ) (P : Finset (Pt d)) (s a : ℝ) :
    (Deco.mk L k P s a).P = P := rfl
@[simp] lemma mk_s {d : ℕ} (L : Set (Pt d)) (k : ℕ) (P : Finset (Pt d)) (s a : ℝ) :
    (Deco.mk L k P s a).s = s := rfl
@[simp] lemma mk_a {d : ℕ} (L : Set (Pt d)) (k : ℕ) (P : Finset (Pt d)) (s a : ℝ) :
    (Deco.mk L k P s a).a = a := rfl

/-- A relation holding between consecutive entries of every tree path (from the one-step
extensions; reused from the check file `audits/kw-banach-hd/checks/chain_paths.lean`, generalized
from `⊇` to any relation). -/
lemma path_step_rel {d : ℕ} (T : DTree d) (R : Deco d → Deco d → Prop)
    (hedge : ∀ q v w, q ++ [v, w] ∈ T.paths → R v w) :
    ∀ p ∈ T.paths, ∀ i (hi : i + 1 < p.length), R p[i] p[i + 1] := by
  intro p hp i hi
  have hpre : p.take (i + 2) ∈ T.paths := dtree_prefix T p hp (i + 2) (by omega)
  have hsplit : p.take (i + 2) = p.take i ++ [p[i], p[i + 1]] := by
    apply List.ext_getElem
    · simp; omega
    · intro n h1 h2
      simp only [List.length_take, List.length_append, List.length_cons, List.length_nil] at h1 h2
      rcases lt_trichotomy n i with h | h | h
      · rw [List.getElem_append_left (by simp; omega)]; simp
      · subst h
        have hm : min n p.length = n := by omega
        rw [List.getElem_append_right (by simp)]; simp [hm]
      · have : n = i + 1 := by omega
        subst this
        have hm : min i p.length = i := by omega
        rw [List.getElem_append_right (by simp)]; simp [hm]
  exact hedge _ _ _ (hsplit ▸ hpre)

/-- A reflexive transitive relation between consecutive entries holds for all `i ≤ j`. -/
lemma rel_of_step {d : ℕ} (p : List (Deco d)) (R : Deco d → Deco d → Prop)
    (hrefl : ∀ x, R x x) (htrans : ∀ x y z, R x y → R y z → R x z)
    (hs : ∀ i (hi : i + 1 < p.length), R p[i] p[i + 1]) (i j : ℕ) (hij : i ≤ j)
    (hj : j < p.length) : R (p[i]'(lt_of_le_of_lt hij hj)) p[j] := by
  induction j, hij using Nat.le_induction with
  | base => exact hrefl _
  | succ j hij ih => exact htrans _ _ _ (ih (by omega)) (hs j hj)

/-- The copy quotas are nondecreasing in the accuracy index (for indices `≥ 1`). -/
lemma copyQuota_mono {d : ℕ} (α : Set (Pt d) → ℝ) (L : Set (Pt d)) {n k : ℕ} (hn : 1 ≤ n)
    (hnk : n ≤ k) : copyQuota α L n ≤ copyQuota α L k := by
  unfold copyQuota
  have h1 : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : (n : ℝ) ≤ k := by exact_mod_cast hnk
  exact max_le_max (sub_le_sub_left (one_div_le_one_div_of_le h1 h2) _) le_rfl

/-- A default decoration (never reached on valid indices). -/
def d0 {d : ℕ} : Deco d := Deco.mk ∅ 0 ∅ 0 0

/-- The `j`-th entry of a list of decorations (the default beyond the end). -/
def dat {d : ℕ} (q : List (Deco d)) (j : ℕ) : Deco d := (q[j]?).getD d0

lemma dat_eq {d : ℕ} {q : List (Deco d)} {j : ℕ} (hj : j < q.length) : dat q j = q[j] := by
  simp [dat, hj]

lemma dat_append {d : ℕ} {q q' : List (Deco d)} {j : ℕ} (hj : j < q.length) :
    dat (q ++ q') j = dat q j := by
  simp [dat, List.getElem?_append_left hj]

lemma dat_take {d : ℕ} {q : List (Deco d)} {n j : ℕ} (hj : j < n) : dat (q.take n) j = dat q j := by
  simp [dat, hj]

/-- The decoration of a duplicated vertex: at depth `i`, with code `(j, n)` (effective copy the
`j`-th vertex of the monotone path `q`, accuracy label `n`): language, protected set and cutoff of
`q_j`, label `n`, radius `a_{q_j} + i`. -/
def cdeco {d : ℕ} (q : List (Deco d)) (i : ℕ) (c : ℕ × ℕ) : Deco d :=
  Deco.mk (dat q c.1).L c.2 (dat q c.1).P (dat q c.1).s ((dat q c.1).a + i)

/-- The path of the duplicated tree with codes `cs` over the monotone path `q`. -/
def build {d : ℕ} (q : List (Deco d)) (cs : List (ℕ × ℕ)) : List (Deco d) := cs.mapIdx (cdeco q)

/-- Admissible codes over a monotone path `q`: the first code is the root `(0, k_root)`; every
code `(j, n)` names a vertex `q_j` and a label `1 ≤ n ≤ k_{q_j}`; the effective indices are
nondecreasing and end at the last vertex of `q`. -/
def Valid {d : ℕ} (q : List (Deco d)) (cs : List (ℕ × ℕ)) : Prop :=
  cs.head? = some (0, (dat q 0).k) ∧
  (∀ c ∈ cs, c.1 < q.length ∧ 1 ≤ c.2 ∧ c.2 ≤ (dat q c.1).k) ∧
  cs.Pairwise (fun c c' => c.1 ≤ c'.1) ∧
  ∀ hne : cs ≠ [], (cs.getLast hne).1 = q.length - 1

@[simp] lemma build_length {d : ℕ} (q : List (Deco d)) (cs : List (ℕ × ℕ)) :
    (build q cs).length = cs.length := by simp [build]

@[simp] lemma build_getElem {d : ℕ} (q : List (Deco d)) (cs : List (ℕ × ℕ)) (i : ℕ)
    (h : i < (build q cs).length) : (build q cs)[i] = cdeco q i (cs[i]'(by simpa using h)) := by
  simp [build]

lemma build_append {d : ℕ} (q : List (Deco d)) (cs : List (ℕ × ℕ)) (c : ℕ × ℕ) :
    build q (cs ++ [c]) = build q cs ++ [cdeco q cs.length c] := by
  simp [build]

lemma build_congr {d : ℕ} (q q' : List (Deco d)) (cs : List (ℕ × ℕ))
    (h : ∀ c ∈ cs, dat q c.1 = dat q' c.1) : build q cs = build q' cs := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [build_getElem, cdeco]
  rw [h _ (List.getElem_mem _)]

lemma build_take {d : ℕ} (q : List (Deco d)) (cs : List (ℕ × ℕ)) (n : ℕ) :
    (build q cs).take n = build q (cs.take n) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

lemma le_last {cs : List (ℕ × ℕ)} (hpw : cs.Pairwise (fun c c' => c.1 ≤ c'.1)) (hne : cs ≠ []) :
    ∀ c ∈ cs, c.1 ≤ (cs.getLast hne).1 := by
  intro c hc
  have e := List.dropLast_append_getLast hne
  rw [← e] at hpw hc
  rw [List.pairwise_append] at hpw
  rcases List.mem_append.1 hc with hc | hc
  · exact hpw.2.2 c hc _ (by simp)
  · simp at hc; rw [hc]

/-- Every consecutive edge in the path is monotone-compatible. This is a predicate
on a path, not the pruning construction itself. -/
def MonoGood {d : ℕ} (p : List (Deco d)) : Prop :=
  ∀ q v w, q ++ [v, w] <+: p → CompatibleCopy (↑v.P) v.L v.k w.L w.k

/-- Broad ⇒ monotone: prune to the paths satisfying `MonoGood`. -/
lemma broad_to_mono {d : ℕ} {X : Set (Set (Pt d))} {h : ℕ → ℝ} {α : Set (Pt d) → ℝ}
    {K : Set (Pt d)} {k : ℕ} {T : DTree d} (hT : IsBroadCopyProtectedTree X h α K k T) :
    ∃ T', IsCopyProtectedTree X h α K k T' := by
  obtain ⟨hroot, hk, hvert, hedge, hchild, hfeas⟩ := hT
  have hroot_good : MonoGood [T.root] := by
    intro q v w hpre
    have := hpre.length_le
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    omega
  let T' : DTree d := DTree.mk {p | p ∈ T.paths ∧ MonoGood p} T.root
    ⟨dtree_root_mem T, hroot_good⟩
    (fun p hp => dtree_head T p hp.1)
    (fun p hp n hn => ⟨dtree_prefix T p hp.1 n hn,
      fun q v w hpre => hp.2 q v w (hpre.trans (List.take_prefix n p))⟩)
    ((dtree_countable T).mono (fun p hp => hp.1))
  refine ⟨T', hroot, hk, fun p hp => hvert p hp.1,
    fun p v w hp => ⟨hp.2 p v w (List.prefix_refl _), (hedge p v w hp.1).2⟩, ?_,
    fun p hp => hfeas p hp.1⟩
  intro p hp hpne M hM n hc
  have hc' := hc
  obtain ⟨hn, hPM, hML, -⟩ := hc'
  obtain ⟨w, hwL, hwk, hw⟩ := hchild p hp.1 hpne M hM n hn hPM hML
  refine ⟨w, hwL, hwk, hw, ?_⟩
  intro q v' w' hpre
  rcases List.prefix_concat_iff.1 hpre with heq | hpre'
  · have h1 : (q ++ [v']) ++ [w'] = p ++ [w] := by simpa using heq
    obtain ⟨rfl, h2⟩ := List.append_inj' h1 rfl
    simp only [List.cons.injEq, and_true] at h2
    subst h2
    simp only [List.getLast_append_singleton] at hc
    rw [hwL, hwk]; exact hc
  · exact hp.2 q v' w' hpre'

/-- Monotone ⇒ broad: duplicate vertices for the equal-language children `(L_v, n)`, `n ≤ k_v`.
The vertices of the new tree are coded over the monotone paths (`build`, `Valid`); the radius at
depth `i` is `a_{e(w)} + i`; feasibility follows from `collapse` with the effective-index map. -/
lemma mono_to_broad {d : ℕ} {X : Set (Set (Pt d))} {h : ℕ → ℝ} {α : Set (Pt d) → ℝ}
    {K : Set (Pt d)} {k : ℕ} {T : DTree d} (hT : IsCopyProtectedTree X h α K k T) :
    ∃ T', IsBroadCopyProtectedTree X h α K k T' := by
  obtain ⟨hroot, hk, hvert, hedge, hchild, hfeas⟩ := hT
  have hqne : ∀ q ∈ T.paths, q ≠ [] := fun q hq h0 => by
    have := dtree_head T q hq; simp [h0] at this
  have hq0 : ∀ q ∈ T.paths, dat q 0 = T.root := by
    intro q hq; have := dtree_head T q hq
    cases q with
    | nil => simp at this
    | cons x t => simp at this; simp [dat, this]
  have hmono : ∀ q ∈ T.paths, ∀ i j (hij : i ≤ j) (hj : j < q.length),
      (q[j]).L ⊆ (q[i]'(by omega)).L ∧ (q[i]'(by omega)).a ≤ q[j].a := by
    intro q hq i j hij hj
    exact rel_of_step q (fun x y => y.L ⊆ x.L ∧ x.a ≤ y.a) (fun x => ⟨subset_rfl, le_rfl⟩)
      (fun x y z h1 h2 => ⟨h2.1.trans h1.1, h1.2.trans h2.2⟩)
      (path_step_rel T (fun x y => y.L ⊆ x.L ∧ x.a ≤ y.a) (fun q v w hqvw =>
        ⟨(hedge q v w hqvw).1.2.2.1, (hedge q v w hqvw).2.le⟩) q hq) i j hij hj
  let root' : Deco d := Deco.mk T.root.L T.root.k T.root.P T.root.s T.root.a
  let P' : Set (List (Deco d)) := {ws | ∃ q ∈ T.paths, ∃ cs, Valid q cs ∧ ws = build q cs}
  have hroot_mem : [root'] ∈ P' := by
    refine ⟨[T.root], dtree_root_mem T, [(0, T.root.k)], ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [dat]
    · intro c hc
      simp only [List.mem_singleton] at hc
      subst hc
      simp only [dat, List.length_singleton, List.getElem?_singleton]
      exact ⟨by omega, (hvert _ (dtree_root_mem T) T.root (by simp)).2.2.2.2, le_rfl⟩
    · simp
    · intro _; simp
    · simp [build, cdeco, dat, root']
  have hhead : ∀ ws ∈ P', ws.head? = some root' := by
    rintro ws ⟨q, hq, cs, ⟨hh, -⟩, rfl⟩
    simp only [build, List.head?_mapIdx, hh, Option.map_some]
    simp [cdeco, hq0 q hq, root']
  have hprefix : ∀ ws ∈ P', ∀ n, 1 ≤ n → ws.take n ∈ P' := by
    rintro ws ⟨q, hq, cs, ⟨hh, hb, hpw, hl⟩, rfl⟩ n hn
    have hcsne : cs ≠ [] := by rintro rfl; simp at hh
    have hcs'ne : cs.take n ≠ [] := by
      rw [Ne, List.take_eq_nil_iff]
      rintro (h0 | h0)
      · omega
      · exact hcsne h0
    have hpw' : (cs.take n).Pairwise (fun c c' => c.1 ≤ c'.1) := hpw.sublist (List.take_sublist _ _)
    have hsub : ∀ c ∈ cs.take n, c ∈ cs := fun c hc => List.mem_of_mem_take hc
    have hjl : ((cs.take n).getLast hcs'ne).1 < q.length := (hb _ (hsub _ (List.getLast_mem _))).1
    have hle : ∀ c ∈ cs.take n, c.1 ≤ ((cs.take n).getLast hcs'ne).1 := le_last hpw' hcs'ne
    refine ⟨q.take (((cs.take n).getLast hcs'ne).1 + 1), dtree_prefix T q hq _ (by omega),
      cs.take n, ⟨?_, ?_, hpw', ?_⟩, ?_⟩
    · rw [dat_take (by omega), List.head?_take]
      simp [show n ≠ 0 by omega, hh]
    · intro c hc
      obtain ⟨h1, h2, h3⟩ := hb c (hsub c hc)
      have := hle c hc
      refine ⟨?_, h2, ?_⟩
      · simp only [List.length_take]; omega
      · rw [dat_take (by omega)]; exact h3
    · intro _; simp only [List.length_take]; omega
    · rw [build_take]
      exact build_congr _ _ _ (fun c hc => (dat_take (by have := hle c hc; omega)).symm)
  have hcount : P'.Countable := by
    have : P' ⊆ (fun x : List (Deco d) × List (ℕ × ℕ) => build x.1 x.2) ''
        (T.paths ×ˢ Set.univ) := by
      rintro ws ⟨q, hq, cs, -, rfl⟩; exact ⟨(q, cs), ⟨hq, trivial⟩, rfl⟩
    exact (((dtree_countable T).prod Set.countable_univ).image _).mono this
  let T' : DTree d := DTree.mk P' root' hroot_mem hhead hprefix hcount
  refine ⟨T', hroot, hk, ?_, ?_, ?_, ?_⟩
  · -- vertex data
    rintro ws ⟨q, hq, cs, ⟨hh, hb, hpw, hl⟩, rfl⟩ v hv
    simp only [build, List.mem_mapIdx] at hv
    obtain ⟨i, hi, rfl⟩ := hv
    obtain ⟨h1, h2, h3⟩ := hb cs[i] (List.getElem_mem _)
    have hu := hvert q hq (dat q cs[i].1) (by rw [dat_eq h1]; exact List.getElem_mem _)
    simp only [cdeco, mk_L, mk_P, mk_s, mk_a, mk_k]
    exact ⟨hu.1, hu.2.1, hu.2.2.1, by have := hu.2.2.2.1; positivity, h2⟩
  · -- edges
    rintro p v w ⟨q, hq, cs, ⟨hh, hb, hpw, hl⟩, heq⟩
    have hlen : cs.length = p.length + 2 := by
      have := congrArg List.length heq; simp at this; omega
    have hv : (build q cs)[p.length]? = some v := by rw [← heq]; simp
    have hw : (build q cs)[p.length + 1]? = some w := by rw [← heq]; simp
    rw [List.getElem?_eq_getElem (by simp; omega), build_getElem, Option.some_inj] at hv hw
    subst hv hw
    have hle : cs[p.length].1 ≤ cs[p.length + 1].1 :=
      List.pairwise_iff_getElem.1 hpw _ _ (by omega) (by omega) (by omega)
    have hb1 := (hb _ (List.getElem_mem (l := cs) (n := p.length) (by omega))).1
    have hb2 := (hb _ (List.getElem_mem (l := cs) (n := p.length + 1) (by omega))).1
    obtain ⟨m1, m2⟩ := hmono q hq _ _ hle hb2
    simp only [cdeco, mk_L, mk_a]
    rw [dat_eq hb1, dat_eq hb2]
    refine ⟨m1, ?_⟩
    push_cast
    linarith
  · -- children: every broad-compatible copy
    rintro ws ⟨q, hq, cs, ⟨hh, hb, hpw, hl⟩, rfl⟩ hwsne M hM n hn hPM hML
    have hcsne : cs ≠ [] := by rintro rfl; simp at hh
    have hqne' := hqne q hq
    have hlastc := hl hcsne
    have hlast : (build q cs).getLast hwsne = cdeco q (cs.length - 1) (cs.getLast hcsne) := by
      simp [build]
    have hvq : dat q (q.length - 1) = q.getLast hqne' := by
      rw [dat_eq (by have := List.length_pos_iff.2 hqne'; omega), List.getLast_eq_getElem]
    rw [hlast] at hPM hML
    simp only [cdeco, mk_L, mk_P, hlastc, hvq] at hPM hML
    by_cases hdup : M = (q.getLast hqne').L ∧ n ≤ (q.getLast hqne').k
    · refine ⟨cdeco q cs.length (q.length - 1, n), ?_, ?_, ?_⟩
      · simp [cdeco, hvq, hdup.1]
      · simp [cdeco]
      · refine ⟨q, hq, cs ++ [(q.length - 1, n)], ⟨?_, ?_, ?_, ?_⟩, ?_⟩
        · simp [List.head?_append, hh]
        · intro c hc
          rcases List.mem_append.1 hc with hc | hc
          · exact hb c hc
          · simp only [List.mem_singleton] at hc
            subst hc
            have := List.length_pos_iff.2 hqne'
            refine ⟨by simp only; omega, hn, ?_⟩
            simp only [hvq]; exact hdup.2
        · rw [List.pairwise_append]
          refine ⟨hpw, by simp, ?_⟩
          intro a ha b hb'
          simp only [List.mem_singleton] at hb'
          subst hb'
          have := (hb a ha).1
          simp only; omega
        · intro _; simp
        · rw [build_append]
    · have hcomp : CompatibleCopy (↑(q.getLast hqne').P) (q.getLast hqne').L
          (q.getLast hqne').k M n := by
        refine ⟨hn, hPM, hML, ?_⟩
        by_cases hMv : M = (q.getLast hqne').L
        · right; exact ⟨hMv, by have := not_and.1 hdup hMv; omega⟩
        · left; exact Set.ssubset_iff_subset_ne.2 ⟨hML, hMv⟩
      obtain ⟨w0, hw0L, hw0k, hw0⟩ := hchild q hq hqne' M hM n hcomp
      have hd : dat (q ++ [w0]) q.length = w0 := by simp [dat]
      refine ⟨cdeco (q ++ [w0]) cs.length (q.length, n), ?_, ?_, ?_⟩
      · simp [cdeco, hd, hw0L]
      · simp [cdeco]
      · refine ⟨q ++ [w0], hw0, cs ++ [(q.length, n)], ⟨?_, ?_, ?_, ?_⟩, ?_⟩
        · have := List.length_pos_iff.2 hqne'
          rw [dat_append this]
          simp [List.head?_append, hh]
        · intro c hc
          rcases List.mem_append.1 hc with hc | hc
          · obtain ⟨h1, h2, h3⟩ := hb c hc
            refine ⟨by simp; omega, h2, ?_⟩
            rw [dat_append h1]; exact h3
          · simp only [List.mem_singleton] at hc
            subst hc
            refine ⟨by simp, hn, ?_⟩
            simp only [hd, hw0k]; exact le_rfl
        · rw [List.pairwise_append]
          refine ⟨hpw, by simp, ?_⟩
          intro a ha b hb'
          simp only [List.mem_singleton] at hb'
          subst hb'
          have := (hb a ha).1
          simp only; omega
        · intro _; simp
        · rw [build_append, build_congr q (q ++ [w0]) cs
            (fun c hc => (dat_append (hb c hc).1).symm)]
  · -- feasibility along every path, by collapsing onto the effective monotone path
    rintro ws ⟨q, hq, cs, ⟨hh, hb, hpw, hl⟩, rfl⟩ hws
    have hqne' := hqne q hq
    have hcsne : cs ≠ [] := by rintro rfl; simp at hh
    have hcpos := List.length_pos_iff.2 hcsne
    have hqpos := List.length_pos_iff.2 hqne'
    have hF := hfeas q hq hqne'
    let cm : Fin ((build q cs).length - 1 + 1) → Fin (q.length - 1 + 1) := fun i =>
      ⟨(cs[i.val]'(by have := i.isLt; simp at this ⊢; omega)).1, by
        have := (hb _ (List.getElem_mem (l := cs) (n := i.val)
          (by have := i.isLt; simp at this ⊢; omega))).1
        omega⟩
    have hcm : ∀ i, (cm i).val = (cs[i.val]'(by have := i.isLt; simp at this ⊢; omega)).1 :=
      fun _ => rfl
    have hbi : ∀ i : Fin ((build q cs).length - 1 + 1),
        (cs[i.val]'(by have := i.isLt; simp at this ⊢; omega)).1 < q.length := fun i =>
      (hb _ (List.getElem_mem _)).1
    refine collapse h _ _ _ _ _ _ _ _ cm cm ?_ ?_ ?_ ?_ (fun _ => le_rfl) ?_ ?_ ?_ hF
    · intro i
      simp only [pathFn, List.get_eq_getElem, build_getElem, cdeco, mk_L, hcm, dat_eq (hbi i)]
    · intro i
      simp only [pathFn, List.get_eq_getElem, build_getElem, cdeco, mk_L, hcm, dat_eq (hbi i)]
    · intro i
      have hbb := hb _ (List.getElem_mem (l := cs) (n := i.val)
        (by have := i.isLt; simp at this ⊢; omega))
      simp only [pathFn, List.get_eq_getElem, build_getElem, cdeco, mk_L, mk_k, hcm,
        dat_eq (hbi i)]
      rw [dat_eq (hbi i)] at hbb
      exact copyQuota_mono α _ hbb.2.1 hbb.2.2
    · intro i
      simp only [pathFn, List.get_eq_getElem, build_getElem, cdeco, mk_s, hcm, dat_eq (hbi i)]
    · intro x y hxy
      rw [Fin.le_def, hcm, hcm]
      rw [Fin.le_def] at hxy
      rcases Nat.lt_or_eq_of_le hxy with hlt | heq
      · exact List.pairwise_iff_getElem.1 hpw _ _ _ _ hlt
      · simp only [heq]; exact le_rfl
    · apply Fin.ext
      rw [hcm]
      have := hl hcsne
      rw [List.getLast_eq_getElem] at this
      simp only [Fin.val_last, build_length]
      exact this
    · have hlast : (build q cs).getLast hws = cdeco q (cs.length - 1) (cs.getLast hcsne) := by
        simp [build]
      rw [hlast]
      simp only [cdeco, mk_a, hl hcsne]
      rw [dat_eq (by omega), ← List.getLast_eq_getElem hqne']
      have : (0 : ℝ) ≤ ((cs.length - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith

end TreesAux

/-- **Broad/monotone copy bridge**: for every root copy `(K,k)`, a protected tree on copies with the
manuscript's broad copy relation (`IsBroadCopyProtectedTree`, Definition 8.14 as written)
exists if and only if one with the monotone relation (`IsCopyProtectedTree`, alternative monotone formulation) exists. The proof combines `TreesAux.broad_to_mono` and
`TreesAux.mono_to_broad`. The latter constructs the duplicated tree and obtains feasibility
from `TreesAux.collapse` with its effective-index map. 
-/
theorem copyTree_broad_iff_monotone {d : ℕ} (X : Set (Set (Pt d))) (h : ℕ → ℝ)
    (α : Set (Pt d) → ℝ) (K : Set (Pt d)) (k : ℕ) :
    (∃ T, IsBroadCopyProtectedTree X h α K k T) ↔ ∃ T, IsCopyProtectedTree X h α K k T := by
  exact ⟨fun ⟨_, hT⟩ => TreesAux.broad_to_mono hT, fun ⟨_, hT⟩ => TreesAux.mono_to_broad hT⟩

/-- A chain `H = (L₀ ⊋ ⋯ ⊋ L_r)` is geometrically `q`-feasible at the cutoffs `s_{H₀},…,s_{H_r}`
of its prefixes `Hᵢ`, outside `Q_{a_H}` (Definitions 8.6 and the `Θ`-goodness of Cor 8.8). -/
def DecoratedGood {d : ℕ} (h : ℕ → ℝ) (q : Set (Pt d) → ℝ) (s a : List (Set (Pt d)) → ℝ)
    (H : List (Set (Pt d))) (hH : H ≠ []) : Prop :=
  GeomFeasible h (listFn H hH) (fun i => q (listFn H hH i))
    (fun i => s (H.take (i.val + 1))) (a H)

/-- **Definition 8.6** (`def:q-good-decoration`): `U ⊆ 𝓗_K` is an open neighbourhood of `(K)`
**closed under taking prefixes** (Q9), and `(s, a)` is a `q`-good geometric decoration of it. -/
def IsQGoodDecoration {d : ℕ} (X : Set (Set (Pt d))) (h : ℕ → ℝ) (q : Set (Pt d) → ℝ)
    (K : Set (Pt d)) (hK : K ∈ X) (U : Set (History X)) (s a : List (Set (Pt d)) → ℝ) : Prop :=
  U ⊆ historiesFrom X K ∧ IsOpen U ∧ History.single K hK ∈ U ∧
  (∀ H ∈ U, ∀ n, 1 ≤ n → ∀ hc : IsChain X (H.1.take n), (⟨H.1.take n, hc⟩ : History X) ∈ U) ∧
  (∀ H ∈ U, 1 ≤ s H.1 ∧ 0 ≤ a H.1) ∧
  (∀ H ∈ U, ∀ Γ ∈ U, ∀ M, History.IsSnoc H Γ M → a H.1 < a Γ.1) ∧
  (∀ H ∈ U, DecoratedGood h q s a H.1 H.2.1)


end BanachDensityHD
