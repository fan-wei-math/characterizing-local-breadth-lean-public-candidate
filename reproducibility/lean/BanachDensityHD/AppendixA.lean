import BanachDensityHD.Characterization

/-!
# Appendix A: the potential proof of the finite rectangle game

Kleinberg–Wei, *Characterizing Local Breadth in Language Generation*.
Historical source numbering is retained; current mappings are in the release registry.

-/

namespace BanachDensityHD

open Set Filter
open scoped Classical

noncomputable section



/-! ## A.1 The abstract game on a tree of regions -/

/-- A finite tree of spatial regions with local requirements (§A.1): vertices `V` (finite), a dummy
root, parent pointers, depths, the game points `E_v` of each vertex, the local requirements
`𝒜_v` (finite sets `Q ⊆ E_v`) and their quotas `a_Q`. The structural conditions are the separate
predicate `RegionTree.WellFormed`. -/
inductive RegionTree (d : ℕ) : Type 1
  | mk (V : Type) [Fintype V] [DecidableEq V] (root : V) (parent : V → Option V) (depth : V → ℕ)
      (E : V → Finset (Pt d)) (reqs : V → Finset (Finset (Pt d))) (quota : V → Finset (Pt d) → ℝ)

/-- The vertex type. -/
def RegionTree.V {d : ℕ} : RegionTree d → Type
  | @RegionTree.mk _ V _ _ _ _ _ _ _ _ => V

/-- The vertex type is finite. -/
instance RegionTree.instFintypeV {d : ℕ} : (T : RegionTree d) → Fintype T.V
  | @RegionTree.mk _ _ fin _ _ _ _ _ _ _ => fin

/-- Vertices have decidable equality. -/
instance RegionTree.instDecidableEqV {d : ℕ} : (T : RegionTree d) → DecidableEq T.V
  | @RegionTree.mk _ _ _ deq _ _ _ _ _ _ => deq

/-- The dummy root. -/
def RegionTree.root {d : ℕ} : (T : RegionTree d) → T.V
  | @RegionTree.mk _ _ _ _ root _ _ _ _ _ => root

/-- The stored parent pointer of a vertex. For arbitrary constructor data no root condition
is imposed; `RegionTree.WellFormed` requires the root's parent to be `none`. -/
def RegionTree.parent {d : ℕ} : (T : RegionTree d) → T.V → Option T.V
  | @RegionTree.mk _ _ _ _ _ parent _ _ _ _ => parent

/-- The depth of a vertex. -/
def RegionTree.depth {d : ℕ} : (T : RegionTree d) → T.V → ℕ
  | @RegionTree.mk _ _ _ _ _ _ depth _ _ _ => depth

/-- The game points `E_v` of a vertex. -/
def RegionTree.E {d : ℕ} : (T : RegionTree d) → T.V → Finset (Pt d)
  | @RegionTree.mk _ _ _ _ _ _ _ E _ _ => E

/-- The local requirements `𝒜_v` of a vertex. -/
def RegionTree.reqs {d : ℕ} : (T : RegionTree d) → T.V → Finset (Finset (Pt d))
  | @RegionTree.mk _ _ _ _ _ _ _ _ reqs _ => reqs

/-- The quota `a_Q` of a requirement `Q` at a vertex. -/
def RegionTree.quota {d : ℕ} : (T : RegionTree d) → T.V → Finset (Pt d) → ℝ
  | @RegionTree.mk _ _ _ _ _ _ _ _ _ quota => quota

namespace RegionTree
variable {d : ℕ} (T : RegionTree d)

/-- `a` is an ancestor of `v`, or `v` itself. -/
inductive Anc : T.V → T.V → Prop
  | refl (v : T.V) : Anc v v
  | step {a u v : T.V} : Anc a u → T.parent v = some u → Anc a v

/-- `a` is a proper ancestor of `v`. -/
def StrictAnc (a v : T.V) : Prop := T.Anc a v ∧ a ≠ v

/-- The tree conditions of §A.1: the root has no parent and depth `0`; every other vertex has a
parent one level less deep; a child's points lie in its parent's; distinct children of one vertex
have disjoint points; every requirement at `v` lies in `E_v`. (The board of the game is by
definition the root's points `E root`.) -/
def WellFormed : Prop :=
  T.parent T.root = none ∧ T.depth T.root = 0 ∧
  (∀ v, v ≠ T.root → ∃ u, T.parent v = some u ∧ T.depth v = T.depth u + 1) ∧
  (∀ v u, T.parent v = some u → T.E v ⊆ T.E u) ∧
  (∀ v w u, T.parent v = some u → T.parent w = some u → v ≠ w → Disjoint (T.E v) (T.E w)) ∧
  (∀ v, ∀ Q ∈ T.reqs v, Q ⊆ T.E v)

/-- The bookkeeping state: Black's and White's points, the active vertices, and the White credits
of each requirement. -/
inductive State
  | mk (black white : Finset (Pt d)) (active : Finset T.V) (credit : T.V → Finset (Pt d) → ℕ)

/-- Black's points. -/
def State.black {T : RegionTree d} : T.State → Finset (Pt d)
  | .mk black _ _ _ => black

/-- White's points. -/
def State.white {T : RegionTree d} : T.State → Finset (Pt d)
  | .mk _ white _ _ => white

/-- The active vertices. -/
def State.active {T : RegionTree d} : T.State → Finset T.V
  | .mk _ _ active _ => active

/-- The White credits of each requirement. -/
def State.credit {T : RegionTree d} : T.State → T.V → Finset (Pt d) → ℕ
  | .mk _ _ _ credit => credit

/-- The initial state: only the dummy root is active. -/
def init : T.State := ⟨∅, ∅, {T.root}, fun _ _ => 0⟩

/-- `E_v^*` (eq. new-effective): the points of `E_v` not in any active proper descendant. -/
def eff (st : T.State) (v : T.V) : Finset (Pt d) :=
  (T.E v).filter fun x => ∀ u ∈ st.active, T.StrictAnc v u → x ∉ T.E u

/-- `x` is unused. -/
def Unused (st : T.State) (x : Pt d) : Prop := x ∉ st.black ∧ x ∉ st.white

/-- A Black claim at `x`. -/
def blackClaim (st : T.State) (x : Pt d) : T.State :=
  ⟨insert x st.black, st.white, st.active, st.credit⟩

/-- A White claim at `y`: every requirement `Q ∈ 𝒜_v` containing `y` with `y ∈ E_v^*` is credited. -/
def whiteClaim (st : T.State) (y : Pt d) : T.State :=
  ⟨st.black, insert y st.white, st.active, fun v Q =>
    if Q ∈ T.reqs v ∧ y ∈ Q ∧ y ∈ T.eff st v then st.credit v Q + 1 else st.credit v Q⟩

/-- Activation of `u`. -/
def activate (st : T.State) (u : T.V) : T.State :=
  ⟨st.black, st.white, insert u st.active, st.credit⟩

/-- `r_Q`: the quota minus the credits (it may be negative). -/
def outstanding (st : T.State) (v : T.V) (Q : Finset (Pt d)) : ℝ := T.quota v Q - st.credit v Q

variable (Pot : T.V → T.State → ℝ)

/-- The score of an unused `x` at `v` (eq. svx): the increase of `P_v` if Black claimed `x`
(active vertices unchanged); `0` for `x ∉ E_v^*`. -/
def score (st : T.State) (v : T.V) (x : Pt d) : ℝ :=
  if x ∈ T.eff st v then Pot v (T.blackClaim st x) - Pot v st else 0

/-- `M_v`: the largest score of an unused point of `E_v^*` (`0` if none). -/
noncomputable def maxScore (st : T.State) (v : T.V) : ℝ :=
  let S := (T.eff st v).filter fun x => T.Unused st x
  if h : S.Nonempty then (S.image (T.score Pot st v)).max' (h.image _) else 0

/-- `I_v = P_v + M_v`, the reserve. -/
noncomputable def reserve (st : T.State) (v : T.V) : ℝ := Pot v st + T.maxScore Pot st v

/-- The states generated from the initial state by Black or White claims of unused board points,
in any order, and by activating any vertex at any time: a superset of the states play reaches.
(P1)–(P4) are required at all of them (whether this is stronger than the paper is an open DEFER);
a hypothetical claim from such a state is again one. -/
inductive Reachable : T.State → Prop
  | init : Reachable T.init
  | black {st : T.State} {x : Pt d} : Reachable st → x ∈ T.E T.root → T.Unused st x →
      Reachable (T.blackClaim st x)
  | white {st : T.State} {y : Pt d} : Reachable st → y ∈ T.E T.root → T.Unused st y →
      Reachable (T.whiteClaim st y)
  | act {st : T.State} {u : T.V} : Reachable st → Reachable (T.activate st u)

/-- The locality properties and **(P1)–(P4)** of §A.2, for a constant `0 < σ ≤ 1/16`, at every
reachable state: potentials are nonnegative (tex l. 6218); a claim outside `E_v^*` leaves `P_v`
unchanged; activating `u` changes potentials only at strict ancestors of `u`; (P1) small initial
potentials and detection of unmet quotas; (P2) one Black move has a small effect, and a White claim
never increases a potential; (P3) White's advantage; (P4) for **every** ancestor `v` of an inactive
`u` with pre-move potential at least `1/12`, a Black claim in `E_u^*` followed by the activation of
`u` increases neither `P_v` nor the reserve `I_v` (ancestors separated from `u` by an active vertex
are unaffected, which this includes). -/
structure PotentialProps (σ : ℝ) : Prop where
  sigma : 0 < σ ∧ σ ≤ 1 / 16
  nonneg : ∀ st, T.Reachable st → ∀ v, 0 ≤ Pot v st
  loc_black : ∀ st, T.Reachable st → ∀ v x, x ∉ T.eff st v → Pot v (T.blackClaim st x) = Pot v st
  loc_white : ∀ st, T.Reachable st → ∀ v y, y ∉ T.eff st v → Pot v (T.whiteClaim st y) = Pot v st
  loc_act : ∀ st, T.Reachable st → ∀ u v, ¬ T.StrictAnc v u → Pot v (T.activate st u) = Pot v st
  p1_init : ∀ v, Pot v T.init ≤ 1 / 16
  p1_detect : ∀ st, T.Reachable st → ∀ v, (∀ x ∈ T.E T.root, x ∈ st.black ∨ x ∈ st.white) →
    (∃ Q ∈ T.reqs v, 0 < T.outstanding st v Q) → 1 ≤ Pot v st
  p2 : ∀ st, T.Reachable st → ∀ v, (∀ u, T.Anc v u → Pot u st ≤ 1 / 4) →
    ∀ x ∈ T.eff st v, T.Unused st x →
      0 ≤ T.score Pot st v x ∧ T.score Pot st v x ≤ σ * Pot v st
  p2_white : ∀ st, T.Reachable st → ∀ u y, Pot u (T.whiteClaim st y) ≤ Pot u st
  p3 : ∀ st, T.Reachable st → ∀ v, (∀ u, T.Anc v u → Pot u st ≤ 1 / 4) →
    ∀ y ∈ T.eff st v, T.Unused st y →
      (1 + 8 * σ) * T.score Pot st v y ≤ Pot v st - Pot v (T.whiteClaim st y) ∧
      ∀ x ∈ T.eff st v, T.Unused st x → x ≠ y →
        T.score Pot (T.whiteClaim st y) v x ≤ (1 + 2 * σ) * T.score Pot st v x
  p4 : ∀ st, T.Reachable st → ∀ u x, u ∉ st.active → 1 / 12 ≤ Pot u st → x ∈ T.eff st u →
    T.Unused st x → ∀ v, T.StrictAnc v u →
      Pot v (T.activate (T.blackClaim st x) u) ≤ Pot v st ∧
      T.reserve Pot (T.activate (T.blackClaim st x) u) v ≤ T.reserve Pot st v

/-- **Definition A.1** (`def:activate`): after Black claims, with the active set unchanged, if some
inactive vertex now has potential at least `1/8`, activate the deepest such vertex (ties broken by
a fixed choice). -/
noncomputable def activationStep (st : T.State) : T.State :=
  let C := Finset.univ.filter fun u => u ∉ st.active ∧ 1 / 8 ≤ Pot u st
  if h : C.Nonempty then T.activate st (Classical.choose (C.exists_max_image T.depth h)) else st

/-- The responsible vertex for a Black claim at `x`: the deepest active vertex whose points contain
`x` (the root if none). -/
noncomputable def responsible (st : T.State) (x : Pt d) : T.V :=
  let C := st.active.filter fun u => x ∈ T.E u
  if h : C.Nonempty then Classical.choose (C.exists_max_image T.depth h) else T.root

/-- White's reply (§A.2, "White's strategy"): a point of `E_v^*` maximizing the score at the
responsible vertex `v` (ties broken by a fixed choice), or a pass if none is unused. -/
noncomputable def reply (st : T.State) (v : T.V) : Option (Pt d) :=
  let S := (T.eff st v).filter fun y => T.Unused st y
  if h : S.Nonempty then some (Classical.choose (S.exists_max_image (T.score Pot st v) h)) else none

/-- One round of the potential strategy: Black claims `x`; activation (Definition A.1); White
replies at the responsible vertex; the accounting is updated. -/
noncomputable def round (st : T.State) (x : Pt d) : T.State × Option (Pt d) :=
  let st₁ := T.activationStep Pot (T.blackClaim st x)
  let rep := T.reply Pot st₁ (T.responsible st₁ x)
  (rep.elim st₁ (T.whiteClaim st₁ ·), rep)

/-- The state after Black's claims `bs` (in order), with the potential strategy replying. -/
noncomputable def run (bs : List (Pt d)) : T.State :=
  bs.foldl (fun st x => (T.round Pot st x).1) T.init

/-- A legal Black sequence: each claim is an unused point of the board. -/
def LegalBlack (bs : List (Pt d)) : Prop :=
  ∀ k (hk : k < bs.length), bs.get ⟨k, hk⟩ ∈ T.E T.root ∧
    T.Unused (T.run Pot (bs.take k)) (bs.get ⟨k, hk⟩)

end RegionTree

namespace AppendixAAux
open RegionTree

variable {d : ℕ} {T : RegionTree d}

/-! ### Helpers (appA2): states, ancestry and the potential strategy (Lemma A.2) -/

theorem state_ext {s t : T.State} (h1 : s.black = t.black) (h2 : s.white = t.white)
    (h3 : s.active = t.active) (h4 : s.credit = t.credit) : s = t := by
  rcases s with ⟨b, w, a, c⟩
  rcases t with ⟨b', w', a', c'⟩
  change b = b' at h1; change w = w' at h2; change a = a' at h3; change c = c' at h4
  subst h1 h2 h3 h4; rfl

theorem blackClaim_comm (st : T.State) (x z : Pt d) :
    T.blackClaim (T.blackClaim st x) z = T.blackClaim (T.blackClaim st z) x :=
  state_ext (Finset.insert_comm _ _ _) rfl rfl rfl

theorem blackClaim_whiteClaim (st : T.State) (y z : Pt d) :
    T.blackClaim (T.whiteClaim st y) z = T.whiteClaim (T.blackClaim st z) y := rfl

theorem blackClaim_activate (st : T.State) (u : T.V) (z : Pt d) :
    T.blackClaim (T.activate st u) z = T.activate (T.blackClaim st z) u := rfl

theorem eff_congr {s t : T.State} (h : s.active = t.active) (v : T.V) : T.eff s v = T.eff t v := by
  unfold RegionTree.eff; rw [h]

theorem mem_eff {st : T.State} {v : T.V} {x : Pt d} :
    x ∈ T.eff st v ↔ x ∈ T.E v ∧ ∀ u ∈ st.active, T.StrictAnc v u → x ∉ T.E u := by
  unfold RegionTree.eff; simp

theorem eff_sub (st : T.State) (v : T.V) : T.eff st v ⊆ T.E v := Finset.filter_subset _ _

/-! #### Ancestry in a well-formed tree -/

theorem parent_depth (hT : T.WellFormed) {v u : T.V} (h : T.parent v = some u) :
    T.depth v = T.depth u + 1 := by
  by_cases hv : v = T.root
  · subst hv; rw [hT.1] at h; cases h
  · obtain ⟨u', hu', hd⟩ := hT.2.2.1 v hv
    rw [h] at hu'; cases hu'; exact hd

theorem anc_eq_or_lt (hT : T.WellFormed) {a v : T.V} (h : T.Anc a v) :
    a = v ∨ T.depth a < T.depth v := by
  induction h with
  | refl => exact Or.inl rfl
  | step _ hp ih =>
    right; rw [parent_depth hT hp]
    rcases ih with rfl | h <;> omega

theorem strictAnc_depth (hT : T.WellFormed) {a v : T.V} (h : T.StrictAnc a v) :
    T.depth a < T.depth v := by
  rcases anc_eq_or_lt hT h.1 with h' | h'
  · exact absurd h' h.2
  · exact h'

theorem anc_eq_of_depth (hT : T.WellFormed) {a v : T.V} (h : T.Anc a v)
    (hd : T.depth v ≤ T.depth a) : a = v := by
  rcases anc_eq_or_lt hT h with h' | h'
  · exact h'
  · omega

theorem anc_trans {a b c : T.V} (h1 : T.Anc a b) (h2 : T.Anc b c) : T.Anc a c := by
  induction h2 with
  | refl => exact h1
  | step _ hp ih => exact RegionTree.Anc.step ih hp

theorem E_anti (hT : T.WellFormed) {a v : T.V} (h : T.Anc a v) : T.E v ⊆ T.E a := by
  induction h with
  | refl => exact le_rfl
  | step _ hp ih => exact (hT.2.2.2.1 _ _ hp).trans ih

theorem anc_root (hT : T.WellFormed) : ∀ v : T.V, T.Anc T.root v := by
  intro v
  induction hn : T.depth v using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    by_cases hv : v = T.root
    · subst hv; exact RegionTree.Anc.refl _
    · obtain ⟨u, hu, hd⟩ := hT.2.2.1 v hv
      exact RegionTree.Anc.step (ih (T.depth u) (by omega) u rfl) hu

theorem E_sub_root (hT : T.WellFormed) (v : T.V) : T.E v ⊆ T.E T.root :=
  E_anti hT (anc_root hT v)

theorem eff_sub_root (hT : T.WellFormed) (st : T.State) (v : T.V) : T.eff st v ⊆ T.E T.root :=
  (eff_sub st v).trans (E_sub_root hT v)

/-- Two vertices whose point sets share a point are comparable. -/
theorem comparable (hT : T.WellFormed) {x : Pt d} :
    ∀ a b : T.V, x ∈ T.E a → x ∈ T.E b → T.Anc a b ∨ T.Anc b a := by
  intro a b
  induction hn : T.depth a + T.depth b using Nat.strong_induction_on generalizing a b with
  | _ n ih =>
    intro ha hb
    by_cases har : a = T.root
    · subst har; exact Or.inl (anc_root hT b)
    by_cases hbr : b = T.root
    · subst hbr; exact Or.inr (anc_root hT a)
    obtain ⟨pa, hpa, hda⟩ := hT.2.2.1 a har
    obtain ⟨pb, hpb, hdb⟩ := hT.2.2.1 b hbr
    have hxa : x ∈ T.E pa := hT.2.2.2.1 a pa hpa ha
    have hxb : x ∈ T.E pb := hT.2.2.2.1 b pb hpb hb
    rcases lt_trichotomy (T.depth a) (T.depth b) with h | h | h
    · rcases ih (T.depth a + T.depth pb) (by omega) a pb rfl ha hxb with h1 | h1
      · exact Or.inl (RegionTree.Anc.step h1 hpb)
      · have := anc_eq_of_depth hT h1 (by omega)
        subst this; exact Or.inl (RegionTree.Anc.step (RegionTree.Anc.refl _) hpb)
    · rcases ih (T.depth pa + T.depth pb) (by omega) pa pb rfl hxa hxb with h1 | h1
      · have := anc_eq_of_depth hT h1 (by omega)
        subst this
        by_cases hab : a = b
        · subst hab; exact Or.inl (RegionTree.Anc.refl _)
        · exact absurd (Finset.disjoint_left.1 (hT.2.2.2.2.1 a b pa hpa hpb hab) ha hb) (by simp)
      · have := anc_eq_of_depth hT h1 (by omega)
        subst this
        by_cases hab : a = b
        · subst hab; exact Or.inl (RegionTree.Anc.refl _)
        · exact absurd (Finset.disjoint_left.1 (hT.2.2.2.2.1 a b pb hpa hpb hab) ha hb) (by simp)
    · rcases ih (T.depth pa + T.depth b) (by omega) pa b rfl hxa hb with h1 | h1
      · have := anc_eq_of_depth hT h1 (by omega)
        subst this; exact Or.inr (RegionTree.Anc.step (RegionTree.Anc.refl _) hpa)
      · exact Or.inr (RegionTree.Anc.step h1 hpa)

/-- Two distinct active vertices never count the same point. -/
theorem not_mem_eff_of_active (hT : T.WellFormed) {st : T.State} {r w : T.V}
    (hr : r ∈ st.active) (hw : w ∈ st.active) (hne : w ≠ r) {y : Pt d}
    (hy : y ∈ T.eff st r) : y ∉ T.eff st w := by
  intro hyw
  have hyr := mem_eff.1 hy
  have hyw' := mem_eff.1 hyw
  rcases comparable hT w r hyw'.1 hyr.1 with h | h
  · exact hyw'.2 r hr ⟨h, hne⟩ hyr.1
  · exact hyr.2 w hw ⟨h, fun h' => hne h'.symm⟩ hyw'.1

theorem eff_activate_of_not {st : T.State} {u w : T.V} (h : ¬ T.StrictAnc w u) :
    T.eff (T.activate st u) w = T.eff st w := by
  ext x
  rw [mem_eff, mem_eff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun a ha => h2 a (Finset.mem_insert_of_mem ha)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a ha hwa => ?_⟩
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact absurd hwa h
    · exact h2 a ha hwa

theorem reachable_root_active {st : T.State} (h : T.Reachable st) : T.root ∈ st.active := by
  induction h with
  | init => exact Finset.mem_singleton_self _
  | black _ _ _ ih => exact ih
  | white _ _ _ ih => exact ih
  | act _ ih => exact Finset.mem_insert_of_mem ih

/-! #### Scores and reserves -/

variable (Pot : T.V → T.State → ℝ)

theorem score_of_mem {st : T.State} {v : T.V} {x : Pt d} (hx : x ∈ T.eff st v) :
    T.score Pot st v x = Pot v (T.blackClaim st x) - Pot v st := by
  unfold RegionTree.score; rw [if_pos hx]

theorem le_maxScore {st : T.State} {v : T.V} {x : Pt d} (hx : x ∈ T.eff st v)
    (hu : T.Unused st x) : T.score Pot st v x ≤ T.maxScore Pot st v := by
  have hmem : x ∈ (T.eff st v).filter (fun x => T.Unused st x) := Finset.mem_filter.2 ⟨hx, hu⟩
  unfold RegionTree.maxScore; dsimp only
  split_ifs with hne
  · exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ hmem)
  · exact absurd ⟨x, hmem⟩ hne

theorem maxScore_le {st : T.State} {v : T.V} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x ∈ T.eff st v, T.Unused st x → T.score Pot st v x ≤ c) : T.maxScore Pot st v ≤ c := by
  unfold RegionTree.maxScore; dsimp only
  split_ifs with hne
  · apply Finset.max'_le
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    have := Finset.mem_filter.1 hx
    exact h x this.1 this.2
  · exact hc

theorem maxScore_nonneg {st : T.State} {v : T.V}
    (h : ∀ x ∈ T.eff st v, T.Unused st x → 0 ≤ T.score Pot st v x) : 0 ≤ T.maxScore Pot st v := by
  unfold RegionTree.maxScore; dsimp only
  split_ifs with hne
  · obtain ⟨x, hx⟩ := hne
    have := Finset.mem_filter.1 hx
    exact (h x this.1 this.2).trans (Finset.le_max' _ _ (Finset.mem_image_of_mem _ hx))
  · exact le_rfl

theorem maxScore_eq_zero {st : T.State} {v : T.V}
    (h : ∀ x ∈ T.eff st v, ¬ T.Unused st x) : T.maxScore Pot st v = 0 := by
  unfold RegionTree.maxScore; dsimp only
  rw [dif_neg]
  rintro ⟨x, hx⟩
  have := Finset.mem_filter.1 hx
  exact h x this.1 this.2

theorem maxScore_mono {s t : T.State} {v : T.V} (h0 : 0 ≤ T.maxScore Pot s v)
    (h : ∀ x ∈ T.eff t v, T.Unused t x →
      x ∈ T.eff s v ∧ T.Unused s x ∧ T.score Pot t v x ≤ T.score Pot s v x) :
    T.maxScore Pot t v ≤ T.maxScore Pot s v :=
  maxScore_le Pot h0 fun x hx hu => by
    obtain ⟨h1, h2, h3⟩ := h x hx hu
    exact h3.trans (le_maxScore Pot h1 h2)

theorem reply_some {st : T.State} {v : T.V} {y : Pt d} (h : T.reply Pot st v = some y) :
    y ∈ T.eff st v ∧ T.Unused st y ∧
      ∀ x ∈ T.eff st v, T.Unused st x → T.score Pot st v x ≤ T.score Pot st v y := by
  unfold RegionTree.reply at h; dsimp only at h
  split_ifs at h with hne
  cases h
  obtain ⟨h1, h2⟩ := Classical.choose_spec
    (((T.eff st v).filter fun y => T.Unused st y).exists_max_image (T.score Pot st v) hne)
  have h1' := Finset.mem_filter.1 h1
  exact ⟨h1'.1, h1'.2, fun x hx hu => h2 x (Finset.mem_filter.2 ⟨hx, hu⟩)⟩

theorem reply_none {st : T.State} {v : T.V} (h : T.reply Pot st v = none) :
    ∀ x ∈ T.eff st v, ¬ T.Unused st x := by
  unfold RegionTree.reply at h; dsimp only at h
  split_ifs at h with hne
  intro x hx hu
  exact hne ⟨x, Finset.mem_filter.2 ⟨hx, hu⟩⟩

theorem responsible_spec {st : T.State} {x : Pt d} (hroot : T.root ∈ st.active)
    (hx : x ∈ T.E T.root) :
    T.responsible st x ∈ st.active ∧ x ∈ T.E (T.responsible st x) ∧
      ∀ w ∈ st.active, x ∈ T.E w → T.depth w ≤ T.depth (T.responsible st x) := by
  have hne : (st.active.filter fun u => x ∈ T.E u).Nonempty :=
    ⟨T.root, Finset.mem_filter.2 ⟨hroot, hx⟩⟩
  unfold RegionTree.responsible; dsimp only
  rw [dif_pos hne]
  obtain ⟨h1, h2⟩ := Classical.choose_spec
    ((st.active.filter fun u => x ∈ T.E u).exists_max_image T.depth hne)
  have h1' := Finset.mem_filter.1 h1
  exact ⟨h1'.1, h1'.2, fun w hw hxw => h2 w (Finset.mem_filter.2 ⟨hw, hxw⟩)⟩

theorem responsible_eff (hT : T.WellFormed) {st : T.State} {x : Pt d}
    (hroot : T.root ∈ st.active) (hx : x ∈ T.E T.root) : x ∈ T.eff st (T.responsible st x) := by
  obtain ⟨h1, h2, h3⟩ := responsible_spec (T := T) hroot hx
  refine mem_eff.2 ⟨h2, fun u hu hru hxu => ?_⟩
  have := h3 u hu hxu
  have := strictAnc_depth hT hru
  omega

theorem activationStep_cases (st : T.State) :
    ((∀ u, u ∉ st.active → Pot u st < 1 / 8) ∧ T.activationStep Pot st = st) ∨
    ∃ u, u ∉ st.active ∧ 1 / 8 ≤ Pot u st ∧
      (∀ w, w ∉ st.active → 1 / 8 ≤ Pot w st → T.depth w ≤ T.depth u) ∧
      T.activationStep Pot st = T.activate st u := by
  unfold RegionTree.activationStep; dsimp only
  split_ifs with hne
  · right
    obtain ⟨h1, h2⟩ := Classical.choose_spec ((Finset.univ.filter fun u => u ∉ st.active ∧
      1 / 8 ≤ Pot u st).exists_max_image T.depth hne)
    have h1' := (Finset.mem_filter.1 h1).2
    exact ⟨_, h1'.1, h1'.2, fun w hw hpw => h2 w (Finset.mem_filter.2 ⟨Finset.mem_univ _, hw, hpw⟩),
      rfl⟩
  · left
    refine ⟨fun u hu => ?_, rfl⟩
    by_contra hlt
    exact hne ⟨u, Finset.mem_filter.2 ⟨Finset.mem_univ _, hu, not_lt.1 hlt⟩⟩

/-! #### The round invariant (eq. new-invariant) -/

variable {Pot} {σ : ℝ}

/-- The invariant of the proof of Lemma A.2 after a completed round: the state is reachable, every
potential is at most `1/4`, active reserves are at most `1/4`, inactive potentials are below `1/8`,
and every requirement has at most as many credits as White points. -/
structure RoundInv (st : T.State) : Prop where
  reach : T.Reachable st
  pot : ∀ v, Pot v st ≤ 1 / 4
  res : ∀ v ∈ st.active, T.reserve Pot st v ≤ 1 / 4
  inact : ∀ v, v ∉ st.active → Pot v st < 1 / 8
  credit : ∀ v Q, st.credit v Q ≤ (st.white ∩ Q).card

theorem score_bounds (hP : T.PotentialProps Pot σ) {st : T.State} (hR : T.Reachable st)
    (hB : ∀ v, Pot v st ≤ 1 / 4) {v : T.V} {x : Pt d} (hx : x ∈ T.eff st v) (hu : T.Unused st x) :
    0 ≤ T.score Pot st v x ∧ T.score Pot st v x ≤ σ * Pot v st :=
  hP.p2 st hR v (fun u _ => hB u) x hx hu

theorem maxScore_bounds (hP : T.PotentialProps Pot σ) {st : T.State} (hR : T.Reachable st)
    (hB : ∀ v, Pot v st ≤ 1 / 4) (v : T.V) :
    0 ≤ T.maxScore Pot st v ∧ T.maxScore Pot st v ≤ σ * Pot v st :=
  ⟨maxScore_nonneg Pot fun x hx hu => (score_bounds hP hR hB hx hu).1,
    maxScore_le Pot (mul_nonneg hP.sigma.1.le (hP.nonneg st hR v))
      fun x hx hu => (score_bounds hP hR hB hx hu).2⟩

/-- A Black claim outside `E_w^*` does not increase the reserve at `w`. -/
theorem reserve_black_le (hT : T.WellFormed) (hP : T.PotentialProps Pot σ) {s : T.State}
    (hR : T.Reachable s) (hB : ∀ v, Pot v s ≤ 1 / 4) {w : T.V} {x : Pt d} (hx : x ∉ T.eff s w) :
    T.reserve Pot (T.blackClaim s x) w ≤ T.reserve Pot s w := by
  unfold RegionTree.reserve
  rw [hP.loc_black s hR w x hx]
  refine add_le_add le_rfl (maxScore_mono Pot (maxScore_bounds hP hR hB w).1 fun z hz hu => ?_)
  have hz' : z ∈ T.eff s w := hz
  have hus : T.Unused s z := ⟨fun h => hu.1 (Finset.mem_insert_of_mem h), hu.2⟩
  refine ⟨hz', hus, le_of_eq ?_⟩
  rw [score_of_mem Pot hz, score_of_mem Pot hz', blackClaim_comm,
    hP.loc_black _ (RegionTree.Reachable.black hR (eff_sub_root hT s w hz') hus) w x hx,
    hP.loc_black s hR w x hx]

/-- A White claim outside `E_w^*` does not increase the reserve at `w`. -/
theorem reserve_white_le (hT : T.WellFormed) (hP : T.PotentialProps Pot σ) {s : T.State}
    (hR : T.Reachable s) (hB : ∀ v, Pot v s ≤ 1 / 4) {w : T.V} {y : Pt d} (hy : y ∉ T.eff s w) :
    T.reserve Pot (T.whiteClaim s y) w ≤ T.reserve Pot s w := by
  unfold RegionTree.reserve
  rw [hP.loc_white s hR w y hy]
  refine add_le_add le_rfl (maxScore_mono Pot (maxScore_bounds hP hR hB w).1 fun z hz hu => ?_)
  have hz' : z ∈ T.eff s w := hz
  have hus : T.Unused s z := ⟨hu.1, fun h => hu.2 (Finset.mem_insert_of_mem h)⟩
  refine ⟨hz', hus, le_of_eq ?_⟩
  rw [score_of_mem Pot hz, score_of_mem Pot hz', blackClaim_whiteClaim,
    hP.loc_white _ (RegionTree.Reachable.black hR (eff_sub_root hT s w hz') hus) w y hy,
    hP.loc_white s hR w y hy]

/-- Activating `u` does not increase the reserve at a vertex that is not a strict ancestor of `u`. -/
theorem reserve_act_le (hT : T.WellFormed) (hP : T.PotentialProps Pot σ) {s : T.State}
    (hR : T.Reachable s) (hB : ∀ v, Pot v s ≤ 1 / 4) {w u : T.V} (hwu : ¬ T.StrictAnc w u) :
    T.reserve Pot (T.activate s u) w ≤ T.reserve Pot s w := by
  unfold RegionTree.reserve
  rw [hP.loc_act s hR u w hwu]
  refine add_le_add le_rfl (maxScore_mono Pot (maxScore_bounds hP hR hB w).1 fun z hz hu => ?_)
  have hz' : z ∈ T.eff s w := by rwa [eff_activate_of_not hwu] at hz
  have hus : T.Unused s z := hu
  refine ⟨hz', hus, le_of_eq ?_⟩
  rw [score_of_mem Pot hz, score_of_mem Pot hz', blackClaim_activate,
    hP.loc_act _ (RegionTree.Reachable.black hR (eff_sub_root hT s w hz') hus) u w hwu,
    hP.loc_act s hR u w hwu]

/-- White's step of a round: from the state after Black's claim and the activation step, White's
reply at the responsible vertex `r` restores the round invariant. -/
theorem white_step (hT : T.WellFormed) (hP : T.PotentialProps Pot σ) {s : T.State} {r : T.V}
    (hR : T.Reachable s) (hB : ∀ v, Pot v s ≤ 1 / 4) (hin : ∀ v, v ∉ s.active → Pot v s < 1 / 8)
    (hr : r ∈ s.active) (hres : ∀ w ∈ s.active, w ≠ r → T.reserve Pot s w ≤ 1 / 4)
    (hcr : ∀ v Q, s.credit v Q ≤ (s.white ∩ Q).card) :
    RoundInv (Pot := Pot) ((T.reply Pot s r).elim s (T.whiteClaim s ·)) := by
  rcases hrep : T.reply Pot s r with _ | y
  · -- White passes
    show RoundInv (Pot := Pot) s
    refine ⟨hR, hB, fun v hv => ?_, hin, hcr⟩
    by_cases hvr : v = r
    · subst hvr
      unfold RegionTree.reserve
      rw [maxScore_eq_zero Pot (reply_none Pot hrep), add_zero]
      exact hB v
    · exact hres v hv hvr
  · obtain ⟨hy, hyu, hymax⟩ := reply_some Pot hrep
    have hyE : y ∈ T.E T.root := eff_sub_root hT s r hy
    have hRW : T.Reachable (T.whiteClaim s y) := RegionTree.Reachable.white hR hyE hyu
    have hPW : ∀ v, Pot v (T.whiteClaim s y) ≤ Pot v s := fun v => hP.p2_white s hR v y
    show RoundInv (Pot := Pot) (T.whiteClaim s y)
    refine ⟨hRW, fun v => (hPW v).trans (hB v), fun v hv => ?_,
      fun v hv => (hPW v).trans_lt (hin v hv), fun v Q => ?_⟩
    · have hv' : v ∈ s.active := hv
      by_cases hvr : v = r
      · subst hvr
        obtain ⟨h3a, h3b⟩ := hP.p3 s hR v (fun u _ => hB u) y hy hyu
        have hsy := (score_bounds hP hR hB hy hyu).1
        have hσ := hP.sigma.1
        have hM : T.maxScore Pot (T.whiteClaim s y) v ≤ (1 + 2 * σ) * T.score Pot s v y := by
          refine maxScore_le Pot (by positivity) fun x hx hxu => ?_
          have hx' : x ∈ T.eff s v := hx
          have hxu' : T.Unused s x := ⟨hxu.1, fun h => hxu.2 (Finset.mem_insert_of_mem h)⟩
          have hxy : x ≠ y := fun h => hxu.2 (h ▸ Finset.mem_insert_self _ _)
          exact (h3b x hx' hxu' hxy).trans
            (mul_le_mul_of_nonneg_left (hymax x hx' hxu') (by linarith))
        unfold RegionTree.reserve
        have := hB v
        nlinarith
      · exact (reserve_white_le hT hP hR hB (not_mem_eff_of_active hT hr hv' hvr hy)).trans
          (hres v hv' hvr)
    · show (if Q ∈ T.reqs v ∧ y ∈ Q ∧ y ∈ T.eff s v then s.credit v Q + 1 else s.credit v Q) ≤
        (insert y s.white ∩ Q).card
      split_ifs with hc
      · rw [Finset.insert_inter_of_mem hc.2.1, Finset.card_insert_of_notMem
          (fun h => hyu.2 (Finset.mem_inter.1 h).1)]
        exact Nat.succ_le_succ (hcr v Q)
      · exact (hcr v Q).trans (Finset.card_le_card
          (Finset.inter_subset_inter (Finset.subset_insert _ _) le_rfl))

/-- One round of the potential strategy preserves the invariant (proof of Lemma A.2). -/
theorem round_inv (hT : T.WellFormed) (hP : T.PotentialProps Pot σ) {st : T.State}
    (hI : RoundInv (Pot := Pot) st) {x : Pt d} (hxE : x ∈ T.E T.root) (hxu : T.Unused st x) :
    RoundInv (Pot := Pot) (T.round Pot st x).1 := by
  obtain ⟨hR, hB, hres, hin, hcr⟩ := hI
  have hσ := hP.sigma
  set stB := T.blackClaim st x with hstB
  have hRB : T.Reachable stB := RegionTree.Reachable.black hR hxE hxu
  -- after Black's claim every potential is at most `1/4`
  have hPB : ∀ v, Pot v stB ≤ 1 / 4 := by
    intro v
    by_cases hxv : x ∈ T.eff st v
    · have h1 : Pot v stB ≤ T.reserve Pot st v := by
        have := le_maxScore Pot hxv hxu
        rw [score_of_mem Pot hxv] at this
        unfold RegionTree.reserve; linarith
      by_cases hva : v ∈ st.active
      · exact h1.trans (hres v hva)
      · have h2 := (maxScore_bounds hP hR hB v).2
        have h3 := hin v hva
        have h4 := hP.nonneg st hR v
        unfold RegionTree.reserve at h1
        nlinarith
    · rw [hP.loc_black st hR v x hxv]; exact hB v
  have hroot : T.root ∈ st.active := reachable_root_active hR
  show RoundInv (Pot := Pot) ((T.reply Pot (T.activationStep Pot stB)
      (T.responsible (T.activationStep Pot stB) x)).elim (T.activationStep Pot stB)
      (T.whiteClaim (T.activationStep Pot stB) ·))
  rcases activationStep_cases Pot stB with ⟨hlow, hact⟩ | ⟨u, hu, hu8, hdeep, hact⟩
  · -- no activation
    rw [hact]
    have hrootB : T.root ∈ stB.active := hroot
    obtain ⟨hr1, -, -⟩ := responsible_spec (T := T) hrootB hxE
    have hxr : x ∈ T.eff st (T.responsible stB x) := responsible_eff hT hrootB hxE
    refine white_step hT hP hRB hPB hlow hr1 (fun w hw hwr => ?_) hcr
    exact (reserve_black_le hT hP hR hB (not_mem_eff_of_active hT hr1 hw hwr hxr)).trans
      (hres w hw)
  · -- activation of the deepest crossing vertex `u`
    rw [hact]
    have hu' : u ∉ st.active := hu
    have hxu_eff : x ∈ T.eff st u := by
      by_contra hn
      have : Pot u stB = Pot u st := hP.loc_black st hR u x hn
      have := hin u hu'
      linarith
    have hsc := score_bounds hP hR hB hxu_eff hxu
    rw [score_of_mem Pot hxu_eff] at hsc
    have hPu12 : 1 / 12 ≤ Pot u st := by
      have := hP.nonneg st hR u
      nlinarith
    have hp4 := hP.p4 st hR u x hu' hPu12 hxu_eff hxu
    set st₁ := T.activate stB u with hst₁
    have hR₁ : T.Reachable st₁ := RegionTree.Reachable.act hRB
    have hxuE : x ∈ T.E u := (mem_eff.1 hxu_eff).1
    -- vertices that are not strict ancestors of `u` keep their post-Black potentials
    have hP₁ : ∀ v, Pot v st₁ ≤ 1 / 4 := by
      intro v
      by_cases hv : T.StrictAnc v u
      · exact (hp4 v hv).1.trans (hB v)
      · rw [hP.loc_act stB hRB u v hv]; exact hPB v
    have hin₁ : ∀ v, v ∉ st₁.active → Pot v st₁ < 1 / 8 := by
      intro v hv
      have hv' : v ∉ insert u st.active := hv
      have hvu : v ≠ u := fun h => hv' (h ▸ Finset.mem_insert_self _ _)
      have hva : v ∉ st.active := fun h => hv' (Finset.mem_insert_of_mem h)
      by_cases hsa : T.StrictAnc v u
      · exact (hp4 v hsa).1.trans_lt (hin v hva)
      · rw [hP.loc_act stB hRB u v hsa]
        by_contra hge
        rw [not_lt] at hge
        have hxv : x ∈ T.eff st v := by
          by_contra hn
          have : Pot v stB = Pot v st := hP.loc_black st hR v x hn
          have := hin v hva
          linarith
        rcases comparable hT v u (mem_eff.1 hxv).1 hxuE with h | h
        · exact hsa ⟨h, hvu⟩
        · have h1 := strictAnc_depth hT ⟨h, fun h' => hvu h'.symm⟩
          have h2 := hdeep v hva hge
          omega
    have hroot₁ : T.root ∈ st₁.active := Finset.mem_insert_of_mem hroot
    obtain ⟨hr1, hr2, hr3⟩ := responsible_spec (T := T) hroot₁ hxE
    -- the responsible vertex is `u`
    have hru : T.responsible st₁ x = u := by
      by_contra hne
      have hra : T.responsible st₁ x ∈ st.active := by
        rcases Finset.mem_insert.1 hr1 with h | h
        · exact absurd h hne
        · exact h
      rcases comparable hT u (T.responsible st₁ x) hxuE hr2 with h | h
      · exact (mem_eff.1 hxu_eff).2 _ hra ⟨h, fun h' => hne h'.symm⟩ hr2
      · have h1 := strictAnc_depth hT ⟨h, hne⟩
        have h2 := hr3 u (Finset.mem_insert_self _ _) hxuE
        omega
    rw [hru]
    refine white_step hT hP hR₁ hP₁ hin₁ (Finset.mem_insert_self _ _) (fun w hw hwu => ?_) hcr
    have hw' : w ∈ st.active := by
      rcases Finset.mem_insert.1 hw with h | h
      · exact absurd h hwu
      · exact h
    by_cases hsa : T.StrictAnc w u
    · exact (hp4 w hsa).2.trans (hres w hw')
    · refine (reserve_act_le hT hP hRB hPB hsa).trans
        ((reserve_black_le hT hP hR hB fun hxw => ?_).trans (hres w hw'))
      rcases comparable hT w u (mem_eff.1 hxw).1 hxuE with h | h
      · exact hsa ⟨h, hwu⟩
      · exact (mem_eff.1 hxu_eff).2 w hw' ⟨h, fun h' => hwu h'.symm⟩ (mem_eff.1 hxw).1

theorem init_inv (hP : T.PotentialProps Pot σ) :
    RoundInv (Pot := Pot) T.init := by
  have hR : T.Reachable T.init := RegionTree.Reachable.init
  have hB : ∀ v, Pot v T.init ≤ 1 / 4 := fun v => (hP.p1_init v).trans (by norm_num)
  refine ⟨hR, hB, fun v _ => ?_, fun v _ => (hP.p1_init v).trans_lt (by norm_num),
    fun v Q => Nat.zero_le _⟩
  have h1 := (maxScore_bounds hP hR hB v).2
  have h2 := hP.p1_init v
  have h3 := hP.nonneg _ hR v
  have hσ := hP.sigma
  unfold RegionTree.reserve
  nlinarith

theorem run_take_succ (bs : List (Pt d)) (k : ℕ) (hk : k < bs.length) :
    T.run Pot (bs.take (k + 1)) = (T.round Pot (T.run Pot (bs.take k)) (bs.get ⟨k, hk⟩)).1 := by
  unfold RegionTree.run
  rw [List.take_succ, List.foldl_append, List.getElem?_eq_getElem hk]
  rfl

theorem run_inv (hT : T.WellFormed) (hP : T.PotentialProps Pot σ) (bs : List (Pt d))
    (hbs : T.LegalBlack Pot bs) : ∀ k ≤ bs.length, RoundInv (Pot := Pot) (T.run Pot (bs.take k)) := by
  intro k
  induction k with
  | zero => intro _; exact init_inv hP
  | succ k ih =>
    intro hk
    rw [run_take_succ bs k hk]
    exact round_inv hT hP (ih (by omega)) (hbs k hk).1 (hbs k hk).2

end AppendixAAux

/-- **Lemma A.2** (`lem:new-abstract`): if the potentials satisfy the locality properties and
(P1)–(P4), then White's potential strategy (with the activation of Definition A.1) meets every
local quota: on every legal complete play, every requirement `Q ∈ 𝒜_v` gets at least `a_Q`
White points. -/
theorem lem_new_abstract {d : ℕ} (T : RegionTree d) (hT : T.WellFormed) (Pot : T.V → T.State → ℝ)
    (σ : ℝ) (hP : T.PotentialProps Pot σ) (bs : List (Pt d)) (hbs : T.LegalBlack Pot bs)
    (hcomplete : ∀ x ∈ T.E T.root, x ∈ (T.run Pot bs).black ∨ x ∈ (T.run Pot bs).white) :
    ∀ v, ∀ Q ∈ T.reqs v, T.quota v Q ≤ ((T.run Pot bs).white ∩ Q).card := by
  have hI := AppendixAAux.run_inv hT hP bs hbs bs.length le_rfl
  rw [List.take_length] at hI
  obtain ⟨hR, hB, -, -, hcr⟩ := hI
  intro v Q hQ
  by_contra hlt
  rw [not_le] at hlt
  have hc : ((T.run Pot bs).credit v Q : ℝ) ≤ (((T.run Pot bs).white ∩ Q).card : ℝ) :=
    Nat.cast_le.2 (hcr v Q)
  have hpos : 0 < T.outstanding (T.run Pot bs) v Q := by
    unfold RegionTree.outstanding; linarith
  have := hP.p1_detect _ hR v hcomplete ⟨Q, hQ, hpos⟩
  linarith [hB v]

/-! ## A.3 The dyadic hierarchy and the local requirements -/

/-- Retained scales and thresholds: exponents `h_j` (`H_j = 2^{h_j}`) and thresholds `α_j`, `γ_j`.
The paper's conditions (`h` strictly increasing, `0 < α_j < γ_j`) are not part of the type; they are
imposed where needed (`ScaleConditions`, and the hypotheses `hpos` of Claims A.3 and A.4). -/
inductive Scales
  | mk (h : ℕ → ℕ) (α γ : ℕ → ℝ)

/-- The exponents `h_j` of the retained scales (`H_j = 2^{h_j}`). -/
def Scales.h : Scales → ℕ → ℕ
  | .mk h _ _ => h

/-- The thresholds `α_j` (a remainder is retained iff it has at least `α_j` points). -/
def Scales.α : Scales → ℕ → ℝ
  | .mk _ α _ => α

/-- The thresholds `γ_j` (a rectangle is eligible at scale `j` iff it has at least `γ_j` points). -/
def Scales.γ : Scales → ℕ → ℝ
  | .mk _ _ γ => γ

/-- The index of the scale-`j` aligned dyadic cube containing `x`. -/
def cubeIdx {d : ℕ} (D : Scales) (j : ℕ) (x : Pt d) : Pt d := fun i => x i / (2 : ℤ) ^ D.h j

/-- The number of points of `E ∩ R` in the same scale-`j` cube as `x`. -/
noncomputable def massIn {d : ℕ} (D : Scales) (E : Finset (Pt d)) (R : Set (Pt d)) (j : ℕ)
    (x : Pt d) : ℕ :=
  ((↑E ∩ R) ∩ {y | cubeIdx D j y = cubeIdx D j x}).ncard

/-- The downward search for a piece `(l, R)` (§A.3): the scale-`j'` cube of `x` (`j' < l`) is
selected iff it meets its own threshold, `|E ∩ R ∩ C| ≥ γ_{j'}`, while every cube strictly between
(scales `j' < m < l`) on the way down to it failed its threshold. -/
def Selected {d : ℕ} (D : Scales) (E : Finset (Pt d)) (R : Set (Pt d)) (l j' : ℕ) (x : Pt d) :
    Prop :=
  j' < l ∧ D.γ j' ≤ massIn D E R j' x ∧ ∀ m, j' < m → m < l → (massIn D E R m x : ℝ) < D.γ m

/-- The local remainder `Q_R` of the piece `(l, R)`: the points of `E ∩ R` in no selected cube. -/
def remainder {d : ℕ} (D : Scales) (E : Finset (Pt d)) (R : Set (Pt d)) (l : ℕ) : Set (Pt d) :=
  {x | x ∈ E ∧ x ∈ R ∧ ∀ j', ¬ Selected D E R l j' x}

/-- The local requirements of the dyadic tree on board `E` with top scale `J` and accuracy `ε`
(§A.3): the vertices are the dummy root and the scale-`j` cubes (`j ≤ J`) that meet `E`; at the
cube `(j, c)` every rectangle `R` inside it with `|E ∩ R| ≥ γ_j` (eligible) contributes its
remainder `Q_R` if `|Q_R| ≥ α_j` (otherwise it is discarded), with quota `(1/2 - ε/2)|Q_R|`.
The parent of a scale-`j` cube (`j < J`) is the scale-`(j+1)` cube containing it, and the parent of
a scale-`J` cube is the dummy root. If the computed parent cube were not a vertex, the definition
falls back to the root; for strictly increasing exponents this cannot happen (the containing cube
meets `E`), and `ScaleConditions` requires `WellFormed`, which rules it out. -/
noncomputable def dyadicTree {d : ℕ} (D : Scales) (ε : ℝ) (E : Finset (Pt d)) (J : ℕ) :
    RegionTree d := by
  classical
  let S : Finset (Fin (J + 1) × Pt d) :=
    Finset.univ.biUnion fun j : Fin (J + 1) => (E.image (cubeIdx D j.val)).map ⟨fun c => (j, c), fun _ _ h => by
      simpa using congrArg Prod.snd h⟩
  let V := Option {p // p ∈ S}
  let cube : Fin (J + 1) → Pt d → Finset (Pt d) := fun j c => E.filter (cubeIdx D j · = c)
  let lowCorner : Fin (J + 1) → Pt d → Pt d := fun j c i => c i * (2 : ℤ) ^ D.h j
  let highCorner : Fin (J + 1) → Pt d → Pt d := fun j c i => c i * (2 : ℤ) ^ D.h j + (2 : ℤ) ^ D.h j - 1
  let reqsAt : Fin (J + 1) → Pt d → Finset (Finset (Pt d)) := fun j c =>
    let box := Finset.Icc (lowCorner j c) (highCorner j c)
    ((box ×ˢ box).filter fun p => p.1 ≤ p.2 ∧
        D.γ j ≤ ((↑E ∩ Set.Icc p.1 p.2 : Set (Pt d)).ncard : ℝ) ∧
        D.α j ≤ ((remainder D E (Set.Icc p.1 p.2) j).ncard : ℝ)).image
      fun p => (E.filter fun x => x ∈ remainder D E (Set.Icc p.1 p.2) j)
  exact RegionTree.mk V none
    (fun v => match v with
      | none => none
      | some ⟨(j, c), _⟩ =>
          if hj : j.val < J then
            let j' : Fin (J + 1) := ⟨j.val + 1, by omega⟩
            let p := (j', cubeIdx D j' (lowCorner j c))
            if hp : p ∈ S then some (some ⟨p, hp⟩) else some none
          else some none)
    (fun v => match v with
      | none => 0
      | some ⟨(j, _), _⟩ => J + 1 - j.val)
    (fun v => match v with
      | none => E
      | some ⟨(j, c), _⟩ => cube j c)
    (fun v => match v with
      | none => ∅
      | some ⟨(j, c), _⟩ => reqsAt j c)
    (fun _ Q => (1 / 2 - ε / 2) * Q.card)

/-! ### Helpers (appA): the dyadic tree is well formed -/

namespace AppendixAAux

theorem ediv_eq_iff_bounds {a b c : ℤ} (hb : 0 < b) : a / b = c ↔ c * b ≤ a ∧ a ≤ c * b + b - 1 := by
  constructor
  · rintro rfl
    have h1 := (Int.le_ediv_iff_mul_le hb).1 (le_refl (a / b))
    have h2 := (Int.ediv_lt_iff_lt_mul hb).1 (lt_add_one (a / b))
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    have h3 := (Int.le_ediv_iff_mul_le hb).2 h1
    have h4 := (Int.ediv_lt_iff_lt_mul hb).2 (show a < (c + 1) * b by nlinarith)
    omega

theorem ediv_pow_nest (a : ℤ) {m n : ℕ} (h : m ≤ n) : (a / 2 ^ m * 2 ^ m) / 2 ^ n = a / 2 ^ n := by
  have e : (2 : ℤ) ^ n = 2 ^ m * 2 ^ (n - m) := by rw [← pow_add]; congr 1; omega
  rw [e, mul_comm (a / 2 ^ m), Int.mul_ediv_mul_of_pos _ _ (by positivity),
    Int.ediv_ediv_of_nonneg (by positivity)]

variable {d : ℕ}

/-- A point lies in the scale-`j` cube with index `c` iff it lies between the cube's corners. -/
theorem cubeIdx_eq_iff (D : Scales) (j : ℕ) (x c : Pt d) :
    cubeIdx D j x = c ↔ ∀ i, c i * 2 ^ D.h j ≤ x i ∧ x i ≤ c i * 2 ^ D.h j + 2 ^ D.h j - 1 := by
  unfold cubeIdx
  rw [funext_iff]
  exact forall_congr' fun i => ediv_eq_iff_bounds (by positivity)

/-- For nested scales the scale-`k` cube of the low corner of `x`'s scale-`j` cube is `x`'s. -/
theorem cubeIdx_lowCorner (D : Scales) {j k : ℕ} (h : D.h j ≤ D.h k) (x : Pt d) :
    cubeIdx D k (fun i => cubeIdx D j x i * 2 ^ D.h j) = cubeIdx D k x := by
  funext i
  exact ediv_pow_nest (x i) h

theorem mem_cubes_iff (D : Scales) (E : Finset (Pt d)) {J : ℕ} (k : Fin (J + 1)) (c : Pt d) :
    (k, c) ∈ (Finset.univ.biUnion fun j : Fin (J + 1) =>
      (E.image (cubeIdx D j.val)).map ⟨fun c => (j, c), fun _ _ h => by
        simpa using congrArg Prod.snd h⟩) ↔ ∃ x ∈ E, cubeIdx D k x = c := by
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_map, Finset.mem_image]
  constructor
  · rintro ⟨j, c', ⟨x, hx, rfl⟩, h⟩
    cases h
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨k, _, ⟨x, hx, rfl⟩, rfl⟩

/-- Every constructed dyadic tree is well formed when the exponents are strictly increasing. -/
theorem dyadicTree_wellFormed (D : Scales) (hD : StrictMono D.h) (ε : ℝ) (E : Finset (Pt d))
    (J : ℕ) : (dyadicTree D ε E J).WellFormed := by
  classical
  have hmono : ∀ j : ℕ, D.h j ≤ D.h (j + 1) := fun j => hD.monotone (Nat.le_succ j)
  -- the parent cube of a vertex below the top level is again a vertex
  have hparent : ∀ (j : Fin (J + 1)) (c : Pt d) (hj : j.val < J), (∃ x ∈ E, cubeIdx D j x = c) →
      ∃ x ∈ E, cubeIdx D (j.val + 1) x =
        cubeIdx D (j.val + 1) (fun i => c i * 2 ^ D.h j.val) := by
    rintro j c - ⟨x, hx, rfl⟩
    exact ⟨x, hx, (cubeIdx_lowCorner D (hmono j.val) x).symm⟩
  unfold RegionTree.WellFormed
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rcases v with _ | ⟨⟨⟨j, c⟩, hp⟩⟩
    · exact absurd rfl hv
    · have hp' := (mem_cubes_iff D E j c).1 hp
      dsimp only [dyadicTree, RegionTree.parent, RegionTree.depth]
      split_ifs with h1 h2
      · exact ⟨_, rfl, by dsimp only; omega⟩
      · exact absurd ((mem_cubes_iff D E _ _).2 (hparent j c h1 hp')) h2
      · exact ⟨none, rfl, by dsimp only; omega⟩
  · intro v u hvu
    rcases v with _ | ⟨⟨⟨j, c⟩, hp⟩⟩
    · cases hvu
    · dsimp only [dyadicTree, RegionTree.parent] at hvu
      split_ifs at hvu with h1 h2 <;> cases hvu
      · dsimp only [dyadicTree, RegionTree.E]
        intro x hx
        rw [Finset.mem_filter] at hx ⊢
        refine ⟨hx.1, ?_⟩
        rw [← hx.2]
        exact (cubeIdx_lowCorner D (hmono j.val) x).symm
      all_goals
        dsimp only [dyadicTree, RegionTree.E]
        exact Finset.filter_subset _ _
  · intro v w u hv hw hne
    rcases v with _ | ⟨⟨⟨j, c⟩, hp⟩⟩
    · cases hv
    rcases w with _ | ⟨⟨⟨k, c'⟩, hq⟩⟩
    · cases hw
    have hp' := (mem_cubes_iff D E j c).1 hp
    have hq' := (mem_cubes_iff D E k c').1 hq
    have hjk : j = k := by
      dsimp only [dyadicTree, RegionTree.parent] at hv hw
      split_ifs at hv with h1 h2
      · split_ifs at hw with h3 h4
        · have h5 := congrArg (fun p : Fin (J + 1) × Pt d => p.1.val)
            (congrArg Subtype.val (Option.some.inj (Option.some.inj (hv.trans hw.symm))))
          dsimp only at h5
          exact Fin.ext (by omega)
        · exact absurd ((mem_cubes_iff D E _ _).2 (hparent k c' h3 hq')) h4
        · cases hv.trans hw.symm
      · exact absurd ((mem_cubes_iff D E _ _).2 (hparent j c h1 hp')) h2
      · split_ifs at hw with h3 h4
        · cases hv.trans hw.symm
        · exact absurd ((mem_cubes_iff D E _ _).2 (hparent k c' h3 hq')) h4
        · exact Fin.ext (by omega)
    subst hjk
    have hcc : c ≠ c' := by
      rintro rfl
      exact hne rfl
    dsimp only [dyadicTree, RegionTree.E]
    rw [Finset.disjoint_filter]
    intro x _ h1 h2
    exact hcc (h1.symm.trans h2)
  · intro v Q hQ
    rcases v with _ | ⟨⟨⟨j, c⟩, hp⟩⟩
    · simp [dyadicTree, RegionTree.reqs] at hQ
    · dsimp only [dyadicTree, RegionTree.reqs, RegionTree.E] at hQ ⊢
      obtain ⟨p, hp1, rfl⟩ := Finset.mem_image.1 hQ
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp1
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨hx.1, ?_⟩
      have hxR : x ∈ Set.Icc p.1 p.2 := hx.2.2.1
      rw [cubeIdx_eq_iff]
      intro i
      exact ⟨(hp1.1.1.1 i).trans (hxR.1 i), (hxR.2 i).trans (hp1.1.2.2 i)⟩

end AppendixAAux

/-- The final piece of a point `x` of a piece `(l, R)`: descend to the selected cube of `x` (the
first selected cube on its branch is the one of largest scale), restrict the rectangle to it, and
repeat; stop when no cube of `x` is selected. -/
noncomputable def finalPiece {d : ℕ} (D : Scales) (E : Finset (Pt d)) (x : Pt d) :
    ℕ → Set (Pt d) → ℕ × Set (Pt d)
  | 0, R => (0, R)
  | l + 1, R =>
      if h : ∃ j' ≤ l, Selected D E R (l + 1) j' x then
        let j' := Nat.findGreatest (fun j' => Selected D E R (l + 1) j' x) l
        have : j' < l + 1 := Nat.lt_succ_of_le (Nat.findGreatest_le l)
        finalPiece D E x j' (R ∩ {y | cubeIdx D j' y = cubeIdx D j' x})
      else (l + 1, R)

/-! ### Helpers (appA): the recursive decomposition and `finalPiece` -/

namespace AppendixAAux

variable {d : ℕ}

/-- Nested cubes: agreeing at scale `j` implies agreeing at every larger scale. -/
theorem cube_mono (D : Scales) (hD : StrictMono D.h) {j k : ℕ} (hjk : j ≤ k) {x y : Pt d}
    (h : cubeIdx D j y = cubeIdx D j x) : cubeIdx D k y = cubeIdx D k x := by
  rw [← cubeIdx_lowCorner D (hD.monotone hjk) y, h, cubeIdx_lowCorner D (hD.monotone hjk) x]

theorem massIn_congr (D : Scales) (E : Finset (Pt d)) (R : Set (Pt d)) (m : ℕ) {x y : Pt d}
    (h : cubeIdx D m y = cubeIdx D m x) : massIn D E R m y = massIn D E R m x := by
  unfold massIn; rw [h]

/-- Restricting a piece to a coarser cube of `x` does not change the mass of `x`'s finer cubes. -/
theorem massIn_restrict (D : Scales) (hD : StrictMono D.h) (E : Finset (Pt d)) (R : Set (Pt d))
    {f j : ℕ} (hfj : f ≤ j) (x : Pt d) :
    massIn D E (R ∩ {y | cubeIdx D j y = cubeIdx D j x}) f x = massIn D E R f x := by
  unfold massIn
  congr 1
  ext y
  simp only [mem_inter_iff, mem_setOf_eq, Finset.mem_coe]
  constructor
  · rintro ⟨⟨h1, h2, -⟩, h4⟩; exact ⟨⟨h1, h2⟩, h4⟩
  · rintro ⟨⟨h1, h2⟩, h4⟩; exact ⟨⟨h1, h2, cube_mono D hD hfj h4⟩, h4⟩

/-- At most one scale is selected for a point. -/
theorem selected_unique {D : Scales} {E : Finset (Pt d)} {R : Set (Pt d)} {L a b : ℕ} {x : Pt d}
    (ha : Selected D E R L a x) (hb : Selected D E R L b x) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · exact absurd hb.2.1 (not_le.2 (ha.2.2 b h hb.1))
  · exact h
  · exact absurd ha.2.1 (not_le.2 (hb.2.2 a h ha.1))

/-- Selection at scale `j` depends only on the cubes of the point at scales `≥ j`. -/
theorem selected_congr {D : Scales} {E : Finset (Pt d)} {R : Set (Pt d)} {L j : ℕ} {x y : Pt d}
    (h : ∀ m, j ≤ m → cubeIdx D m y = cubeIdx D m x) :
    Selected D E R L j y ↔ Selected D E R L j x := by
  unfold Selected
  rw [massIn_congr D E R j (h j le_rfl)]
  constructor
  · rintro ⟨a, b, c⟩
    refine ⟨a, b, fun m h1 h2 => ?_⟩
    rw [← massIn_congr D E R m (h m h1.le)]; exact c m h1 h2
  · rintro ⟨a, b, c⟩
    refine ⟨a, b, fun m h1 h2 => ?_⟩
    rw [massIn_congr D E R m (h m h1.le)]; exact c m h1 h2

theorem finalPiece_of_selected (D : Scales) (E : Finset (Pt d)) {l j : ℕ} {R : Set (Pt d)}
    {x : Pt d} (hs : Selected D E R (l + 1) j x) :
    finalPiece D E x (l + 1) R =
      finalPiece D E x j (R ∩ {y | cubeIdx D j y = cubeIdx D j x}) := by
  have hex : ∃ j' ≤ l, Selected D E R (l + 1) j' x := ⟨j, Nat.lt_succ_iff.1 hs.1, hs⟩
  rw [finalPiece, dif_pos hex]
  have hfg := Nat.findGreatest_spec (P := fun j' => Selected D E R (l + 1) j' x)
    (Nat.lt_succ_iff.1 hs.1) hs
  have heq := selected_unique hfg hs
  dsimp only
  rw [heq]

theorem finalPiece_of_none (D : Scales) (E : Finset (Pt d)) {l : ℕ} {R : Set (Pt d)} {x : Pt d}
    (hn : ∀ j', ¬ Selected D E R l j' x) : finalPiece D E x l R = (l, R) := by
  cases l with
  | zero => rw [finalPiece]
  | succ l =>
    rw [finalPiece, dif_neg]
    rintro ⟨j', -, hj'⟩
    exact hn j' hj'

/-- The final piece of `x`: its level is at most `l`; below `l` it is `R` cut to `x`'s cube at
that level, which met its threshold; at level `l` it is `R`; nothing is selected from it. -/
theorem finalPiece_spec (D : Scales) (hD : StrictMono D.h) (E : Finset (Pt d)) :
    ∀ (l : ℕ) (R : Set (Pt d)) (x : Pt d),
    (finalPiece D E x l R).1 ≤ l ∧
    ((finalPiece D E x l R).1 < l →
      (finalPiece D E x l R).2 =
        R ∩ {y | cubeIdx D (finalPiece D E x l R).1 y = cubeIdx D (finalPiece D E x l R).1 x} ∧
      D.γ (finalPiece D E x l R).1 ≤ massIn D E R (finalPiece D E x l R).1 x) ∧
    ((finalPiece D E x l R).1 = l → (finalPiece D E x l R).2 = R) ∧
    ∀ j', ¬ Selected D E (finalPiece D E x l R).2 (finalPiece D E x l R).1 j' x := by
  intro l
  induction l using Nat.strong_induction_on with
  | _ l ih =>
  intro R x
  by_cases hex : ∃ j, Selected D E R l j x
  · obtain ⟨j, hs⟩ := hex
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by have := hs.1; omega⟩
    rw [finalPiece_of_selected D E hs]
    obtain ⟨h1, h2, h3, h4⟩ := ih j hs.1 (R ∩ {y | cubeIdx D j y = cubeIdx D j x}) x
    have hjl := hs.1
    refine ⟨by omega, fun _ => ?_, fun h => absurd h (by omega), h4⟩
    rcases lt_or_eq_of_le h1 with hlt | heq
    · obtain ⟨e1, e2⟩ := h2 hlt
      refine ⟨?_, ?_⟩
      · rw [e1, Set.inter_assoc]
        congr 1
        ext y
        simp only [mem_inter_iff, mem_setOf_eq]
        constructor
        · rintro ⟨_, h⟩; exact h
        · intro h; exact ⟨cube_mono D hD hlt.le h, h⟩
      · rw [← massIn_restrict D hD E R hlt.le x]; exact e2
    · rw [h3 heq, heq]
      exact ⟨rfl, hs.2.1⟩
  · push_neg at hex
    rw [finalPiece_of_none D E hex]
    exact ⟨le_rfl, fun h => absurd h (lt_irrefl _), fun _ => rfl, hex⟩

/-- A point that agrees with `x` at all scales from `x`'s final level up, and for which nothing is
selected from `x`'s final piece, has the same final piece. -/
theorem finalPiece_congr (D : Scales) (hD : StrictMono D.h) (E : Finset (Pt d)) :
    ∀ (l : ℕ) (R : Set (Pt d)) (x y : Pt d),
    (∀ m, (finalPiece D E x l R).1 ≤ m → cubeIdx D m y = cubeIdx D m x) →
    (∀ j', ¬ Selected D E (finalPiece D E x l R).2 (finalPiece D E x l R).1 j' y) →
    finalPiece D E y l R = finalPiece D E x l R := by
  intro l
  induction l using Nat.strong_induction_on with
  | _ l ih =>
  intro R x y hagree hnone
  by_cases hex : ∃ j, Selected D E R l j x
  · obtain ⟨j, hs⟩ := hex
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by have := hs.1; omega⟩
    have hle := (finalPiece_spec D hD E j (R ∩ {y | cubeIdx D j y = cubeIdx D j x}) x).1
    rw [finalPiece_of_selected D E hs] at hagree hnone ⊢
    have hy : Selected D E R (l' + 1) j y :=
      (selected_congr fun m hm => hagree m (hle.trans hm)).2 hs
    rw [finalPiece_of_selected D E hy]
    have hcs : {z | cubeIdx D j z = cubeIdx D j y} = {z | cubeIdx D j z = cubeIdx D j x} := by
      rw [hagree j hle]
    rw [hcs]
    exact ih j hs.1 _ x y hagree hnone
  · push_neg at hex
    rw [finalPiece_of_none D E hex] at hnone ⊢
    exact finalPiece_of_none D E hnone

/-- For a piece `R` inside one scale-`l` cube that is eligible, the final piece of every point
`x ∈ R` is `R` cut to `x`'s cube at the final level, and it met that level's threshold. -/
theorem finalPiece_data (D : Scales) (hD : StrictMono D.h) (E : Finset (Pt d)) {l : ℕ}
    {R : Set (Pt d)} (hRcube : ∃ c, R ⊆ {y | cubeIdx D l y = c})
    (helig : D.γ l ≤ ((↑E ∩ R : Set (Pt d)).ncard : ℝ)) {x : Pt d} (hx : x ∈ R) :
    (finalPiece D E x l R).1 ≤ l ∧
    (finalPiece D E x l R).2 =
        R ∩ {y | cubeIdx D (finalPiece D E x l R).1 y = cubeIdx D (finalPiece D E x l R).1 x} ∧
    D.γ (finalPiece D E x l R).1 ≤ massIn D E R (finalPiece D E x l R).1 x ∧
    ∀ j', ¬ Selected D E (finalPiece D E x l R).2 (finalPiece D E x l R).1 j' x := by
  obtain ⟨h1, h2, h3, h4⟩ := finalPiece_spec D hD E l R x
  obtain ⟨c, hc⟩ := hRcube
  have hRl : R ∩ {y | cubeIdx D l y = cubeIdx D l x} = R := by
    ext y
    simp only [mem_inter_iff, mem_setOf_eq, and_iff_left_iff_imp]
    intro hy
    rw [hc hy, hc hx]
  refine ⟨h1, ?_, ?_, h4⟩
  · rcases lt_or_eq_of_le h1 with hlt | heq
    · exact (h2 hlt).1
    · rw [h3 heq, heq, hRl]
  · rcases lt_or_eq_of_le h1 with hlt | heq
    · exact (h2 hlt).2
    · rw [heq]
      unfold massIn
      rw [Set.inter_assoc, hRl]
      exact helig

/-- The intersection of a rectangle with the scale-`j` cube of one of its points is a rectangle. -/
theorem rect_inter_cube (D : Scales) (R : Rect d) (j : ℕ) {x : Pt d} (hx : x ∈ R.pts) :
    ∃ R' : Rect d, R'.pts = R.pts ∩ {y | cubeIdx D j y = cubeIdx D j x} := by
  have hxc := (cubeIdx_eq_iff D j x (cubeIdx D j x)).1 rfl
  refine ⟨Rect.mk (R.lo ⊔ fun i => cubeIdx D j x i * 2 ^ D.h j)
    (R.hi ⊓ fun i => cubeIdx D j x i * 2 ^ D.h j + 2 ^ D.h j - 1)
    (le_trans (sup_le hx.1 fun i => (hxc i).1) (le_inf hx.2 fun i => (hxc i).2)), ?_⟩
  ext y
  simp only [Rect.pts, Rect.lo, Rect.hi, mem_Icc, mem_inter_iff, mem_setOf_eq, cubeIdx_eq_iff,
    sup_le_iff, le_inf_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, h3⟩, fun i => ⟨h2 i, h4 i⟩⟩
  · rintro ⟨⟨h1, h3⟩, h⟩; exact ⟨⟨h1, fun i => (h i).1⟩, h3, fun i => (h i).2⟩

/-- The scale-`j` mass of `x` in `R` counted as a finset. -/
theorem massIn_eq_card (D : Scales) (E : Finset (Pt d)) (R : Set (Pt d)) (j : ℕ) (x : Pt d) :
    massIn D E R j x =
      ((E.filter (· ∈ R)).filter (fun y => cubeIdx D j y = cubeIdx D j x)).card := by
  unfold massIn
  rw [← Set.ncard_coe_finset]
  congr 1
  ext y
  simp

theorem remainder_ncard (D : Scales) (E : Finset (Pt d)) (R : Set (Pt d)) (l : ℕ) :
    (remainder D E R l).ncard = (E.filter (· ∈ remainder D E R l)).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext y
  simp only [Finset.coe_filter, mem_setOf_eq]
  exact ⟨fun h => ⟨h.1, h⟩, fun h => h.2⟩

theorem inter_remainder_ncard (D : Scales) (E : Finset (Pt d)) (R : Set (Pt d)) (l : ℕ)
    (W : Set (Pt d)) :
    (W ∩ remainder D E R l).ncard = ((E.filter (· ∈ remainder D E R l)).filter (· ∈ W)).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext y
  rw [Finset.coe_filter]
  simp only [Finset.mem_filter, mem_setOf_eq, mem_inter_iff]
  exact ⟨fun h => ⟨⟨h.2.1, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩

end AppendixAAux

open AppendixAAux in
/-- **Claim A.3** (`claim:discardsmall`): assume the standing hypotheses of §A.3, nested scales
(`StrictMono D.h`) and `0 < α_j < γ_j`. If `α_j/γ_j ≤ δ_j` with `δ_j ≥ 0`, `∑ δ_j ≤ ε/4`, then for every
eligible rectangle `R` in a scale-`l` cube, the points of `E ∩ R` whose final piece has a discarded
remainder (`|Q| < α`) number at most `(ε/4)|E ∩ R|`. -/
theorem claim_discardsmall {d : ℕ} (D : Scales) (hD : StrictMono D.h) (E : Finset (Pt d)) (ε : ℝ)
    (δ : ℕ → ℝ) (hpos : ∀ j, 0 < D.α j ∧ D.α j < D.γ j) (hδ : ∀ j, D.α j / D.γ j ≤ δ j)
    (hδnn : ∀ j, 0 ≤ δ j) (hsum : Summable δ) (hδsum : ∑' j, δ j ≤ ε / 4)
    (l : ℕ) (R : Rect d) (hRcube : ∃ c, R.pts ⊆ {y | cubeIdx D l y = c})
    (helig : D.γ l ≤ ((↑E ∩ R.pts : Set (Pt d)).ncard : ℝ)) :
    (({x | x ∈ E ∧ x ∈ R.pts ∧
        ((remainder D E (finalPiece D E x l R.pts).2 (finalPiece D E x l R.pts).1).ncard : ℝ) <
          D.α (finalPiece D E x l R.pts).1}).ncard : ℝ) ≤
      ε / 4 * ((↑E ∩ R.pts : Set (Pt d)).ncard : ℝ) := by
  classical
  set F : Pt d → ℕ × Set (Pt d) := fun x => finalPiece D E x l R.pts with hF
  set ER := E.filter (· ∈ R.pts) with hER
  have hERset : (↑E ∩ R.pts : Set (Pt d)) = ↑ER := by ext y; simp [hER]
  set Disc := ER.filter (fun x => ((remainder D E (F x).2 (F x).1).ncard : ℝ) < D.α (F x).1)
    with hDisc
  have hset : {x | x ∈ E ∧ x ∈ R.pts ∧
        ((remainder D E (finalPiece D E x l R.pts).2 (finalPiece D E x l R.pts).1).ncard : ℝ) <
          D.α (finalPiece D E x l R.pts).1} = ↑Disc := by
    ext y; simp [hDisc, hER, hF, and_assoc]
  rw [hset, Set.ncard_coe_finset, hERset, Set.ncard_coe_finset]
  have hαδ : ∀ j, D.α j ≤ δ j * D.γ j := fun j =>
    (div_le_iff₀ ((hpos j).1.trans (hpos j).2)).1 (hδ j)
  -- the data of the final piece of a point of `R`
  have hdata := fun x (hx : x ∈ R.pts) => finalPiece_data D hD E hRcube helig hx
  -- one cube at one level
  have hcube : ∀ j ∈ Finset.range (l + 1), ∀ c ∈ ER.image (cubeIdx D j),
      (((Disc.filter (fun x => (F x).1 = j)).filter (fun x => cubeIdx D j x = c)).card : ℝ) ≤
        δ j * ((ER.filter (fun x => cubeIdx D j x = c)).card : ℝ) := by
    intro j _ c _
    set G := (Disc.filter (fun x => (F x).1 = j)).filter (fun x => cubeIdx D j x = c) with hG
    rcases G.eq_empty_or_nonempty with h0 | ⟨x0, hx0⟩
    · rw [h0, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg (hδnn j) (Nat.cast_nonneg _)
    have m1 := Finset.mem_filter.1 hx0
    have m2 := Finset.mem_filter.1 m1.1
    have m3 := Finset.mem_filter.1 m2.1
    have m4 := Finset.mem_filter.1 m3.1
    have hx0R : x0 ∈ R.pts := m4.2
    have hx0d := m3.2
    have hx0j : (F x0).1 = j := m2.2
    have hx0c : cubeIdx D j x0 = c := m1.2
    obtain ⟨-, e0, g0, -⟩ := hdata x0 hx0R
    have hsub : G ⊆ E.filter (· ∈ remainder D E (F x0).2 (F x0).1) := by
      intro y hy
      have n1 := Finset.mem_filter.1 hy
      have n2 := Finset.mem_filter.1 n1.1
      have n3 := Finset.mem_filter.1 n2.1
      have n4 := Finset.mem_filter.1 n3.1
      have hyE : y ∈ E := n4.1
      have hyR : y ∈ R.pts := n4.2
      have hyj : (F y).1 = j := n2.2
      have hyc : cubeIdx D j y = c := n1.2
      obtain ⟨-, ey, -, ny⟩ := hdata y hyR
      have hFy : F y = F x0 := by
        refine Prod.ext (hyj.trans hx0j.symm) ?_
        show (finalPiece D E y l R.pts).2 = (finalPiece D E x0 l R.pts).2
        rw [ey, e0]
        have h1 : (finalPiece D E y l R.pts).1 = j := hyj
        have h2 : (finalPiece D E x0 l R.pts).1 = j := hx0j
        rw [h1, h2, hyc, hx0c]
      have hymem : y ∈ remainder D E (F y).2 (F y).1 := by
        refine ⟨hyE, ?_, ny⟩
        show y ∈ (finalPiece D E y l R.pts).2
        rw [ey]
        exact ⟨hyR, rfl⟩
      rw [hFy] at hymem
      exact Finset.mem_filter.2 ⟨hyE, hymem⟩
    have hcard := Finset.card_le_card hsub
    rw [← remainder_ncard] at hcard
    have hγ : D.γ j ≤ ((ER.filter (fun x => cubeIdx D j x = c)).card : ℝ) := by
      have := g0
      rw [massIn_eq_card] at this
      have h2 : (finalPiece D E x0 l R.pts).1 = j := hx0j
      rw [h2, hx0c] at this
      exact this
    have hrem : ((remainder D E (F x0).2 (F x0).1).ncard : ℝ) < D.α j := by
      have h2 : (F x0).1 = j := hx0j
      rw [← h2]; exact hx0d
    calc (G.card : ℝ) ≤ ((remainder D E (F x0).2 (F x0).1).ncard : ℝ) := by exact_mod_cast hcard
      _ ≤ D.α j := hrem.le
      _ ≤ δ j * D.γ j := hαδ j
      _ ≤ δ j * ((ER.filter (fun x => cubeIdx D j x = c)).card : ℝ) :=
          mul_le_mul_of_nonneg_left hγ (hδnn j)
  -- one level
  have hlevel : ∀ j ∈ Finset.range (l + 1),
      ((Disc.filter (fun x => (F x).1 = j)).card : ℝ) ≤ δ j * (ER.card : ℝ) := by
    intro j hj
    rw [Finset.card_eq_sum_card_fiberwise (f := cubeIdx D j) (t := ER.image (cubeIdx D j))
      (fun x hx => Finset.mem_image_of_mem _ (Finset.mem_of_mem_filter x
        (Finset.mem_of_mem_filter x hx)))]
    rw [Finset.card_eq_sum_card_fiberwise (s := ER) (f := cubeIdx D j)
      (t := ER.image (cubeIdx D j)) (fun x hx => Finset.mem_image_of_mem _ hx)]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (hcube j hj)
  have htot : (Disc.card : ℝ) ≤ ∑ j ∈ Finset.range (l + 1), δ j * (ER.card : ℝ) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun x => (F x).1) (t := Finset.range (l + 1))
      (fun x hx => Finset.mem_range.2 (Nat.lt_succ_of_le
        (hdata x (Finset.mem_filter.1 (Finset.mem_of_mem_filter x hx)).2).1))]
    push_cast
    exact Finset.sum_le_sum hlevel
  rw [← Finset.sum_mul] at htot
  have hδl : ∑ j ∈ Finset.range (l + 1), δ j ≤ ε / 4 :=
    (hsum.sum_le_tsum _ (fun j _ => hδnn j)).trans hδsum
  exact htot.trans (mul_le_mul_of_nonneg_right hδl (Nat.cast_nonneg _))

open AppendixAAux in
/-- **Claim A.4** (`claim:quotassuffice`): under the hypotheses of Claim A.3 (nested scales
`StrictMono D.h`, `0 < α_j < γ_j`, `α_j/γ_j ≤ δ_j`, `∑ δ_j ≤ ε/4`) and `0 < ε ≤ 1/4`, if White meets the
quota `(1/2 - ε/2)|Q|` of every retained local requirement at the levels `j ≤ l` (every eligible
rectangle inside a scale-`j` cube whose remainder has at least `α_j` points), then every eligible
rectangle `R` inside a scale-`l` cube has `|W ∩ R| ≥ (1/2 - ε)|E ∩ R|`. Only the levels the
decomposition of `R` uses are assumed, as in the paper's retained levels `0, …, J`. -/
theorem claim_quotassuffice {d : ℕ} (D : Scales) (hD : StrictMono D.h) (E : Finset (Pt d)) (ε : ℝ)
    (hε : 0 < ε)
    (hε' : ε ≤ 1 / 4) (δ : ℕ → ℝ) (hpos : ∀ j, 0 < D.α j ∧ D.α j < D.γ j)
    (hδ : ∀ j, D.α j / D.γ j ≤ δ j) (hδnn : ∀ j, 0 ≤ δ j) (hsum : Summable δ)
    (hδsum : ∑' j, δ j ≤ ε / 4) (W : Set (Pt d))
    (l : ℕ) (hquota : ∀ j ≤ l, ∀ (R' : Rect d), (∃ c, R'.pts ⊆ {y | cubeIdx D j y = c}) →
      D.γ j ≤ ((↑E ∩ R'.pts : Set (Pt d)).ncard : ℝ) →
      D.α j ≤ ((remainder D E R'.pts j).ncard : ℝ) →
      (1 / 2 - ε / 2) * ((remainder D E R'.pts j).ncard : ℝ) ≤
        ((W ∩ remainder D E R'.pts j).ncard : ℝ))
    (R : Rect d) (hRcube : ∃ c, R.pts ⊆ {y | cubeIdx D l y = c})
    (helig : D.γ l ≤ ((↑E ∩ R.pts : Set (Pt d)).ncard : ℝ)) :
    (1 / 2 - ε) * ((↑E ∩ R.pts : Set (Pt d)).ncard : ℝ) ≤ ((W ∩ R.pts).ncard : ℝ) := by
  classical
  have hdisc := claim_discardsmall D hD E ε δ hpos hδ hδnn hsum hδsum l R hRcube helig
  set F : Pt d → ℕ × Set (Pt d) := fun x => finalPiece D E x l R.pts with hF
  set ER := E.filter (· ∈ R.pts) with hER
  have hERset : (↑E ∩ R.pts : Set (Pt d)) = ↑ER := by ext y; simp [hER]
  set Disc := ER.filter (fun x => ((remainder D E (F x).2 (F x).1).ncard : ℝ) < D.α (F x).1)
    with hDisc
  have hset : {x | x ∈ E ∧ x ∈ R.pts ∧
        ((remainder D E (finalPiece D E x l R.pts).2 (finalPiece D E x l R.pts).1).ncard : ℝ) <
          D.α (finalPiece D E x l R.pts).1} = ↑Disc := by
    ext y; simp [hDisc, hER, hF, and_assoc]
  rw [hset, Set.ncard_coe_finset, hERset, Set.ncard_coe_finset] at hdisc
  rw [hERset, Set.ncard_coe_finset]
  set Ret := ER.filter (fun x => ¬ (((remainder D E (F x).2 (F x).1).ncard : ℝ) < D.α (F x).1))
    with hRet
  have hsplit : (Disc.card : ℝ) + Ret.card = ER.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not _
  have hdata := fun x (hx : x ∈ R.pts) => finalPiece_data D hD E hRcube helig hx
  have hcube : ∀ j ∈ Finset.range (l + 1), ∀ c ∈ ER.image (cubeIdx D j),
      (1 / 2 - ε / 2) *
          (((Ret.filter (fun x => (F x).1 = j)).filter (fun x => cubeIdx D j x = c)).card : ℝ) ≤
        ((((Ret.filter (· ∈ W)).filter (fun x => (F x).1 = j)).filter
          (fun x => cubeIdx D j x = c)).card : ℝ) := by
    intro j hj c _
    set G := (Ret.filter (fun x => (F x).1 = j)).filter (fun x => cubeIdx D j x = c) with hG
    have hGW : ((Ret.filter (· ∈ W)).filter (fun x => (F x).1 = j)).filter
        (fun x => cubeIdx D j x = c) = G.filter (· ∈ W) := by
      ext y; simp only [hG, Finset.mem_filter]; tauto
    rw [hGW]
    rcases G.eq_empty_or_nonempty with h0 | ⟨x0, hx0⟩
    · rw [h0, Finset.card_empty, Nat.cast_zero, mul_zero]
      exact Nat.cast_nonneg _
    have m1 := Finset.mem_filter.1 hx0
    have m2 := Finset.mem_filter.1 m1.1
    have m3 := Finset.mem_filter.1 m2.1
    have m4 := Finset.mem_filter.1 m3.1
    have hx0R : x0 ∈ R.pts := m4.2
    have hx0ret := m3.2
    have hx0j : (F x0).1 = j := m2.2
    have hx0c : cubeIdx D j x0 = c := m1.2
    obtain ⟨-, e0, g0, -⟩ := hdata x0 hx0R
    have hx0j' : (finalPiece D E x0 l R.pts).1 = j := hx0j
    rw [hx0j'] at e0 g0
    have e0' : (F x0).2 = R.pts ∩ {y | cubeIdx D j y = cubeIdx D j x0} := e0
    have hGeq : G = E.filter (· ∈ remainder D E (F x0).2 (F x0).1) := by
      ext y
      constructor
      · intro hy
        have n1 := Finset.mem_filter.1 hy
        have n2 := Finset.mem_filter.1 n1.1
        have n3 := Finset.mem_filter.1 n2.1
        have n4 := Finset.mem_filter.1 n3.1
        have hyE : y ∈ E := n4.1
        have hyR : y ∈ R.pts := n4.2
        have hyj : (F y).1 = j := n2.2
        have hyc : cubeIdx D j y = c := n1.2
        obtain ⟨-, ey, -, ny⟩ := hdata y hyR
        have hyj' : (finalPiece D E y l R.pts).1 = j := hyj
        rw [hyj'] at ey
        have hFy : F y = F x0 := by
          refine Prod.ext (hyj.trans hx0j.symm) ?_
          show (finalPiece D E y l R.pts).2 = (F x0).2
          rw [ey, e0', hyc, hx0c]
        have hymem : y ∈ remainder D E (F y).2 (F y).1 := by
          refine ⟨hyE, ?_, ny⟩
          show y ∈ (finalPiece D E y l R.pts).2
          rw [ey]
          exact ⟨hyR, rfl⟩
        rw [hFy] at hymem
        exact Finset.mem_filter.2 ⟨hyE, hymem⟩
      · intro hy
        obtain ⟨hyE, hyrem⟩ := Finset.mem_filter.1 hy
        obtain ⟨-, hyP, nsel⟩ := hyrem
        rw [e0'] at hyP
        obtain ⟨hyR, hyc0⟩ := hyP
        have hyc0' : cubeIdx D j y = cubeIdx D j x0 := hyc0
        have hFy : F y = F x0 :=
          finalPiece_congr D hD E l R.pts x0 y
            (fun m hm => cube_mono D hD (hx0j' ▸ hm) hyc0') nsel
        refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_filter.2
          ⟨Finset.mem_filter.2 ⟨hyE, hyR⟩, ?_⟩, hFy ▸ hx0j⟩, hyc0'.trans hx0c⟩
        rw [hFy]; exact hx0ret
    obtain ⟨R', hR'⟩ := rect_inter_cube D R j hx0R
    have hremR' : remainder D E R'.pts j = remainder D E (F x0).2 (F x0).1 := by
      rw [hR', ← e0', hx0j]
    have hq := hquota j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) R'
      ⟨cubeIdx D j x0, by rw [hR']; exact Set.inter_subset_right⟩
      (by
        rw [hR', ← Set.inter_assoc]
        exact g0)
      (by
        rw [hremR', hx0j]
        rw [hx0j] at hx0ret
        exact not_lt.1 hx0ret)
    rw [hremR'] at hq
    rw [hGeq, ← remainder_ncard, ← inter_remainder_ncard]
    exact hq
  have hmain : (1 / 2 - ε / 2) * (Ret.card : ℝ) ≤ ((Ret.filter (· ∈ W)).card : ℝ) := by
    have hmapR : ∀ x ∈ Ret, (F x).1 ∈ Finset.range (l + 1) := fun x hx =>
      Finset.mem_range.2 (Nat.lt_succ_of_le
        (hdata x (Finset.mem_filter.1 (Finset.mem_of_mem_filter x hx)).2).1)
    rw [Finset.card_eq_sum_card_fiberwise (f := fun x => (F x).1) (t := Finset.range (l + 1)) hmapR,
      Finset.card_eq_sum_card_fiberwise (f := fun x => (F x).1) (t := Finset.range (l + 1))
        (fun x hx => hmapR x (Finset.mem_of_mem_filter x hx))]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hmapC : ∀ x ∈ Ret.filter (fun x => (F x).1 = j), cubeIdx D j x ∈ ER.image (cubeIdx D j) :=
      fun x hx => Finset.mem_image_of_mem _ (Finset.mem_of_mem_filter x
        (Finset.mem_of_mem_filter x hx))
    rw [Finset.card_eq_sum_card_fiberwise (f := cubeIdx D j) (t := ER.image (cubeIdx D j)) hmapC,
      Finset.card_eq_sum_card_fiberwise (f := cubeIdx D j) (t := ER.image (cubeIdx D j))
        (s := (Ret.filter (· ∈ W)).filter (fun x => (F x).1 = j))
        (fun x hx => Finset.mem_image_of_mem _ (Finset.mem_of_mem_filter x
          (Finset.mem_of_mem_filter x (Finset.mem_of_mem_filter x hx))))]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (hcube j hj)
  have hW : ((Ret.filter (· ∈ W)).card : ℝ) ≤ ((W ∩ R.pts).ncard : ℝ) := by
    rw [← Set.ncard_coe_finset]
    refine Nat.cast_le.2 (Set.ncard_le_ncard ?_ ((Set.finite_Icc R.lo R.hi).subset fun y hy => hy.2))
    intro y hy
    have k1 := Finset.mem_filter.1 hy
    exact ⟨k1.2, (Finset.mem_filter.1 (Finset.mem_of_mem_filter y k1.1)).2⟩
  have hN : (0 : ℝ) ≤ ER.card := Nat.cast_nonneg _
  have h1 : (1 - ε / 4) * (ER.card : ℝ) ≤ Ret.card := by linarith
  have h2 : (1 / 2 - ε / 2) * ((1 - ε / 4) * (ER.card : ℝ)) ≤ (1 / 2 - ε / 2) * Ret.card :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  have h3 : (1 / 2 - ε) * (ER.card : ℝ) ≤ (1 / 2 - ε / 2) * ((1 - ε / 4) * (ER.card : ℝ)) := by
    nlinarith [mul_nonneg (mul_nonneg hε.le hε.le) hN, mul_nonneg hε.le hN]
  linarith

namespace AppendixAAux

variable {d : ℕ}

/-! ### Helpers (appA2): from the potential strategy to the claim game (Proposition A.5) -/

/-- The Black claims of a move sequence, in order. -/
def claimsOf : List (BMove d) → List (Pt d) :=
  List.filterMap fun m => match m with
    | .claim x => some x
    | .down => none

theorem claimsOf_nil : claimsOf ([] : List (BMove d)) = [] := rfl

theorem claimsOf_claim (ms : List (BMove d)) (x : Pt d) :
    claimsOf (ms ++ [.claim x]) = claimsOf ms ++ [x] := by
  unfold claimsOf; rw [List.filterMap_append]; rfl

/-- White's potential strategy as a strategy of the claim game: after Black's claim `x`, replay
Black's earlier claims and answer as the round of Lemma A.2 does. -/
def potStrategy (T : RegionTree d) (Pot : T.V → T.State → ℝ) : WStrategy d := fun ms =>
  match ms.getLast? with
  | some (.claim x) => (T.round Pot (T.run Pot (claimsOf ms.dropLast)) x).2
  | _ => none

theorem potStrategy_claim (T : RegionTree d) (Pot : T.V → T.State → ℝ) (ms : List (BMove d))
    (x : Pt d) :
    potStrategy T Pot (ms ++ [.claim x]) = (T.round Pot (T.run Pot (claimsOf ms)) x).2 := by
  unfold potStrategy
  rw [List.getLast?_concat, List.dropLast_concat]

section
variable (T : RegionTree d) (Pot : T.V → T.State → ℝ)

theorem run_append (bs : List (Pt d)) (x : Pt d) :
    T.run Pot (bs ++ [x]) = (T.round Pot (T.run Pot bs) x).1 := by
  unfold RegionTree.run; rw [List.foldl_append]; rfl

theorem activationStep_black (s : T.State) : (T.activationStep Pot s).black = s.black := by
  unfold RegionTree.activationStep; dsimp only; split_ifs <;> rfl

theorem activationStep_white (s : T.State) : (T.activationStep Pot s).white = s.white := by
  unfold RegionTree.activationStep; dsimp only; split_ifs <;> rfl

theorem round_black (s : T.State) (x : Pt d) :
    (T.round Pot s x).1.black = insert x s.black := by
  unfold RegionTree.round; dsimp only
  rcases T.reply Pot _ _ with _ | y
  · exact activationStep_black T Pot _
  · exact activationStep_black T Pot _

theorem round_white (s : T.State) (x : Pt d) :
    (T.round Pot s x).1.white = (T.round Pot s x).2.elim s.white (insert · s.white) := by
  unfold RegionTree.round; dsimp only
  rcases T.reply Pot _ _ with _ | y
  · exact activationStep_white T Pot _
  · show insert y (T.activationStep Pot _).white = _
    rw [activationStep_white]; rfl

theorem round_reply (s : T.State) (x : Pt d) {y : Pt d} (h : (T.round Pot s x).2 = some y) :
    y ∈ T.eff (T.activationStep Pot (T.blackClaim s x))
      (T.responsible (T.activationStep Pot (T.blackClaim s x)) x) ∧
    y ∉ insert x s.black ∧ y ∉ s.white := by
  have h' : T.reply Pot (T.activationStep Pot (T.blackClaim s x))
      (T.responsible (T.activationStep Pot (T.blackClaim s x)) x) = some y := h
  obtain ⟨h1, h2, -⟩ := reply_some Pot h'
  refine ⟨h1, ?_, ?_⟩
  · have := h2.1; rwa [activationStep_black] at this
  · have := h2.2; rwa [activationStep_white] at this

end

/-- Along a play of the claim game consistent with the potential strategy, Black's claims form a
legal sequence of the abstract game and the claimed points agree with the abstract run. -/
theorem reach_inv (T : RegionTree d) (Pot : T.V → T.State → ℝ) (E : Finset (Pt d))
    (hE : T.E T.root = E) (Rs : Finset (Rect d)) (q : ℝ) {ms : List (BMove d)}
    {st : (claimGame E Rs q).State} (h : (claimGame E Rs q).Reach (potStrategy T Pot) ms st) :
    T.LegalBlack Pot (claimsOf ms) ∧ st.black = ↑(T.run Pot (claimsOf ms)).black ∧
      st.white = ↑(T.run Pot (claimsOf ms)).white := by
  induction h with
  | nil =>
    refine ⟨fun k hk => absurd hk (by simp [claimsOf_nil]), ?_, ?_⟩ <;>
      simp [claimsOf_nil, RegionTree.run, StopGame.init, StopGame.State.black,
        StopGame.State.white, RegionTree.init, RegionTree.State.black, RegionTree.State.white]
  | @claim ms st x _ hfree _ ih =>
    obtain ⟨hleg, hb, hw⟩ := ih
    have hxE : x ∈ E := hfree.1
    have hxu : T.Unused (T.run Pot (claimsOf ms)) x :=
      ⟨fun h => hfree.2.1 (hb ▸ (Finset.mem_coe.2 h)), fun h => hfree.2.2 (hw ▸ Finset.mem_coe.2 h)⟩
    rw [claimsOf_claim]
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      rw [List.length_append, List.length_singleton] at hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | rfl
      · have h1 : (claimsOf ms ++ [x]).get ⟨k, by simpa using hk⟩ = (claimsOf ms).get ⟨k, hk'⟩ := by
          simp [List.getElem_append_left hk']
        rw [h1, List.take_append_of_le_length hk'.le]
        exact hleg k hk'
      · have h1 : (claimsOf ms ++ [x]).get ⟨(claimsOf ms).length, by simp⟩ = x := by simp
        rw [h1, List.take_left']
        · exact ⟨hE ▸ hxE, hxu⟩
        · rfl
    · show insert x st.black = _
      rw [run_append, round_black, Finset.coe_insert, hb]
    · show (potStrategy T Pot (ms ++ [.claim x])).elim st.white (insert · st.white) = _
      rw [run_append, round_white, potStrategy_claim, hw]
      rcases (T.round Pot (T.run Pot (claimsOf ms)) x).2 with _ | y
      · rfl
      · simp
  | @down ms st i _ hi _ =>
    exfalso
    have := st.level.isLt
    have hr : (claimGame E Rs q).r = 0 := rfl
    omega

/-- The replies of the potential strategy are legal in the claim game. -/
theorem potStrategy_legal (T : RegionTree d) (hT : T.WellFormed) (Pot : T.V → T.State → ℝ)
    (E : Finset (Pt d)) (hE : T.E T.root = E) (Rs : Finset (Rect d)) (q : ℝ)
    {ms : List (BMove d)} {st : (claimGame E Rs q).State}
    (h : (claimGame E Rs q).Reach (potStrategy T Pot) ms st) (x : Pt d) :
    (claimGame E Rs q).LegalReply ⟨st.level, insert x st.black, st.white⟩
      (potStrategy T Pot (ms ++ [.claim x])) := by
  obtain ⟨-, hb, hw⟩ := reach_inv T Pot E hE Rs q h
  rw [potStrategy_claim]
  rcases hrep : (T.round Pot (T.run Pot (claimsOf ms)) x).2 with _ | y
  · trivial
  · obtain ⟨h1, h2, h3⟩ := round_reply T Pot _ x hrep
    refine ⟨?_, ?_, ?_⟩
    · show y ∈ (↑E : Set (Pt d))
      exact Finset.mem_coe.2 (hE ▸ eff_sub_root hT _ _ h1)
    · show y ∉ insert x st.black
      rw [hb, ← Finset.coe_insert]; exact fun h => h2 (Finset.mem_coe.1 h)
    · show y ∉ st.white
      rw [hw]; exact fun h => h3 (Finset.mem_coe.1 h)

/-! #### Geometry: a rectangle with short sides meets few cubes -/

theorem ediv_mem_pair {a b t : ℤ} (hb : 0 < b) (h1 : a ≤ t) (h2 : t ≤ a + b - 1) :
    t / b = a / b ∨ t / b = a / b + 1 := by
  have k1 : a / b ≤ t / b := Int.ediv_le_ediv hb h1
  have k2 : t / b ≤ (a + b) / b := Int.ediv_le_ediv hb (by omega)
  have k3 : (a + b) / b = a / b + 1 := by
    rw [Int.add_ediv_of_dvd_right (dvd_refl b), Int.ediv_self hb.ne']
  omega

/-- If every side of `R` is at most `2^{h_j}`, the points of `R` lie in at most `2^d` scale-`j`
cubes. -/
theorem card_cubes_le (D : Scales) (j : ℕ) (R : Rect d)
    (hside : ∀ i, R.hi i - R.lo i + 1 ≤ 2 ^ D.h j) (S : Finset (Pt d)) (hS : ∀ y ∈ S, y ∈ R.pts) :
    (S.image (cubeIdx D j)).card ≤ 2 ^ d := by
  have hb : (0 : ℤ) < 2 ^ D.h j := by positivity
  have hsub : S.image (cubeIdx D j) ⊆
      Fintype.piFinset fun i => ({R.lo i / 2 ^ D.h j, R.lo i / 2 ^ D.h j + 1} : Finset ℤ) := by
    intro c hc
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hc
    rw [Fintype.mem_piFinset]
    intro i
    have hyR := hS y hy
    have := ediv_mem_pair hb (hyR.1 i) (by have := hyR.2 i; have := hside i; linarith)
    unfold cubeIdx
    rcases this with h | h <;> simp [h]
  refine (Finset.card_le_card hsub).trans ?_
  rw [Fintype.card_piFinset]
  calc ∏ i : Fin d, ({R.lo i / 2 ^ D.h j, R.lo i / 2 ^ D.h j + 1} : Finset ℤ).card
      ≤ ∏ _i : Fin d, 2 := Finset.prod_le_prod' (fun _ _ => Finset.card_le_two)
    _ = 2 ^ d := by simp

/-- A side of a rectangle is at most its volume. -/
theorem side_le_vol (R : Rect d) (i : Fin d) : R.hi i - R.lo i + 1 ≤ (R.vol : ℤ) := by
  have hinj : Set.InjOn (fun t : ℤ => Function.update R.lo i t) (Set.Icc (R.lo i) (R.hi i)) :=
    fun a _ b _ h => by simpa using congrFun h i
  have hmaps : Set.MapsTo (fun t : ℤ => Function.update R.lo i t) (Set.Icc (R.lo i) (R.hi i))
      R.pts := by
    intro t ht
    refine ⟨fun k => ?_, fun k => ?_⟩
    · by_cases hk : k = i
      · subst hk; simpa using ht.1
      · simp [Function.update_of_ne hk]
    · by_cases hk : k = i
      · subst hk; simpa using ht.2
      · simp [Function.update_of_ne hk, R.le k]
  have := Set.ncard_le_ncard_of_injOn _ hmaps hinj (Set.finite_Icc _ _)
  rw [← Finset.coe_Icc, Set.ncard_coe_finset, Int.card_Icc] at this
  unfold Rect.vol
  have h0 : R.lo i ≤ R.hi i := R.le i
  omega

/-- Counting over the pieces of `R` cut by scale-`j` cubes. Let every side of the rectangle `R` be
at most `2^{h_j}` (so `R` meets at most `2^d` scale-`j` cubes) and let `q, γ ≥ 0`. If every
eligible piece (at least `γ` points of `E`) inside one cube gets a `q` fraction of White points,
then `R` gets `q (|E ∩ R| - 2^d γ)`. -/
theorem split_count (D : Scales) (j : ℕ) (E W : Finset (Pt d)) (R : Rect d)
    (hside : ∀ i, R.hi i - R.lo i + 1 ≤ 2 ^ D.h j) {q γ : ℝ} (hq : 0 ≤ q) (hγ : 0 ≤ γ)
    (hpiece : ∀ R' : Rect d, (∃ c, R'.pts ⊆ {y | cubeIdx D j y = c}) →
      γ ≤ ((↑E ∩ R'.pts : Set (Pt d)).ncard : ℝ) →
      q * ((↑E ∩ R'.pts : Set (Pt d)).ncard : ℝ) ≤ ((↑W ∩ R'.pts : Set (Pt d)).ncard : ℝ)) :
    q * (((↑E ∩ R.pts : Set (Pt d)).ncard : ℝ) - 2 ^ d * γ) ≤
      ((↑W ∩ R.pts : Set (Pt d)).ncard : ℝ) := by
  set ER := E.filter (· ∈ R.pts) with hER
  set WR := W.filter (· ∈ R.pts) with hWR
  set I := ER.image (cubeIdx D j) with hI
  have hEset : (↑E ∩ R.pts : Set (Pt d)) = ↑ER := by ext y; simp [hER]
  have hWset : (↑W ∩ R.pts : Set (Pt d)) = ↑WR := by ext y; simp [hWR]
  rw [hEset, hWset, Set.ncard_coe_finset, Set.ncard_coe_finset]
  have hIcard : (I.card : ℝ) ≤ 2 ^ d := by
    exact_mod_cast card_cubes_le D j R hside ER fun y hy => (Finset.mem_filter.1 hy).2
  -- per-piece bound
  have hper : ∀ c ∈ I, q * (((ER.filter fun y => cubeIdx D j y = c).card : ℝ) - γ) ≤
      ((WR.filter fun y => cubeIdx D j y = c).card : ℝ) := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨R', hR'⟩ := rect_inter_cube D R j (Finset.mem_filter.1 hx).2
    have hE' : (↑E ∩ R'.pts : Set (Pt d)) = ↑(ER.filter fun y => cubeIdx D j y = cubeIdx D j x) := by
      ext y; simp [hR', hER, and_assoc]
    have hW' : (↑W ∩ R'.pts : Set (Pt d)) = ↑(WR.filter fun y => cubeIdx D j y = cubeIdx D j x) := by
      ext y; simp [hR', hWR, and_assoc]
    have hsub : ∃ c, R'.pts ⊆ {y | cubeIdx D j y = c} :=
      ⟨cubeIdx D j x, by rw [hR']; exact Set.inter_subset_right⟩
    by_cases hel : γ ≤ ((↑E ∩ R'.pts : Set (Pt d)).ncard : ℝ)
    · have := hpiece R' hsub hel
      rw [hE', hW', Set.ncard_coe_finset, Set.ncard_coe_finset] at this
      nlinarith
    · rw [hE', Set.ncard_coe_finset] at hel
      have : (0 : ℝ) ≤ ((WR.filter fun y => cubeIdx D j y = cubeIdx D j x).card : ℝ) := by positivity
      nlinarith
  have hEsum : (ER.card : ℝ) = ∑ c ∈ I, ((ER.filter fun y => cubeIdx D j y = c).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise fun y hy => Finset.mem_image_of_mem _ hy
  have hWsum : ∑ c ∈ I, ((WR.filter fun y => cubeIdx D j y = c).card : ℝ) ≤ (WR.card : ℝ) := by
    have := Finset.card_eq_sum_card_fiberwise (s := WR.filter fun y => cubeIdx D j y ∈ I)
      (t := I) (f := cubeIdx D j) fun y hy => (Finset.mem_filter.1 hy).2
    have h2 : ((WR.filter fun y => cubeIdx D j y ∈ I).card : ℝ) ≤ WR.card := by
      exact_mod_cast Finset.card_filter_le _ _
    have h3 : ∀ c ∈ I, ((WR.filter fun y => cubeIdx D j y ∈ I).filter fun y => cubeIdx D j y = c) =
        WR.filter fun y => cubeIdx D j y = c := by
      intro c hc; ext y; simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ hc⟩, h3⟩
    rw [Finset.sum_congr rfl fun c hc => by rw [← h3 c hc]]
    exact_mod_cast (le_of_eq this.symm).trans (by exact_mod_cast h2)
  have hsum := Finset.sum_le_sum hper
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← hEsum, Finset.sum_const, nsmul_eq_mul] at hsum
  have : q * ((ER.card : ℝ) - 2 ^ d * γ) ≤ q * ((ER.card : ℝ) - I.card * γ) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hq
  linarith

/-- The local requirement of an eligible rectangle inside a scale-`j` cube (`j ≤ J`) with a large
remainder is a requirement of the dyadic tree, with quota `(1/2 - ε/2)|Q_R|`. -/
theorem mem_reqs_dyadic (D : Scales) (ε : ℝ) (E : Finset (Pt d)) (J j : ℕ) (hj : j ≤ J)
    (R : Rect d) (c : Pt d) (hc : R.pts ⊆ {y | cubeIdx D j y = c}) (hγ : 0 < D.γ j)
    (helig : D.γ j ≤ ((↑E ∩ R.pts : Set (Pt d)).ncard : ℝ))
    (hα : D.α j ≤ ((remainder D E R.pts j).ncard : ℝ)) :
    ∃ v, E.filter (· ∈ remainder D E R.pts j) ∈ (dyadicTree D ε E J).reqs v ∧
      (dyadicTree D ε E J).quota v (E.filter (· ∈ remainder D E R.pts j)) =
        (1 / 2 - ε / 2) * (E.filter (· ∈ remainder D E R.pts j)).card := by
  have hne : (↑E ∩ R.pts : Set (Pt d)).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Set.ncard_empty] at helig
    push_cast at helig; linarith
  obtain ⟨x, hxE, hxR⟩ := hne
  have hxc : cubeIdx D j x = c := hc hxR
  have hmem := (mem_cubes_iff D E (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (J + 1)) c).2 ⟨x, hxE, hxc⟩
  refine ⟨some ⟨((⟨j, Nat.lt_succ_of_le hj⟩ : Fin (J + 1)), c), hmem⟩, ?_, rfl⟩
  have hlo := (cubeIdx_eq_iff D j R.lo c).1 (hc (Set.left_mem_Icc.2 R.le))
  have hhi := (cubeIdx_eq_iff D j R.hi c).1 (hc (Set.right_mem_Icc.2 R.le))
  dsimp only [dyadicTree, RegionTree.reqs]
  rw [Finset.mem_image]
  refine ⟨(R.lo, R.hi), ?_, ?_⟩
  · rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨⟨fun i => (hlo i).1, fun i => (hlo i).2⟩, ⟨fun i => (hhi i).1, fun i => (hhi i).2⟩⟩,
      R.le, helig, hα⟩
  · ext y; simp only [Finset.mem_filter, Rect.pts]; exact Finset.mem_filter.symm

theorem dyadic_E_root (D : Scales) (ε : ℝ) (E : Finset (Pt d)) (J : ℕ) :
    (dyadicTree D ε E J).E (dyadicTree D ε E J).root = E := rfl

/-- The scale bound used in Proposition A.5: the predecessor-size condition `hmin` gives
`γ_j ≤ K h_τ(V(R))`, with `K = c / (log 2)^{1+τ}`. No fitting-size condition on scale `j`
is assumed; at `j = 0`, `hmin` is vacuous. Choosing the least fitting scale is an application. -/
theorem gamma_le_hTau (D : Scales) {c τ : ℝ} (hτ : 0 < τ) (hc : 0 < c) (hγ0 : D.γ 0 ≤ c)
    (hγ : ∀ j, D.γ (j + 1) ≤ c * (D.h j : ℝ) ^ (1 + τ)) (R : Rect d) (j : ℕ)
    (hmin : ∀ k, j = k + 1 → ∃ i, (2 : ℤ) ^ D.h k < R.hi i - R.lo i + 1) :
    D.γ j ≤ c / Real.log 2 ^ (1 + τ) * hTau τ R.vol := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hV1 : (1 : ℝ) ≤ R.vol := by exact_mod_cast BasicAux.rect_vol_pos R
  have hL : Real.log 2 ≤ Real.log (2 + R.vol) := Real.log_le_log (by norm_num) (by linarith)
  have hp : (0 : ℝ) < Real.log 2 ^ (1 + τ) := Real.rpow_pos_of_pos hlog2 _
  unfold hTau
  rcases j with _ | k
  · calc D.γ 0 ≤ c := hγ0
      _ = c / Real.log 2 ^ (1 + τ) * Real.log 2 ^ (1 + τ) := (div_mul_cancel₀ _ hp.ne').symm
      _ ≤ c / Real.log 2 ^ (1 + τ) * Real.log (2 + R.vol) ^ (1 + τ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hlog2.le hL (by linarith))
            (div_pos hc hp).le
  · obtain ⟨i, hi⟩ := hmin k rfl
    have hside := side_le_vol R i
    have hVZ : (2 : ℤ) ^ D.h k < R.vol := lt_of_lt_of_le hi hside
    have hVR : (2 : ℝ) ^ D.h k < R.vol := by exact_mod_cast hVZ
    have hhk : (D.h k : ℝ) * Real.log 2 < Real.log (2 + R.vol) := by
      rw [← Real.log_pow]
      exact Real.log_lt_log (by positivity) (by linarith)
    have hhk' : (D.h k : ℝ) ≤ Real.log (2 + R.vol) / Real.log 2 := by
      rw [le_div_iff₀ hlog2]; exact hhk.le
    calc D.γ (k + 1) ≤ c * (D.h k : ℝ) ^ (1 + τ) := hγ k
      _ ≤ c * (Real.log (2 + R.vol) / Real.log 2) ^ (1 + τ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hhk' (by linarith))
            hc.le
      _ = c / Real.log 2 ^ (1 + τ) * Real.log (2 + R.vol) ^ (1 + τ) := by
          rw [Real.div_rpow (by linarith) hlog2.le]; ring

end AppendixAAux

/-- The conditions (G1)–(G3) of Proposition A.5 for accuracy `ε` and constant `c`: (G1)
`∑ α_j/γ_j ≤ ε/4`; (G2) `γ_0 ≤ c` and `γ_j ≤ c h_{j-1}^{1+τ}`; (G3) for every board `E` and every
number of retained levels, the dyadic tree's local requirements admit potentials with the
locality properties and (P1)–(P4). The exponents are strictly increasing, `0 < α_j < γ_j`, the
series `∑ α_j/γ_j` is summable (so (G1) is meaningful); `dyadicTree D ε E J` `WellFormed` is a
condition of the Lean encoding of the tree, not part of the paper's (G1)–(G3). -/
def ScaleConditions (d : ℕ) (D : Scales) (ε τ c : ℝ) : Prop :=
  StrictMono D.h ∧ (∀ j, 0 < D.α j ∧ D.α j < D.γ j) ∧
  Summable (fun j => D.α j / D.γ j) ∧ ∑' j, D.α j / D.γ j ≤ ε / 4 ∧
  D.γ 0 ≤ c ∧ (∀ j, D.γ (j + 1) ≤ c * (D.h j : ℝ) ^ (1 + τ)) ∧
  ∀ (E : Finset (Pt d)) (J : ℕ), (dyadicTree D ε E J).WellFormed ∧
    ∃ (Pot : (dyadicTree D ε E J).V → (dyadicTree D ε E J).State → ℝ) (σ : ℝ),
      (dyadicTree D ε E J).PotentialProps Pot σ

open AppendixAAux in
/-- **Proposition A.5** (`prop:cf-conditional`): if for every `0 < ε ≤ 1/4` some retained scales and
thresholds satisfy (G1)–(G3) with a constant `c_{d,ε,τ}`, then Lemma 9.1 holds. -/
theorem prop_cf_conditional {d : ℕ} (hd : 2 ≤ d) {τ : ℝ} (hτ : 0 < τ)
    (hG : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 → ∃ (D : Scales) (c : ℝ), ScaleConditions d D ε τ c) :
    ∀ η : ℝ, 0 < η → η < 1 / 2 →
      ∃ C : ℝ, 0 < C ∧ ∀ (E : Finset (Pt d)) (Rs : Finset (Rect d)),
        (claimGame E (Rs.filter fun R =>
            C * hTau τ R.vol ≤ ((↑E ∩ R.pts : Set (Pt d)).ncard : ℝ)) (1 / 2 - η)).Feasible := by
  intro η hη hη2
  set ε := min η (1 / 4) / 2 with hεdef
  have hmin_pos : 0 < min η (1 / 4) := lt_min hη (by norm_num)
  have hε : 0 < ε := by positivity
  have hε4 : ε ≤ 1 / 4 := by have := min_le_right η (1 / 4); linarith
  have hεη : ε ≤ η / 2 := by have := min_le_left η (1 / 4); linarith
  obtain ⟨D, c, hD, hpos, hsum, hG1, hγ0, hγ, hG3⟩ := hG ε hε hε4
  have hc : 0 < c := ((hpos 0).1.trans (hpos 0).2).trans_le hγ0
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set K := c / Real.log 2 ^ (1 + τ) with hK
  have hKpos : 0 < K := div_pos hc (Real.rpow_pos_of_pos hlog2 _)
  refine ⟨2 ^ d * K / ε, by positivity, ?_⟩
  intro E Rs
  -- the number of retained levels: every requested rectangle fits in a scale-`J` cube
  set J := ∑ R ∈ Rs, ∑ i, (R.hi i - R.lo i + 1).toNat with hJ
  have hJside : ∀ R ∈ Rs, ∀ i, R.hi i - R.lo i + 1 ≤ 2 ^ D.h J := by
    intro R hR i
    have h1 : (R.hi i - R.lo i + 1).toNat ≤ J :=
      (Finset.single_le_sum (f := fun i => (R.hi i - R.lo i + 1).toNat) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)).trans
        (Finset.single_le_sum (f := fun R => ∑ i, (R.hi i - R.lo i + 1).toNat)
          (fun _ _ => Nat.zero_le _) hR)
    have h2 : J < 2 ^ D.h J := (Nat.lt_two_pow_self).trans_le
      (Nat.pow_le_pow_right (by norm_num) (hD.id_le J))
    have h3 : ((J : ℕ) : ℤ) < ((2 ^ D.h J : ℕ) : ℤ) := by exact_mod_cast h2
    push_cast at h3
    have h4 := Int.self_le_toNat (R.hi i - R.lo i + 1)
    omega
  set T := dyadicTree D ε E J with hTdef
  have hT : T.WellFormed := (hG3 E J).1
  obtain ⟨Pot, σ, hP⟩ := (hG3 E J).2
  refine ⟨potStrategy T Pot, fun ms st h => ⟨fun x _ =>
    potStrategy_legal T hT Pot E (dyadic_E_root D ε E J) _ _ h x, fun hstop R hR => ?_⟩⟩
  obtain ⟨hleg, hb, hw⟩ := reach_inv T Pot E (dyadic_E_root D ε E J) _ _ h
  set run := T.run Pot (claimsOf ms) with hrun
  have hcomplete : ∀ x ∈ T.E T.root, x ∈ run.black ∨ x ∈ run.white := by
    intro x hx
    rw [dyadic_E_root] at hx
    have : x ∈ st.black ∪ st.white := hstop (Finset.mem_coe.2 hx)
    rcases this with h1 | h1
    · left; rw [hb] at h1; exact Finset.mem_coe.1 h1
    · right; rw [hw] at h1; exact Finset.mem_coe.1 h1
  have hA := lem_new_abstract T hT Pot σ hP (claimsOf ms) hleg hcomplete
  have hR' : R ∈ Rs ∧ 2 ^ d * K / ε * hTau τ R.vol ≤ ((↑E ∩ R.pts : Set (Pt d)).ncard : ℝ) :=
    Finset.mem_filter.1 hR
  show (1 / 2 - η) * ((↑E ∩ R.pts : Set (Pt d)).ncard : ℝ) ≤ ((st.white ∩ ↑E ∩ R.pts).ncard : ℝ)
  -- the least scale whose cubes are as long as every side of `R`
  have hex : ∃ j, ∀ i, R.hi i - R.lo i + 1 ≤ 2 ^ D.h j := ⟨J, hJside R hR'.1⟩
  set j := Nat.find hex with hjdef
  have hjside : ∀ i, R.hi i - R.lo i + 1 ≤ 2 ^ D.h j := Nat.find_spec hex
  have hjJ : j ≤ J := Nat.find_min' hex (hJside R hR'.1)
  have hjmin : ∀ k, j = k + 1 → ∃ i, (2 : ℤ) ^ D.h k < R.hi i - R.lo i + 1 := by
    intro k hk
    have := Nat.find_min hex (show k < j by omega)
    push_neg at this
    exact this
  have hγj := gamma_le_hTau D hτ hc hγ0 hγ R j hjmin
  -- White's run meets every eligible piece inside a scale-`j` cube
  have hlocal : ∀ R' : Rect d, (∃ c', R'.pts ⊆ {y | cubeIdx D j y = c'}) →
      D.γ j ≤ ((↑E ∩ R'.pts : Set (Pt d)).ncard : ℝ) →
      (1 / 2 - ε) * ((↑E ∩ R'.pts : Set (Pt d)).ncard : ℝ) ≤
        ((↑(run.white ∩ E) ∩ R'.pts : Set (Pt d)).ncard : ℝ) := by
    intro R' hcube helig
    refine claim_quotassuffice D hD E ε hε hε4 (fun j => D.α j / D.γ j) hpos (fun _ => le_rfl)
      (fun j => div_nonneg (hpos j).1.le ((hpos j).1.trans (hpos j).2).le) hsum hG1
      ↑(run.white ∩ E) j ?_ R' hcube helig
    intro j' hj' R'' hcube' helig' hα'
    obtain ⟨c', hc'⟩ := hcube'
    obtain ⟨v, hv, hq⟩ := mem_reqs_dyadic D ε E J j' (hj'.trans hjJ) R'' c' hc'
      ((hpos j').1.trans (hpos j').2) helig' hα'
    have h1 := hA v _ hv
    rw [hq, ← remainder_ncard] at h1
    refine h1.trans ?_
    rw [inter_remainder_ncard]
    exact_mod_cast Finset.card_le_card fun y hy => by
      obtain ⟨hy1, hy2⟩ := Finset.mem_inter.1 hy
      have hy2' := Finset.mem_filter.1 hy2
      exact Finset.mem_filter.2 ⟨hy2, Finset.mem_coe.2 (Finset.mem_inter.2 ⟨hy1, hy2'.1⟩)⟩
  have hsplit := split_count D j E (run.white ∩ E) R hjside (q := 1 / 2 - ε) (γ := D.γ j)
    (by linarith) ((hpos j).1.trans (hpos j).2).le hlocal
  have hWeq : (↑(run.white ∩ E) ∩ R.pts : Set (Pt d)) = st.white ∩ ↑E ∩ R.pts := by
    rw [hw, Finset.coe_inter]
  rw [hWeq] at hsplit
  -- the ineligible pieces are few
  have hN : (0 : ℝ) ≤ ((↑E ∩ R.pts : Set (Pt d)).ncard : ℝ) := Nat.cast_nonneg _
  have hfew : 2 ^ d * D.γ j ≤ ε * ((↑E ∩ R.pts : Set (Pt d)).ncard : ℝ) := by
    have h1 : 2 ^ d * D.γ j ≤ 2 ^ d * (K * hTau τ R.vol) :=
      mul_le_mul_of_nonneg_left hγj (by positivity)
    have h2 : ε * (2 ^ d * K / ε * hTau τ R.vol) = 2 ^ d * (K * hTau τ R.vol) := by
      field_simp
    nlinarith [hR'.2]
  have h3 : (1 / 2 - ε) * (((↑E ∩ R.pts : Set (Pt d)).ncard : ℝ) -
      ε * ((↑E ∩ R.pts : Set (Pt d)).ncard : ℝ)) ≤
      (1 / 2 - ε) * (((↑E ∩ R.pts : Set (Pt d)).ncard : ℝ) - 2 ^ d * D.γ j) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  nlinarith [mul_nonneg hε.le hN, mul_nonneg (mul_nonneg hε.le hε.le) hN]



end

end BanachDensityHD
