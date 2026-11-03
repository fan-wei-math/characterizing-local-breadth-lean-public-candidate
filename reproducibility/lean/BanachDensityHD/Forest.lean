import BanachDensityHD.Separation

/-!
# Section 8.3: forest, boards, simulated games, the generator

Kleinberg–Wei, *Characterizing Local Breadth in Language Generation*.
Historical source numbering is retained; current mappings are in the release registry.

-/

namespace BanachDensityHD

open Set Filter
open scoped Classical



/-! ### The static protected forest (§8.3.2) and the critical guess -/

/-- `i` is a possible parent of `j` (§8.3.2): `i < j`, `L_j ⊊ L_i` and `P_i ⊆ L_j`. With
`strict = false` the label inclusion is nonstrict (`L_j ⊆ L_i`), as for accuracy copies (§8.5,
"allow equality of underlying language labels in the parent scan"). -/
def PossibleParent {d : ℕ} (strict : Bool) (lab : ℕ → Set (Pt d)) (P : ℕ → Set (Pt d))
    (i j : ℕ) : Prop :=
  i < j ∧ (if strict then lab j ⊂ lab i else lab j ⊆ lab i) ∧ P i ⊆ lab j

/-- The parent scan (§8.3.2): scan the possible parents of `j` in increasing index order, retain the
first, and replace the retained `p` by a later possible parent `i` whenever `L_i ⊆ L_p`; the final
retained vertex is the parent (`none`: `j` is a root). -/
noncomputable def scanParent {d : ℕ} (strict : Bool) (lab : ℕ → Set (Pt d)) (P : ℕ → Set (Pt d))
    (j : ℕ) : Option ℕ :=
  (List.range j).foldl (fun acc i =>
    if PossibleParent strict lab P i j then
      match acc with
      | none => some i
      | some p => if lab i ⊆ lab p then some i else some p
    else acc) none

/-- `a` is an ancestor of `v` (or `v` itself) in the forest given by `parent`. -/
inductive IsAncestor (parent : ℕ → Option ℕ) : ℕ → ℕ → Prop
  | refl (v : ℕ) : IsAncestor parent v v
  | step {a u v : ℕ} : IsAncestor parent a u → parent v = some u → IsAncestor parent a v

/-- Vertex `i` is consistent with the input set `S` (§8.3.2): `S ⊆ L_i`. -/
def Consistent {d : ℕ} (lab : ℕ → Set (Pt d)) (S : Set (Pt d)) (i : ℕ) : Prop := S ⊆ lab i

/-- Vertex `i` (one of the vertices `i < N`; `N = ⊤` for infinitely many) is critical for `S`:
consistent, and `L_i ⊆ L_u` for every earlier consistent `u`. -/
def Critical {d : ℕ} (N : ℕ∞) (lab : ℕ → Set (Pt d)) (S : Set (Pt d)) (i : ℕ) : Prop :=
  (i : ℕ∞) < N ∧ Consistent lab S i ∧ ∀ u < i, Consistent lab S u → lab i ⊆ lab u

/-- The current guess `Q_t` after the inputs `w 0, …, w t`: the largest-index critical vertex among
the first `t + 1` vertices (`none` if there is none); the vertices are the indices `i < N`. -/
noncomputable def guess {d : ℕ} (N : ℕ∞) (lab : ℕ → Set (Pt d)) (w : ℕ → Pt d) (t : ℕ) :
    Option ℕ :=
  let S : Set (Pt d) := {x | x ∈ inputsUpTo w t}
  if h : ∃ i ≤ t, Critical N lab S i then some (Nat.findGreatest (fun i => Critical N lab S i) t)
  else none

/-! ## Section B: Lemma 6.16 (capture) for the HD forest -/

namespace ForestAux

variable {d : ℕ}

/-- The input set `S_t = {w 0, …, w t}` as used by `guess`. -/
theorem mem_inputs {w : ℕ → Pt d} {t : ℕ} {x : Pt d} :
    x ∈ inputsUpTo w t ↔ ∃ i ≤ t, w i = x := by
  unfold inputsUpTo
  rw [List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨i, Nat.lt_succ_iff.1 i.2, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, Nat.lt_succ_iff.2 hi⟩, rfl⟩

/-- Every finite subset of the range of `w` eventually appears among the inputs. -/
theorem eventually_subset_inputs (w : ℕ → Pt d) {F : Set (Pt d)} (hF : F.Finite)
    (hFw : F ⊆ range w) : ∀ᶠ t in atTop, F ⊆ {x | x ∈ inputsUpTo w t} := by
  have : ∀ᶠ t in atTop, ∀ p ∈ F, p ∈ inputsUpTo w t := by
    rw [Filter.eventually_all_finite hF]
    intro p hp
    obtain ⟨i, rfl⟩ := hFw hp
    filter_upwards [eventually_ge_atTop i] with t ht
    exact mem_inputs.2 ⟨i, ht, rfl⟩
  filter_upwards [this] with t ht p hp
  exact ht p hp

/-- A successful possible-parent test implies that the child label `A` is a subset of
the parent label `B`; no reciprocal inclusion is asserted. -/
theorem sub_of_test {strict : Bool} {A B : Set (Pt d)}
    (h : if strict then A ⊂ B else A ⊆ B) : A ⊆ B := by
  cases strict
  · simpa using h
  · exact (by simpa using h : A ⊂ B).subset

/-- The parent scan of `v`, when `z < v` is a possible parent, every possible parent before `z`
has label containing `lab z`, and `lab v ⊆ lab z`: the retained parent is some `p` with `z ≤ p < v`
and `lab v ⊆ lab p ⊆ lab z`. -/
theorem scan_retains {strict : Bool} {lab P : ℕ → Set (Pt d)} {z v : ℕ} (hzv : z < v)
    (hz : PossibleParent strict lab P z v)
    (hbefore : ∀ i < z, PossibleParent strict lab P i v → lab z ⊆ lab i) :
    ∃ p, scanParent strict lab P v = some p ∧ z ≤ p ∧ p < v ∧ lab v ⊆ lab p ∧
      lab p ⊆ lab z := by
  -- invariant along the scan
  have key : ∀ k ≤ v,
      (k ≤ z → ∀ p, (List.range k).foldl (fun acc i =>
          if PossibleParent strict lab P i v then
            match acc with
            | none => some i
            | some p => if lab i ⊆ lab p then some i else some p
          else acc) none = some p → lab z ⊆ lab p) ∧
      (z < k → ∃ p, (List.range k).foldl (fun acc i =>
          if PossibleParent strict lab P i v then
            match acc with
            | none => some i
            | some p => if lab i ⊆ lab p then some i else some p
          else acc) none = some p ∧ z ≤ p ∧ p < k ∧ lab v ⊆ lab p ∧ lab p ⊆ lab z) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨fun _ p h => by simp at h, fun h => absurd h (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set acc := (List.range k).foldl (fun acc i =>
          if PossibleParent strict lab P i v then
            match acc with
            | none => some i
            | some p => if lab i ⊆ lab p then some i else some p
          else acc) none with hacc
      rcases lt_trichotomy k z with hkz | rfl | hkz
      · -- before `z`
        refine ⟨fun _ p hp => ?_, fun h => absurd h (by omega)⟩
        by_cases hpp : PossibleParent strict lab P k v
        · rw [if_pos hpp] at hp
          rcases hA : acc with _ | p'
          · rw [hA] at hp; cases hp; exact hbefore k hkz hpp
          · rw [hA] at hp
            simp only at hp
            split_ifs at hp
            · cases hp; exact hbefore k hkz hpp
            · cases hp; exact ih1 (by omega) p hA
        · rw [if_neg hpp] at hp; exact ih1 (by omega) p hp
      · -- at `z`
        refine ⟨fun h => absurd h (by omega), fun _ => ?_⟩
        rw [if_pos hz]
        rcases hA : acc with _ | p'
        · exact ⟨k, rfl, le_rfl, by omega, sub_of_test hz.2.1, subset_rfl⟩
        · have := ih1 le_rfl p' hA
          simp only [if_pos this]
          exact ⟨k, rfl, le_rfl, by omega, sub_of_test hz.2.1, subset_rfl⟩
      · -- after `z`
        refine ⟨fun h => absurd h (by omega), fun _ => ?_⟩
        obtain ⟨p, hp, hzp, hpk, hvp, hpz⟩ := ih2 hkz
        by_cases hpp : PossibleParent strict lab P k v
        · rw [if_pos hpp, hp]
          simp only
          split_ifs with hkp
          · exact ⟨k, rfl, by omega, by omega, sub_of_test hpp.2.1, hkp.trans hpz⟩
          · exact ⟨p, rfl, hzp, by omega, hvp, hpz⟩
        · rw [if_neg hpp, hp]
          exact ⟨p, rfl, hzp, by omega, hvp, hpz⟩
  exact (key v le_rfl).2 hzv

/-- **Lemma 6.16** (`lem:capture`), generalized to the HD forest (the core of Lemma 8.10, for
both the strict scan of the fixed-quota forest and the nonstrict scan of accuracy copies). Let `z`
be a vertex (`z < N`) with finite `P_z ⊆ L_z`, and, for the strict scan, let labels be injective
on the vertices. On every full enumeration of `L_z`, all sufficiently late guesses `Q_t` are
defined and lie in the subtree rooted at `z`. Only `P_z` is used; the protected sets of other
vertices, the cutoffs, the radii and the games play no role (as the manuscript says). -/
theorem capture_gen (strict : Bool) (N : ℕ∞) (lab P : ℕ → Set (Pt d))
    (hinj : strict = true →
      ∀ i j : ℕ, (i : ℕ∞) < N → (j : ℕ∞) < N → lab i = lab j → i = j)
    (z : ℕ) (hz : (z : ℕ∞) < N) (hPz : (P z).Finite ∧ P z ⊆ lab z) (w : ℕ → Pt d)
    (hw : IsFullEnumeration w (lab z)) :
    ∃ T, ∀ t ≥ T, ∃ v, guess N lab w t = some v ∧ IsAncestor (scanParent strict lab P) z v := by
  set K := lab z with hK
  -- the eventual conditions
  have hev : ∀ᶠ t in atTop, z ≤ t ∧ P z ⊆ {x | x ∈ inputsUpTo w t} ∧
      ∀ u < z, {x | x ∈ inputsUpTo w t} ⊆ lab u → K ⊆ lab u := by
    refine (eventually_ge_atTop z).and ((eventually_subset_inputs w hPz.1
      (hPz.2.trans hw.symm.subset)).and ?_)
    have : ∀ᶠ t in atTop, ∀ u ∈ Finset.range z, {x | x ∈ inputsUpTo w t} ⊆ lab u → K ⊆ lab u := by
      rw [Filter.eventually_all_finset]
      intro u _
      by_cases hKu : K ⊆ lab u
      · exact Eventually.of_forall fun _ _ => hKu
      · obtain ⟨p, hpK, hpu⟩ := not_subset.1 hKu
        have hpw : p ∈ range w := hw.symm ▸ hpK
        filter_upwards [eventually_subset_inputs w (finite_singleton p)
          (singleton_subset_iff.2 hpw)] with t ht hsub
        exact absurd (hsub (ht rfl)) hpu
    filter_upwards [this] with t ht u hu
    exact ht u (Finset.mem_range.2 hu)
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 hev
  refine ⟨T, fun t ht => ?_⟩
  obtain ⟨hzt, hPS, hearly⟩ := hT t ht
  set S : Set (Pt d) := {x | x ∈ inputsUpTo w t} with hS
  have hSK : S ⊆ K := fun x hx => by
    obtain ⟨i, -, rfl⟩ := mem_inputs.1 hx
    have h := mem_range_self (f := w) i
    rw [hw] at h
    exact h
  have hcritz : Critical N lab S z := ⟨hz, hSK, fun u hu hcu => hearly u hu hcu⟩
  have hex : ∃ i ≤ t, Critical N lab S i := ⟨z, hzt, hcritz⟩
  set Q := Nat.findGreatest (fun i => Critical N lab S i) t with hQ
  have hguess : guess N lab w t = some Q := by
    simp only [guess]
    rw [dif_pos hex]
  have hQcrit : Critical N lab S Q := Nat.findGreatest_spec hzt hcritz
  have hzQ : z ≤ Q := Nat.le_findGreatest hzt hcritz
  have hQK : lab Q ⊆ K := by
    rcases eq_or_lt_of_le hzQ with h | h
    · rw [← h]
    · exact hQcrit.2.2 z h hSK
  -- every vertex `v ≥ z` with `S ⊆ lab v ⊆ K` is a descendant of `z`
  have hdesc : ∀ v, z ≤ v → (v : ℕ∞) < N → S ⊆ lab v → lab v ⊆ K →
      IsAncestor (scanParent strict lab P) z v := by
    intro v
    induction v using Nat.strong_induction_on with
    | _ v ih =>
      intro hzv hvN hSv hvK
      rcases eq_or_lt_of_le hzv with rfl | hlt
      · exact IsAncestor.refl _
      · have hpz : PossibleParent strict lab P z v := by
          refine ⟨hlt, ?_, hPS.trans hSv⟩
          cases hs : strict
          · simpa using hvK
          · simp only [if_true]
            refine ⟨hvK, fun hzsub => ?_⟩
            have := hinj hs v z hvN hz (subset_antisymm hvK hzsub)
            omega
        have hbefore : ∀ i < z, PossibleParent strict lab P i v → lab z ⊆ lab i := by
          intro i hi hpp
          exact hearly i hi (hSv.trans (sub_of_test hpp.2.1))
        obtain ⟨p, hp, hzp, hpv, hvp, hpK⟩ := scan_retains hlt hpz hbefore
        have hpN : (p : ℕ∞) < N := lt_trans (by exact_mod_cast hpv) hvN
        exact IsAncestor.step (ih p hpv hzp hpN (hSv.trans hvp) hpK) hp
  exact ⟨Q, hguess, hdesc Q hzQ hQcrit.1 hQcrit.2.1 hQK⟩

end ForestAux

/-- **Lemma 8.10** (`lem:hd-capture`), for the fixed-quota forest: the vertices `i < N` (`N` finite
for a finite family, `N = ⊤` otherwise) enumerate the distinct languages of `X` (`L_1, L_2, …` in
the paper; injective on the vertices, image `X`); every vertex carries a finite `P_i ⊆ L_i`, and
the forest is given by the strict parent scan. On every full enumeration of `K = L_z`, all
sufficiently late guesses `Q_t` are defined and lie in the subtree rooted at `z` (`z` included).
The cutoffs, radii and games play no role, as the manuscript says. -/
theorem lem_hd_capture {d : ℕ} {X : Set (Set (Pt d))} (hX : LangClass X) (N : ℕ∞)
    (lab : ℕ → Set (Pt d))
    (hinj : ∀ i j : ℕ, (i : ℕ∞) < N → (j : ℕ∞) < N → lab i = lab j → i = j)
    (hrange : {L | ∃ i : ℕ, (i : ℕ∞) < N ∧ lab i = L} = X) (P : ℕ → Set (Pt d))
    (hP : ∀ i, (P i).Finite ∧ P i ⊆ lab i) (z : ℕ) (hz : (z : ℕ∞) < N) (w : ℕ → Pt d)
    (hw : IsFullEnumeration w (lab z)) :
    ∃ T, ∀ t ≥ T, ∃ v, guess N lab w t = some v ∧ IsAncestor (scanParent true lab P) z v := by
  exact ForestAux.capture_gen true N lab P (fun _ => hinj) z hz (hP z) w hw

/-- The capture lemma for accuracy copies (used by Theorem 8.2, §8.5: "the capture … proofs apply
to each fixed copy"): the vertices enumerate the copies `(L, k)` (`L ∈ X`, `k ≥ 1`) bijectively,
the copies of each language in increasing accuracy order; the parent scan is nonstrict. For a
fixed copy `z` and every full enumeration of its language, all sufficiently late guesses lie in
the subtree rooted at `z`. -/
theorem lem_hd_capture_copy {d : ℕ} {X : Set (Set (Pt d))} (hX : LangClass X)
    (lab : ℕ → Set (Pt d)) (acc : ℕ → ℕ) (hlab : ∀ i, lab i ∈ X) (hacc : ∀ i, 1 ≤ acc i)
    (hsurj : ∀ L ∈ X, ∀ k, 1 ≤ k → ∃ i, lab i = L ∧ acc i = k)
    (hinj : ∀ i j, lab i = lab j → acc i = acc j → i = j)
    (horder : ∀ i j, lab i = lab j → acc i < acc j → i < j) (P : ℕ → Set (Pt d))
    (hP : ∀ i, (P i).Finite ∧ P i ⊆ lab i) (z : ℕ) (w : ℕ → Pt d)
    (hw : IsFullEnumeration w (lab z)) :
    ∃ T, ∀ t ≥ T, ∃ v, guess ⊤ lab w t = some v ∧ IsAncestor (scanParent false lab P) z v := by
  exact ForestAux.capture_gen false ⊤ lab P (fun h => absurd h Bool.false_ne_true) z
    (ENat.natCast_lt_top z) (hP z) w hw

/-! ### Simulating the finite stopping game on a board (§8.3.4) -/

/-- One actual round of the board simulation (§8.3.4, items 2–3): first enlarge visibility, one
level at a time and with no White reply, down to the pullback level `ℓ` (an LCA update never goes
deeper); then, if the actual input `x` is a free visible point, it is Black's next claim and the
stored strategy `σ` replies. Returns the new move list, the new state, and the reply. -/
noncomputable def simStep {d : ℕ} (S : StopGame d) (σ : WStrategy d) (ms : List (BMove d))
    (st : S.State) (ℓ : ℕ) (x : Pt d) : List (BMove d) × S.State × Option (Pt d) :=
  let lv : ℕ := min ℓ st.level.val
  let ms₁ := ms ++ List.replicate (st.level.val - lv) BMove.down
  let st₁ : S.State := ⟨⟨lv, by have := st.level.isLt; omega⟩, st.black, st.white⟩
  if S.Free st₁ x then
    let rep := σ (ms₁ ++ [BMove.claim x])
    (ms₁ ++ [BMove.claim x], S.afterClaim st₁ x rep, rep)
  else (ms₁, st₁, none)

/-- The simulation on a board initialized at round `t₀`, driven by the actual inputs `x` and the
pullback levels `lev` (level `r` of the packet is the board's initial pullback `v`):
`simRun … k` is the state after the actual rounds `t₀, …, t₀ + k - 1`. -/
noncomputable def simRun {d : ℕ} (S : StopGame d) (σ : WStrategy d) (x : ℕ → Pt d)
    (lev : ℕ → ℕ) (t₀ : ℕ) : ℕ → List (BMove d) × S.State × Option (Pt d)
  | 0 => ([], S.init, none)
  | k + 1 =>
      let p := simRun S σ x lev t₀ k
      simStep S σ p.1 p.2.1 (lev (t₀ + k)) (x (t₀ + k))

namespace ForestAux

variable {d : ℕ}

/-- Moving `n` levels down from a reached state (no White reply) gives a reached state with the
same points. -/
theorem reach_downs {S : StopGame d} {σ : WStrategy d} {ms : List (BMove d)}
    {lvl : Fin (S.r + 1)} {b w : Set (Pt d)} (h : S.Reach σ ms ⟨lvl, b, w⟩) :
    ∀ n m (hm : m + n = lvl.val),
      S.Reach σ (ms ++ List.replicate n BMove.down) ⟨⟨m, by have := lvl.isLt; omega⟩, b, w⟩ := by
  exact StopGame.Reach.downs h

/-- At a reached state of a winning strategy, the requirement of every level `i` at or below the
current level holds as soon as everything visible at level `i` is claimed (Black may move down to
level `i` and stop there). -/
theorem level_req {S : StopGame d} {σ : WStrategy d} (hσ : S.Wins σ) {ms : List (BMove d)}
    {lvl : Fin (S.r + 1)} {b w : Set (Pt d)} (h : S.Reach σ ms ⟨lvl, b, w⟩)
    (i : Fin (S.r + 1)) (hi : i ≤ lvl) (hvis : S.visible i ⊆ b ∪ w) :
    ∀ R ∈ S.rects i, S.quota i * ((S.L i ∩ R.pts).ncard : ℝ) ≤ ((w ∩ S.L i ∩ R.pts).ncard : ℝ) := by
  have hR := reach_downs h (lvl.val - i.val) i.val (by rw [Fin.le_def] at hi; omega)
  exact (hσ _ _ hR).2 hvis

/-- The invariant of the board simulation (Lemma 8.12): the simulated play is legal, every
support point input since `t₀` is claimed, and every simulated White point is an actual output. -/
theorem help_inv {r : ℕ} (Ls : Fin (r + 1) → Set (Pt d)) (qs : Fin (r + 1) → ℝ)
    (rects : Fin (r + 1) → Finset (Rect d)) (hanti : Antitone Ls) (σ : WStrategy d)
    (hσ : (packetGame Ls qs rects).Wins σ) (x y : ℕ → Pt d) (lev : ℕ → ℕ) (t₀ : ℕ)
    (hpre : ∀ t < t₀, x t ∉ packetSupport Ls rects)
    (hvis : ∀ t ≥ t₀, x t ∈ packetSupport Ls rects → x t ∈ Ls ⟨min (lev t) r, by omega⟩)
    (hout : ∀ k y', (simRun (packetGame Ls qs rects) σ x lev t₀ (k + 1)).2.2 = some y' →
      (∀ i ≤ t₀ + k, x i ≠ y') → (∀ i < t₀ + k, y i ≠ y') → y (t₀ + k) = y') (k : ℕ) :
    (packetGame Ls qs rects).Reach σ (simRun (packetGame Ls qs rects) σ x lev t₀ k).1
        (simRun (packetGame Ls qs rects) σ x lev t₀ k).2.1 ∧
    (∀ t, t₀ ≤ t → t < t₀ + k → x t ∈ packetSupport Ls rects →
        x t ∈ (simRun (packetGame Ls qs rects) σ x lev t₀ k).2.1.black ∪
          (simRun (packetGame Ls qs rects) σ x lev t₀ k).2.1.white) ∧
    (∀ q ∈ (simRun (packetGame Ls qs rects) σ x lev t₀ k).2.1.white,
        ∃ t < t₀ + k, y t = q) := by
  set S := packetGame Ls qs rects with hS
  induction k with
  | zero =>
    refine ⟨StopGame.Reach.nil, fun t h1 h2 => by omega, fun q hq => ?_⟩
    exact absurd hq (by simp [simRun, StopGame.init, StopGame.State.white])
  | succ k ih =>
    obtain ⟨hR, hB, hW⟩ := ih
    rcases hp : simRun S σ x lev t₀ k with ⟨ms, ⟨lvl, b, w⟩, o⟩
    rw [hp] at hR hB hW
    have hsucc : simRun S σ x lev t₀ (k + 1) =
        simStep S σ ms ⟨lvl, b, w⟩ (lev (t₀ + k)) (x (t₀ + k)) := by
      show simStep S σ (simRun S σ x lev t₀ k).1 (simRun S σ x lev t₀ k).2.1 _ _ = _
      rw [hp]
    have hdown := reach_downs hR (lvl.val - min (lev (t₀ + k)) lvl.val)
      (min (lev (t₀ + k)) lvl.val) (by omega)
    have hlvl : lvl.val ≤ r := Nat.lt_succ_iff.1 lvl.isLt
    -- the current input is visible at the enlarged level when it lies in the support
    have hzvis : x (t₀ + k) ∈ packetSupport Ls rects →
        x (t₀ + k) ∈ S.visible ⟨min (lev (t₀ + k)) lvl.val, by omega⟩ := by
      intro hz
      exact ⟨hz, hanti (show (⟨min (lev (t₀ + k)) lvl.val, by omega⟩ : Fin (r + 1)) ≤
        ⟨min (lev (t₀ + k)) r, by omega⟩ from Fin.mk_le_mk.2 (by omega))
        (hvis (t₀ + k) (by omega) hz)⟩
    by_cases hfree : S.Free ⟨⟨min (lev (t₀ + k)) lvl.val, by omega⟩, b, w⟩ (x (t₀ + k))
    · have hst : simStep S σ ms ⟨lvl, b, w⟩ (lev (t₀ + k)) (x (t₀ + k)) =
          (ms ++ List.replicate (lvl.val - min (lev (t₀ + k)) lvl.val) BMove.down ++
              [BMove.claim (x (t₀ + k))],
            S.afterClaim ⟨⟨min (lev (t₀ + k)) lvl.val, by omega⟩, b, w⟩ (x (t₀ + k))
              (σ (ms ++ List.replicate (lvl.val - min (lev (t₀ + k)) lvl.val) BMove.down ++
                [BMove.claim (x (t₀ + k))])),
            σ (ms ++ List.replicate (lvl.val - min (lev (t₀ + k)) lvl.val) BMove.down ++
                [BMove.claim (x (t₀ + k))])) := by
        dsimp only [simStep, StopGame.State.level, StopGame.State.black, StopGame.State.white]
        exact if_pos hfree
      have hleg := (hσ _ _ hdown).1 (x (t₀ + k)) hfree
      have hreach := StopGame.Reach.claim hdown hfree hleg
      have hout' := hout k
      rw [hsucc, hst] at hout' ⊢
      refine ⟨hreach, ?_, ?_⟩
      · intro t h1 h2 hxt
        rcases Nat.lt_succ_iff_lt_or_eq.1 (show t < t₀ + k + 1 by omega) with h3 | h3
        · rcases hB t h1 h3 hxt with h4 | h4
          · exact Or.inl (Set.mem_insert_of_mem _ h4)
          · right
            show x t ∈ (σ _).elim w fun y => insert y w
            rcases σ (ms ++ List.replicate (lvl.val - min (lev (t₀ + k)) lvl.val) BMove.down ++
                [BMove.claim (x (t₀ + k))]) with _ | y'
            · exact h4
            · exact Set.mem_insert_of_mem _ h4
        · subst h3
          exact Or.inl (Set.mem_insert _ _)
      · intro q hq
        change q ∈ (σ _).elim w (fun y => insert y w) at hq
        rcases hrep : σ (ms ++ List.replicate (lvl.val - min (lev (t₀ + k)) lvl.val) BMove.down ++
            [BMove.claim (x (t₀ + k))]) with _ | y'
        · rw [hrep] at hq
          obtain ⟨t, ht, hyt⟩ := hW q hq
          exact ⟨t, by omega, hyt⟩
        · rw [hrep] at hq hleg hout'
          have hyfree : S.Free ⟨⟨min (lev (t₀ + k)) lvl.val, by omega⟩, insert (x (t₀ + k)) b, w⟩
              y' := hleg
          rcases Set.mem_insert_iff.1 hq with rfl | hq
          · by_cases hy : ∃ i < t₀ + k, y i = q
            · obtain ⟨i, hi, hyi⟩ := hy
              exact ⟨i, by omega, hyi⟩
            · refine ⟨t₀ + k, by omega, hout' q rfl ?_ fun i hi hyi => hy ⟨i, hi, hyi⟩⟩
              intro i hi hxi
              have hqU : q ∈ packetSupport Ls rects := hyfree.1.1
              have hti : t₀ ≤ i := by
                by_contra hlt
                exact hpre i (by omega) (hxi ▸ hqU)
              rcases Nat.lt_or_ge i (t₀ + k) with hik | hik
              · rcases hB i hti hik (hxi ▸ hqU) with h4 | h4
                · exact hyfree.2.1 (Set.mem_insert_of_mem _ (hxi ▸ h4))
                · exact hyfree.2.2 (hxi ▸ h4)
              · have : i = t₀ + k := by omega
                subst this
                exact hyfree.2.1 (hxi ▸ Set.mem_insert _ _)
          · obtain ⟨t, ht, hyt⟩ := hW q hq
            exact ⟨t, by omega, hyt⟩
    · have hst : simStep S σ ms ⟨lvl, b, w⟩ (lev (t₀ + k)) (x (t₀ + k)) =
          (ms ++ List.replicate (lvl.val - min (lev (t₀ + k)) lvl.val) BMove.down,
            ⟨⟨min (lev (t₀ + k)) lvl.val, by omega⟩, b, w⟩, none) := by
        dsimp only [simStep, StopGame.State.level, StopGame.State.black, StopGame.State.white]
        exact if_neg hfree
      rw [hsucc, hst]
      refine ⟨hdown, ?_, fun q hq => ?_⟩
      · intro t h1 h2 hxt
        rcases Nat.lt_succ_iff_lt_or_eq.1 (show t < t₀ + k + 1 by omega) with h3 | h3
        · exact hB t h1 h3 hxt
        · subst h3
          by_contra hn
          simp only [Set.mem_union, not_or] at hn
          exact hfree ⟨hzvis hxt, hn.1, hn.2⟩
      · obtain ⟨t, ht, hyt⟩ := hW q hq
        exact ⟨t, by omega, hyt⟩

end ForestAux

/-- **Lemma 8.12** (`lem:hd-help`). Consider the packet game `S = packetGame Ls qs rects` of a
board on a nonincreasing chain of languages `L₀ ⊇ L₁ ⊇ ⋯ ⊇ L_r` (`Antitone Ls`; repeated languages
allowed, as along accuracy-copy paths; the general stopping game allows more sequences,
while this lemma is restricted to chains), with a winning White strategy `σ`
(feasibility), simulated from round `t₀` on, where:
* no actual input before round `t₀` lies in the packet's support (the board is initialized by its
  first input; earlier outputs there are allowed),
* the pullback levels never increase and start at the top level `r`,
* every actual input that lies in the support is visible at the current pullback level after the
  enlargement (item 3a: the pullback is an ancestor of the current guess),
* whenever the strategy replies `y'` and `y'` is globally fresh, the actual output is `y'` (item 4),
* the actual outputs are globally fresh.
Then, after each round: (1) every support point that has appeared as an actual input is claimed in
the simulated game; (2) every simulated White point is an actual output so far. Consequently, at a
level `i ≤` the current pullback level (an ancestor), if every visible point at level `i` appeared as an
actual input, every requested rectangle `R` of level `i` satisfies `q_i |L_i ∩ R| ≤ |O ∩ L_i ∩ R|`. -/
theorem lem_hd_help {d r : ℕ} (Ls : Fin (r + 1) → Set (Pt d)) (qs : Fin (r + 1) → ℝ)
    (rects : Fin (r + 1) → Finset (Rect d)) (hanti : Antitone Ls) (σ : WStrategy d)
    (hσ : (packetGame Ls qs rects).Wins σ) (x y : ℕ → Pt d) (lev : ℕ → ℕ) (t₀ : ℕ)
    (hpre : ∀ t < t₀, x t ∉ packetSupport Ls rects)
    (hlev0 : lev t₀ = r) (hlev : ∀ t ≥ t₀, lev (t + 1) ≤ lev t)
    (hvis : ∀ t ≥ t₀, x t ∈ packetSupport Ls rects → x t ∈ Ls ⟨min (lev t) r, by omega⟩)
    (hout : ∀ k y', (simRun (packetGame Ls qs rects) σ x lev t₀ (k + 1)).2.2 = some y' →
      (∀ i ≤ t₀ + k, x i ≠ y') → (∀ i < t₀ + k, y i ≠ y') → y (t₀ + k) = y')
    (hfresh : ∀ t, (∀ i ≤ t, x i ≠ y t) ∧ ∀ i < t, y i ≠ y t) (k : ℕ) :
    let st := (simRun (packetGame Ls qs rects) σ x lev t₀ k).2.1
    (∀ p ∈ packetSupport Ls rects, (∃ t, t₀ ≤ t ∧ t < t₀ + k ∧ x t = p) →
        p ∈ st.black ∪ st.white) ∧
    (∀ p ∈ st.white, ∃ t < t₀ + k, y t = p) ∧
    (∀ i : Fin (r + 1), i ≤ st.level →
      (∀ p ∈ packetSupport Ls rects ∩ Ls i, ∃ t, t₀ ≤ t ∧ t < t₀ + k ∧ x t = p) →
      ∀ R ∈ rects i, qs i * ((Ls i ∩ R.pts).ncard : ℝ) ≤
        (({p | ∃ t < t₀ + k, y t = p} ∩ Ls i ∩ R.pts).ncard : ℝ)) := by
  intro st
  obtain ⟨hR, hB, hW⟩ := ForestAux.help_inv Ls qs rects hanti σ hσ x y lev t₀ hpre hvis hout k
  have hstd : st = (simRun (packetGame Ls qs rects) σ x lev t₀ k).2.1 := rfl
  clear_value st
  subst hstd
  refine ⟨fun p hp hex => by obtain ⟨t, h1, h2, hx⟩ := hex; subst hx; exact hB t h1 h2 hp, hW, ?_⟩
  intro i hi hall R hR'
  have hfin : ({p | ∃ t < t₀ + k, y t = p} ∩ Ls i ∩ R.pts).Finite :=
    have h1 : {p | ∃ t < t₀ + k, y t = p}.Finite :=
      ((Set.finite_lt_nat (t₀ + k)).image y).subset (by
        rintro p ⟨t, ht, hp⟩; exact ⟨t, ht, hp⟩)
    (h1.inter_of_left _).inter_of_left _
  rcases hst : (simRun (packetGame Ls qs rects) σ x lev t₀ k).2.1 with ⟨lvl, b, w⟩
  rw [hst] at hR hB hW hi
  have hvisi : (packetGame Ls qs rects).visible i ⊆ b ∪ w := fun p hp => by
    obtain ⟨t, h1, h2, hx⟩ := hall p hp
    subst hx
    exact hB t h1 h2 hp.1
  refine (ForestAux.level_req hσ hR i hi hvisi R hR').trans ?_
  exact_mod_cast Set.ncard_le_ncard (Set.inter_subset_inter_left _
    (Set.inter_subset_inter_left _ hW)) hfin


end BanachDensityHD
