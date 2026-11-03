import BanachDensityHD.Histories

/-!
# The finite stopping game

Kleinberg–Wei, *Characterizing Local Breadth in Language Generation*.
Historical source numbering is retained; current mappings are in the release registry.

-/

namespace BanachDensityHD

open Set Filter
open scoped Classical

/-! ## The finite stopping game (§8.2, Definition 8.4) -/

/-- Black's moves: claim a point, or move one level down (enlarging visibility). -/
inductive BMove (d : ℕ)
  | claim (x : Pt d)
  | down

/-- A White strategy: from the sequence of Black's moves so far, an optional reply. -/
abbrev WStrategy (d : ℕ) := List (BMove d) → Option (Pt d)

/-- A stopping game: levels `0, …, r`, with a language `Lᵢ`, a visible set, a quota and a finite
family of rectangles at every level. The chain is intended to be nonincreasing,
`L 0 ⊇ L 1 ⊇ ⋯ ⊇ L r` (consecutive equal languages allowed: this covers accuracy copies), but the
type does not enforce it: every paper-facing result that uses the game restricts it to such chains
(for `lem_hd_help`, Lemma 8.12, by its hypothesis `Antitone Ls`). The visible
sets `vis` are free data; `packetGame` sets `vis i = U ∩ Lᵢ`, and `claimGame` sets them to the
board. -/
inductive StopGame (d : ℕ)
  | mk (r : ℕ) (L : Fin (r + 1) → Set (Pt d)) (vis : Fin (r + 1) → Set (Pt d))
      (quota : Fin (r + 1) → ℝ) (rects : Fin (r + 1) → Finset (Rect d))

/-- The top level `r` (levels are `0, …, r`). -/
def StopGame.r {d : ℕ} : StopGame d → ℕ
  | .mk r _ _ _ _ => r

/-- The language `Lᵢ` of level `i`. -/
def StopGame.L {d : ℕ} : (S : StopGame d) → Fin (S.r + 1) → Set (Pt d)
  | .mk _ L _ _ _ => L

/-- The visible set of level `i`. It is intended to be nondecreasing as the level goes down (as
for `packetGame` on a nonincreasing chain); the type does not enforce this, and a result that needs
it assumes it explicitly (e.g. `StopGame.greedy_stop_bound`, hypothesis `hmono`). -/
def StopGame.vis {d : ℕ} : (S : StopGame d) → Fin (S.r + 1) → Set (Pt d)
  | .mk _ _ vis _ _ => vis

/-- The quota `qᵢ` of level `i`. -/
def StopGame.quota {d : ℕ} : (S : StopGame d) → Fin (S.r + 1) → ℝ
  | .mk _ _ _ quota _ => quota

/-- The requested rectangles `𝓡ᵢ` of level `i`. -/
def StopGame.rects {d : ℕ} : (S : StopGame d) → Fin (S.r + 1) → Finset (Rect d)
  | .mk _ _ _ _ rects => rects

/-- The finite support `U = ⋃ᵢ ⋃_{R ∈ 𝓡ᵢ} (Lᵢ ∩ R)` of a rectangle packet. -/
def packetSupport {d r : ℕ} (L : Fin (r + 1) → Set (Pt d)) (rects : Fin (r + 1) → Finset (Rect d)) :
    Set (Pt d) :=
  ⋃ i, ⋃ R ∈ rects i, L i ∩ R.pts

/-- The finite stopping game of §8.2 for a packet: the visible set at level `i` is `U ∩ Lᵢ`. -/
def packetGame {d r : ℕ} (L : Fin (r + 1) → Set (Pt d)) (quota : Fin (r + 1) → ℝ)
    (rects : Fin (r + 1) → Finset (Rect d)) : StopGame d :=
  ⟨r, L, fun i => packetSupport L rects ∩ L i, quota, rects⟩

namespace StopGame
variable {d : ℕ} (S : StopGame d)

/-- The visible set at level `i`. -/
def visible (i : Fin (S.r + 1)) : Set (Pt d) := S.vis i

/-- A game state: current level, Black's points, White's points. -/
inductive State
  | mk (level : Fin (S.r + 1)) (black white : Set (Pt d))

/-- The current level of a state. -/
def State.level {S : StopGame d} : S.State → Fin (S.r + 1)
  | .mk level _ _ => level

/-- Black's points in a state. -/
def State.black {S : StopGame d} : S.State → Set (Pt d)
  | .mk _ black _ => black

/-- White's points in a state. -/
def State.white {S : StopGame d} : S.State → Set (Pt d)
  | .mk _ _ white => white

/-- The initial state: level `r`, nothing claimed. -/
def init : S.State := ⟨Fin.last S.r, ∅, ∅⟩

/-- `p` is unused and visible at `st`. -/
def Free (st : S.State) (p : Pt d) : Prop :=
  p ∈ S.visible st.level ∧ p ∉ st.black ∧ p ∉ st.white

/-- White's reply is legal: a pass, or one free point. -/
def LegalReply (st : S.State) : Option (Pt d) → Prop
  | none => True
  | some y => S.Free st y

/-- The state after Black claims `x` and White replies `rep`. -/
def afterClaim (st : S.State) (x : Pt d) (rep : Option (Pt d)) : S.State :=
  ⟨st.level, insert x st.black, rep.elim st.white fun y => insert y st.white⟩

end StopGame

/-- The plays consistent with `σ` on which all of `σ`'s replies were legal: `Reach S σ ms st`
says that Black's move sequence `ms` is legal and leads to the state `st`. -/
inductive StopGame.Reach {d : ℕ} (S : StopGame d) (σ : WStrategy d) :
    List (BMove d) → S.State → Prop
  | nil : StopGame.Reach S σ [] S.init
  | claim {ms : List (BMove d)} {st : S.State} {x : Pt d} :
      StopGame.Reach S σ ms st → S.Free st x →
      S.LegalReply ⟨st.level, insert x st.black, st.white⟩ (σ (ms ++ [BMove.claim x])) →
      StopGame.Reach S σ (ms ++ [BMove.claim x]) (S.afterClaim st x (σ (ms ++ [BMove.claim x])))
  | down {ms : List (BMove d)} {st : S.State} (i : Fin (S.r + 1)) :
      StopGame.Reach S σ ms st → i.val + 1 = st.level.val →
      StopGame.Reach S σ (ms ++ [BMove.down]) ⟨i, st.black, st.white⟩

namespace StopGame
variable {d : ℕ} (S : StopGame d)

/-- `σ` is winning: every reply on a legal play is legal, and at every legal stop (all points
visible at the current level claimed) every rectangle requirement of that level holds:
`|W ∩ Lᵢ ∩ R| ≥ q_i |Lᵢ ∩ R|` for every `R ∈ 𝓡ᵢ`. -/
def Wins (σ : WStrategy d) : Prop :=
  ∀ ms st, S.Reach σ ms st →
    (∀ x, S.Free st x →
        S.LegalReply ⟨st.level, insert x st.black, st.white⟩ (σ (ms ++ [.claim x]))) ∧
    (S.visible st.level ⊆ st.black ∪ st.white →
        ∀ R ∈ S.rects st.level,
          S.quota st.level * ((S.L st.level ∩ R.pts).ncard : ℝ) ≤
            ((st.white ∩ S.L st.level ∩ R.pts).ncard : ℝ))

/-- The packet is **feasible**: White has one strategy winning at every possible stop. -/
def Feasible : Prop := ∃ σ : WStrategy d, S.Wins σ

end StopGame

/-- **Definition 8.4** (unlabelled): the chain `Ls` (with quotas `qs`) is geometrically feasible
at cutoffs `ss` outside `Q_a`: every packet whose level-`i` rectangles miss `Q_a` and satisfy
`m_{Lᵢ}(R) ≥ sᵢ h(V(R))` is feasible. -/
def GeomFeasible {d : ℕ} (h : ℕ → ℝ) {r : ℕ} (Ls : Fin (r + 1) → Set (Pt d))
    (qs ss : Fin (r + 1) → ℝ) (a : ℝ) : Prop :=
  ∀ rects : Fin (r + 1) → Finset (Rect d),
    (∀ i, ∀ R ∈ rects i, Disjoint R.pts (core d a) ∧ ss i * h R.vol ≤ mass (Ls i) R) →
    (packetGame Ls qs rects).Feasible


/-- The single-board claim game of **Lemma 9.1**: one level, the whole of `E` visible; Black
claims an unused point of `E`, White then claims at most one unused point of `E`; the only stop
is the exhaustion of `E`, where every rectangle of `Rs` must satisfy `|W ∩ R| ≥ quota·|E ∩ R|`. -/
def claimGame {d : ℕ} (E : Finset (Pt d)) (Rs : Finset (Rect d)) (quota : ℝ) : StopGame d :=
  ⟨0, fun _ => ↑E, fun _ => ↑E, fun _ => quota, fun _ => Rs⟩


namespace GameAux

/-- The potential `Φ = (visible white) + ⌊(visible unused)/2⌋` of the pairing game, for white
points `W`, black points `Bl` and visible set `V`. -/
def potential {α : Type*} [DecidableEq α] (W Bl V : Finset α) : ℕ := (W ∩ V).card + (V \ (W ∪ Bl)).card / 2

/-- A turn of the pairing game does not decrease the potential. -/
lemma potential_turn {α : Type*} [DecidableEq α] {W W' Bl Bl' V : Finset α} {a : α} (hWW : W ⊆ W')
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
lemma potential_reveal {α : Type*} [DecidableEq α] {W Bl V V' : Finset α} (hVV : V ⊆ V') (hBl : Bl ⊆ V) :
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
lemma potential_reveal_many {α : Type*} [DecidableEq α] (Y : ℕ → Finset α) (hY : Monotone Y) (W Bl : Finset α) (s : ℕ)
    (hBl : Bl ⊆ Y s) : ∀ s', s ≤ s' →
    potential W Bl (Y s) + ∑ i ∈ Finset.Ico s s', (Y (i + 1) \ Y i).card / 2 ≤ potential W Bl (Y s') := by
  intro s' hss'
  induction s', hss' using Nat.le_induction with
  | base => simp
  | succ s' hss' ih =>
    rw [Finset.sum_Ico_succ_top hss']
    have := potential_reveal (W := W) (hY (show s' ≤ s' + 1 by omega)) (hBl.trans (hY hss'))
    omega

end GameAux

/-- **Lemma 6.18** (`lem:pairing-game`), ported from `BanachDensity1D.lem_pairing_game`
(`Finset ℤ` ↦ `Finset α`, statement otherwise verbatim): when a finite board is revealed through
the filtration `Y` and the algorithm answers each adversary selection with an unused visible point
whenever one remains, it ends with at least `∑ ⌊|Yᵢ₊₁ \ Yᵢ|/2⌋` points. -/
theorem lem_pairing_game {α : Type*} [DecidableEq α] (Bd : Finset α) (m : ℕ) (Y : ℕ → Finset α)
    (hY0 : Y 0 = ∅) (hYmono : Monotone Y) (hYm : Y m = Bd) (T : ℕ) (stage : ℕ → ℕ)
    (hst : Monotone stage) (hstm : ∀ j, stage j ≤ m) (a : ℕ → α) (ha : ∀ j < T, a j ∈ Y (stage j))
    (W Bl : ℕ → Finset α) (hBl0 : Bl 0 = ∅) (hW0 : W 0 ⊆ Bd)
    (hBl : ∀ j < T, Bl (j + 1) = if a j ∈ W j then Bl j else insert (a j) (Bl j))
    (hWmono : ∀ j < T, W j ⊆ W (j + 1)) (hWsub : ∀ j < T, W (j + 1) ⊆ Bd)
    (hWdisj : ∀ j < T, Disjoint (W (j + 1)) (Bl (j + 1)))
    (hresp : ∀ j < T, (∃ x ∈ Y (stage j), x ∉ W j ∧ x ∉ Bl (j + 1)) →
      ∃ x ∈ Y (stage j), x ∉ W j ∧ x ∉ Bl (j + 1) ∧ x ∈ W (j + 1))
    (hcomplete : ∀ x ∈ Bd, ∃ j < T, a j = x) :
    ∑ i ∈ Finset.range m, (Y (i + 1) \ Y i).card / 2 ≤ (W T).card := by
  open GameAux Finset in
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

namespace StopGame
variable {d : ℕ} (S : StopGame d)

/-- `σ` follows the greedy rule ("claim any unused visible point"): on every legal play, whenever
Black's claim leaves some free visible point, `σ` claims one (which one is up to `σ`). -/
def IsGreedy (σ : WStrategy d) : Prop :=
  ∀ (ms : List (BMove d)) (st : S.State) (x : Pt d), StopGame.Reach S σ ms st → S.Free st x →
    (∃ y, S.Free ⟨st.level, insert x st.black, st.white⟩ y) →
      ∃ y, σ (ms ++ [BMove.claim x]) = some y ∧ S.Free ⟨st.level, insert x st.black, st.white⟩ y

/-- One step of a particular greedy play: a Black claim is answered by some free visible point (a
fixed choice) if one exists, otherwise by a pass; a visibility enlargement gets no reply. -/
noncomputable def greedyStep (st : S.State) : BMove d → S.State × Option (Pt d)
  | .claim x =>
      let st₁ : S.State := ⟨st.level, insert x st.black, st.white⟩
      let rep : Option (Pt d) := if hy : ∃ y, S.Free st₁ y then some (Classical.choose hy) else none
      (S.afterClaim st x rep, rep)
  | .down =>
      (if h : 0 < st.level.val then ⟨⟨st.level.val - 1, by omega⟩, st.black, st.white⟩ else st, none)

/-- Replaying Black's moves against that greedy rule. -/
noncomputable def greedyRun (ms : List (BMove d)) : S.State × Option (Pt d) :=
  ms.foldl (fun acc m => S.greedyStep acc.1 m) (S.init, none)

/-- One particular greedy White strategy (a fixed choice among the free visible points). -/
noncomputable def greedy : WStrategy d := fun ms => (S.greedyRun ms).2

/-- Replaying one more move. -/
theorem _root_.BanachDensityHD.GameAux.greedyRun_append (ms : List (BMove d)) (m : BMove d) :
    S.greedyRun (ms ++ [m]) = S.greedyStep (S.greedyRun ms).1 m := by
  simp [greedyRun, List.foldl_append]

/-- On a legal play against `greedy`, the replayed state is the reached state. 
-/
theorem _root_.BanachDensityHD.GameAux.greedyRun_of_reach {ms : List (BMove d)} {st : S.State}
    (h : StopGame.Reach S S.greedy ms st) : (S.greedyRun ms).1 = st := by
  induction h with
  | nil => rfl
  | @claim ms st x h hfree hleg ih =>
    rw [GameAux.greedyRun_append, ih]
    simp only [greedyStep]
    congr 1
    show _ = (S.greedyRun (ms ++ [BMove.claim x])).2
    rw [GameAux.greedyRun_append, ih]
    rfl
  | @down ms st i h hi ih =>
    rw [GameAux.greedyRun_append, ih]
    have hpos : 0 < st.level.val := by omega
    simp only [greedyStep, dif_pos hpos]
    congr 1
    ext
    simp only
    omega

/-- The particular strategy `greedy` follows the greedy rule (so `IsGreedy` is satisfiable). -/
theorem greedy_isGreedy : S.IsGreedy S.greedy := by
  intro ms st x hreach _ hex
  have hrun := GameAux.greedyRun_of_reach S hreach
  refine ⟨Classical.choose hex, ?_, Classical.choose_spec hex⟩
  show (S.greedyRun (ms ++ [BMove.claim x])).2 = _
  rw [GameAux.greedyRun_append, hrun]
  simp only [greedyStep]
  rw [dif_pos hex]

/-- The points that become visible at level `j` (the `j`-th layer of the filtration). -/
noncomputable def newAt (j : Fin (S.r + 1)) : Set (Pt d) :=
  if hj : j.val < S.r then S.vis j \ S.vis ⟨j.val + 1, by omega⟩ else S.vis j

/-- The potential invariant of a greedy play: Black's and White's points are visible, and the
layers revealed so far are paid for by `|W| + ⌊|unused visible| / 2⌋`. -/
def _root_.BanachDensityHD.GameAux.GInv (st : S.State) : Prop :=
  st.black ⊆ S.vis st.level ∧ st.white ⊆ S.vis st.level ∧
  ∑ j ∈ Finset.univ.filter (fun j : Fin (S.r + 1) => st.level ≤ j), (S.newAt j).ncard / 2 ≤
    st.white.ncard + (S.vis st.level \ (st.white ∪ st.black)).ncard / 2

/-- If visibility only grows as the level decreases (`hmono`) and the level-0 visible set is
finite (`hfin`), the potential invariant holds along every legal play of a strategy following the
greedy rule. Without `hmono` it can fail. -/
theorem _root_.BanachDensityHD.GameAux.greedy_inv
    (hmono : ∀ i j : Fin (S.r + 1), i ≤ j → S.vis j ⊆ S.vis i)
    (hfin : (S.vis 0).Finite) (σ : WStrategy d) (hσ : S.IsGreedy σ) {ms : List (BMove d)}
    {st : S.State} (hreach : StopGame.Reach S σ ms st) :
    st.black ⊆ S.vis st.level ∧ st.white ⊆ S.vis st.level ∧
    ∑ j ∈ Finset.univ.filter (fun j : Fin (S.r + 1) => st.level ≤ j), (S.newAt j).ncard / 2 ≤
      st.white.ncard + (S.vis st.level \ (st.white ∪ st.black)).ncard / 2 := by
  have hfin' : ∀ i, (S.vis i).Finite := fun i => hfin.subset (hmono 0 i (Fin.zero_le _))
  induction hreach with
  | nil =>
    refine ⟨empty_subset _, empty_subset _, ?_⟩
    have hfilt : Finset.univ.filter (fun j : Fin (S.r + 1) => S.init.level ≤ j) =
        {Fin.last S.r} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      show Fin.last S.r ≤ j ↔ _
      exact ⟨fun h => le_antisymm (Fin.le_last _) h, fun h => h ▸ le_rfl⟩
    rw [hfilt, Finset.sum_singleton]
    have hnew : S.newAt (Fin.last S.r) = S.vis (Fin.last S.r) := by
      unfold newAt; rw [dif_neg (by simp)]
    show _ ≤ (∅ : Set (Pt d)).ncard + (S.vis (Fin.last S.r) \ (∅ ∪ ∅)).ncard / 2
    rw [hnew]; simp
  | @claim ms st x h hfree hleg ih =>
    obtain ⟨hB, hW, hsum⟩ := ih
    have hxU : x ∈ S.vis st.level \ (st.white ∪ st.black) :=
      ⟨hfree.1, fun h => h.elim hfree.2.2 hfree.2.1⟩
    have hUfin : (S.vis st.level \ (st.white ∪ st.black)).Finite := (hfin' _).diff
    have hWfin : st.white.Finite := (hfin' _).subset hW
    by_cases hex : ∃ y, S.Free ⟨st.level, insert x st.black, st.white⟩ y
    · obtain ⟨y, hy, hyfree⟩ := hσ ms st x h hfree hex
      rw [hy]
      obtain ⟨hyV, hyB, hyW⟩ := hyfree
      change y ∈ S.vis st.level at hyV
      change y ∉ insert x st.black at hyB
      change y ∉ st.white at hyW
      refine ⟨insert_subset hfree.1 hB, insert_subset hyV hW, ?_⟩
      change _ ≤ (insert y st.white).ncard +
        (S.vis st.level \ (insert y st.white ∪ insert x st.black)).ncard / 2
      have hU : S.vis st.level \ (insert y st.white ∪ insert x st.black) =
          ((S.vis st.level \ (st.white ∪ st.black)) \ {x}) \ {y} := by
        ext p; simp only [mem_diff, mem_union, mem_insert_iff, mem_singleton_iff]; tauto
      have hyU : y ∈ (S.vis st.level \ (st.white ∪ st.black)) \ {x} :=
        ⟨⟨hyV, fun h => h.elim hyW fun h => hyB (Or.inr h)⟩, fun h => hyB (Or.inl h)⟩
      rw [hU, Set.ncard_sdiff_singleton_of_mem hyU,
        Set.ncard_sdiff_singleton_of_mem hxU, Set.ncard_insert_of_notMem hyW hWfin]
      have h2 : 2 ≤ (S.vis st.level \ (st.white ∪ st.black)).ncard := by
        have hsub : ({x, y} : Set (Pt d)) ⊆ S.vis st.level \ (st.white ∪ st.black) :=
          insert_subset hxU (singleton_subset_iff.2 hyU.1)
        have := Set.ncard_le_ncard hsub hUfin
        rw [Set.ncard_pair (fun h => hyB (Or.inl h.symm))] at this
        exact this
      exact le_trans hsum (by omega)
    · have hnone : σ (ms ++ [BMove.claim x]) = none := by
        cases hrep : σ (ms ++ [BMove.claim x]) with
        | none => rfl
        | some y => rw [hrep] at hleg; exact absurd ⟨y, hleg⟩ hex
      rw [hnone]
      refine ⟨insert_subset hfree.1 hB, hW, ?_⟩
      change _ ≤ st.white.ncard +
        (S.vis st.level \ (st.white ∪ insert x st.black)).ncard / 2
      have hU : S.vis st.level \ (st.white ∪ insert x st.black) =
          (S.vis st.level \ (st.white ∪ st.black)) \ {x} := by
        ext p; simp only [mem_diff, mem_union, mem_insert_iff, mem_singleton_iff]; tauto
      have hempty : (S.vis st.level \ (st.white ∪ st.black)) \ {x} = ∅ := by
        ext p
        simp only [mem_diff, mem_union, mem_singleton_iff, mem_empty_iff_false, iff_false]
        rintro ⟨⟨hpV, hpWB⟩, hpx⟩
        exact hex ⟨p, hpV, fun h => h.elim hpx fun h => hpWB (Or.inr h), fun h => hpWB (Or.inl h)⟩
      have h1 := Set.ncard_sdiff_singleton_of_mem hxU
      rw [hempty, Set.ncard_empty] at h1
      rw [hU, hempty, Set.ncard_empty]
      have : (S.vis st.level \ (st.white ∪ st.black)).ncard ≤ 1 := by
        have := Set.ncard_pos hUfin |>.2 ⟨x, hxU⟩
        omega
      exact le_trans hsum (by omega)
  | @down ms st i h hi ih =>
    obtain ⟨hB, hW, hsum⟩ := ih
    have hil : i ≤ st.level := by rw [Fin.le_def]; omega
    have hlt : i.val < S.r := by have := st.level.isLt; omega
    refine ⟨hB.trans (hmono _ _ hil), hW.trans (hmono _ _ hil), ?_⟩
    change ∑ j ∈ Finset.univ.filter (fun j : Fin (S.r + 1) => i ≤ j), (S.newAt j).ncard / 2 ≤
      st.white.ncard + (S.vis i \ (st.white ∪ st.black)).ncard / 2
    have hfilt : Finset.univ.filter (fun j : Fin (S.r + 1) => i ≤ j) =
        insert i (Finset.univ.filter (fun j : Fin (S.r + 1) => st.level ≤ j)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.le_def,
        Fin.ext_iff]
      omega
    have hnotin : i ∉ Finset.univ.filter (fun j : Fin (S.r + 1) => st.level ≤ j) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]; omega
    rw [hfilt, Finset.sum_insert hnotin]
    have hnew : S.newAt i = S.vis i \ S.vis st.level := by
      have hl : (⟨i.val + 1, by omega⟩ : Fin (S.r + 1)) = st.level := Fin.ext hi
      unfold newAt; rw [dif_pos hlt, hl]
    have hU : S.vis i \ (st.white ∪ st.black) =
        (S.vis st.level \ (st.white ∪ st.black)) ∪ (S.vis i \ S.vis st.level) := by
      ext p
      simp only [mem_diff, mem_union]
      constructor
      · rintro ⟨hp, hpn⟩
        by_cases hpl : p ∈ S.vis st.level
        · exact Or.inl ⟨hpl, hpn⟩
        · exact Or.inr ⟨hp, hpl⟩
      · rintro (⟨hp, hpn⟩ | ⟨hp, hpl⟩)
        · exact ⟨hmono _ _ hil hp, hpn⟩
        · exact ⟨hp, fun h => hpl (h.elim (fun h => hW h) (fun h => hB h))⟩
    have hdisj : Disjoint (S.vis st.level \ (st.white ∪ st.black)) (S.vis i \ S.vis st.level) :=
      Set.disjoint_left.2 fun p hp hq => hq.2 hp.1
    rw [hnew, hU, Set.ncard_union_eq hdisj (hfin' _).diff (hfin' _).diff]
    omega

/-- **Generic helper** for Remark 5 and the parallel paragraph of §8.3.1 (one result for both): if
visibility only grows as the level decreases and is finite, then for **every** strategy following
the greedy rule (whichever free visible point it claims), at every legal stop at level `i` White
holds at least `∑_{j ≥ i} ⌊|newAt j| / 2⌋` visible points. -/
theorem greedy_stop_bound (hmono : ∀ i j : Fin (S.r + 1), i ≤ j → S.vis j ⊆ S.vis i)
    (hfin : (S.vis 0).Finite) (σ : WStrategy d) (hσ : S.IsGreedy σ) (ms : List (BMove d))
    (st : S.State) (hreach : StopGame.Reach S σ ms st)
    (hstop : S.visible st.level ⊆ st.black ∪ st.white) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin (S.r + 1) => st.level ≤ j), (S.newAt j).ncard / 2 ≤
      (st.white ∩ S.visible st.level).ncard := by
  obtain ⟨-, hW, hsum⟩ := GameAux.greedy_inv S hmono hfin σ hσ hreach
  have hempty : S.vis st.level \ (st.white ∪ st.black) = ∅ := by
    ext p
    simp only [mem_diff, mem_union, mem_empty_iff_false, iff_false, not_and, not_not]
    intro hp
    rcases hstop hp with h | h
    · exact Or.inr h
    · exact Or.inl h
  rw [hempty, Set.ncard_empty, Nat.zero_div, add_zero] at hsum
  have hWv : st.white ∩ S.visible st.level = st.white := Set.inter_eq_left.2 hW
  rw [hWv]
  exact hsum

end StopGame


/-- Moving `n` levels down from a reached state (no White reply) gives a reached state with the
same points. -/
theorem StopGame.Reach.downs {d : ℕ} {S : StopGame d} {σ : WStrategy d} {ms : List (BMove d)}
    {lvl : Fin (S.r + 1)} {b w : Set (Pt d)} (h : S.Reach σ ms ⟨lvl, b, w⟩) :
    ∀ n m (hm : m + n = lvl.val),
      S.Reach σ (ms ++ List.replicate n BMove.down) ⟨⟨m, by have := lvl.isLt; omega⟩, b, w⟩ := by
  intro n
  induction n with
  | zero =>
    intro m hm
    have hl : (⟨m, by have := lvl.isLt; omega⟩ : Fin (S.r + 1)) = lvl := Fin.ext (by simpa using hm)
    rw [hl]
    simpa using h
  | succ n ih =>
    intro m hm
    have h1 := ih (m + 1) (by omega)
    have h2 := StopGame.Reach.down (i := ⟨m, by have := lvl.isLt; omega⟩) h1 rfl
    rw [List.replicate_succ', ← List.append_assoc]
    exact h2

end BanachDensityHD
