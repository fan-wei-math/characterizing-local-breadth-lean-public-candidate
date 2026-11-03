import BanachDensityHD.AppendixAConstruction

/-!
# Section 9: finite Cantor–Bendixson rank

Kleinberg–Wei, *Characterizing Local Breadth in Language Generation*.
Historical source numbering is retained; current mappings are in the release registry.

-/

namespace BanachDensityHD

open Set Filter
open scoped Classical

/-! ## Proof development (helpers for §9) -/

namespace FiniteRankAux

section Rank
variable {α : Type*} {X : Set (Set α)}

/-- Every open set of the finite-evidence topology containing `x` contains a basic set
`U_{x,F}` with `F ⊆ x` finite (port of the 1D `TheoremsAux.evidence_nhds_basis`). -/
theorem evidence_nhds_basis (U : Set X) (hU : (evidenceTopology X).IsOpen U) :
    ∀ x ∈ U, ∃ F : Set α, F.Finite ∧ F ⊆ x.1 ∧ evidenceSet X x.1 F ⊆ U := by
  change TopologicalSpace.GenerateOpen _ U at hU
  induction hU with
  | basic s hs =>
    obtain ⟨L, -, F, hF, -, rfl⟩ := hs
    intro x hx
    exact ⟨F, hF, hx.1, fun M hM => ⟨hM.1, hM.2.trans hx.2⟩⟩
  | univ =>
    intro x _
    exact ⟨∅, finite_empty, empty_subset _, subset_univ _⟩
  | inter s t _ _ ihs iht =>
    intro x hx
    obtain ⟨F₁, hF₁, hF₁x, h₁⟩ := ihs x hx.1
    obtain ⟨F₂, hF₂, hF₂x, h₂⟩ := iht x hx.2
    refine ⟨F₁ ∪ F₂, hF₁.union hF₂, union_subset hF₁x hF₂x, fun M hM => ⟨?_, ?_⟩⟩
    · exact h₁ ⟨subset_union_left.trans hM.1, hM.2⟩
    · exact h₂ ⟨subset_union_right.trans hM.1, hM.2⟩
  | sUnion S _ ih =>
    rintro x ⟨s, hs, hx⟩
    obtain ⟨F, hF, hFx, hsub⟩ := ih s hs x hx
    exact ⟨F, hF, hFx, hsub.trans (subset_sUnion_of_mem hs)⟩

/-- A language of `X` outside `X^{(r)}` has some point rank `r' < r`. -/
theorem exists_rank_of_not_mem {M : Set α} (hM : M ∈ X) :
    ∀ {r : ℕ}, (⟨M, hM⟩ : X) ∉ cbDerived X r → ∃ r' < r, PointRank X M r'
  | 0, h => absurd (mem_univ _) h
  | r + 1, h => by
    by_cases hr : (⟨M, hM⟩ : X) ∈ cbDerived X r
    · exact ⟨r, Nat.lt_succ_self r, hM, hr, h⟩
    · obtain ⟨r', hr', hrank⟩ := exists_rank_of_not_mem hM hr
      exact ⟨r', by omega, hrank⟩

/-- The protected set of a finite-rank language (proof of Theorem 9.2): if `L` has point rank
`r`, it is isolated in `X^{(r)}`, so some finite `P ⊆ L` has `U_{L,P} ∩ X^{(r)} = {L}`; every
`M ∈ X` with `P ⊆ M ⊊ L` then has point rank `< r`. -/
theorem finite_rank_witness {L : Set α} {r : ℕ} (hL : PointRank X L r) :
    ∃ F : Set α, F.Finite ∧ F ⊆ L ∧ ∀ M ∈ X, F ⊆ M → M ⊂ L → ∃ r' < r, PointRank X M r' := by
  obtain ⟨hLX, hr, hr1⟩ := hL
  have hiso : ∃ U : Set X, (evidenceTopology X).IsOpen U ∧
      U ∩ cbDerived X r = {(⟨L, hLX⟩ : X)} := by
    by_contra hc
    exact hr1 ⟨hr, hc⟩
  obtain ⟨U, hU, hUeq⟩ := hiso
  have hxU : (⟨L, hLX⟩ : X) ∈ U ∩ cbDerived X r := by rw [hUeq]; rfl
  obtain ⟨F, hF, hFL, hsub⟩ := evidence_nhds_basis U hU _ hxU.1
  refine ⟨F, hF, hFL, fun M hM hFM hML => ?_⟩
  apply exists_rank_of_not_mem hM
  intro hMr
  have hmem : (⟨M, hM⟩ : X) ∈ U ∩ cbDerived X r := ⟨hsub ⟨hFM, hML.1⟩, hMr⟩
  rw [hUeq, mem_singleton_iff] at hmem
  exact hML.ne (congrArg Subtype.val hmem)

variable (X)

/-- The least point rank of `L` (`0` when `L` has no finite point rank). -/
noncomputable def rk (L : Set α) : ℕ := if h : ∃ r, PointRank X L r then Nat.find h else 0

/-- The protected set `P_L` of the proof of Theorem 9.2 (empty without finite point rank). -/
noncomputable def prot (L : Set α) : Set α :=
  if h : ∃ r, PointRank X L r then (finite_rank_witness (Nat.find_spec h)).choose else ∅

variable {X}

theorem prot_finite (L : Set α) : (prot X L).Finite := by
  unfold prot; split_ifs with h
  · exact (finite_rank_witness (Nat.find_spec h)).choose_spec.1
  · exact finite_empty

theorem prot_sub (L : Set α) : prot X L ⊆ L := by
  unfold prot; split_ifs with h
  · exact (finite_rank_witness (Nat.find_spec h)).choose_spec.2.1
  · exact empty_subset _

/-- Every proper refinement `M ∈ X` with `P_L ⊆ M ⊊ L` of a finite-rank `L` has finite point
rank, and its (least) rank is strictly smaller. -/
theorem rank_step {L M : Set α} (hL : ∃ r, PointRank X L r) (hM : M ∈ X)
    (hPM : prot X L ⊆ M) (hML : M ⊂ L) :
    (∃ r, PointRank X M r) ∧ rk X M < rk X L := by
  unfold prot at hPM
  rw [dite_eq_left hL] at hPM
  obtain ⟨r', hr', hM'⟩ := (finite_rank_witness (Nat.find_spec hL)).choose_spec.2.2 M hM hPM hML
  have hMr : ∃ r, PointRank X M r := ⟨r', hM'⟩
  refine ⟨hMr, ?_⟩
  unfold rk
  rw [dite_eq_left hL, dite_eq_left hMr]
  exact lt_of_le_of_lt (Nat.find_min' hMr hM') hr'

end Rank

section Interleave
variable {d : ℕ}

/-- Black's claims inside `E`. -/
def keep (E : Finset (Pt d)) : BMove d → Bool
  | .claim y => decide (y ∈ E)
  | .down => false

/-- The projection of Black's moves onto the layer `E`: his claims in `E`, in order. -/
def proj (E : Finset (Pt d)) (ms : List (BMove d)) : List (BMove d) := ms.filter (keep E)

/-- The interleaved White strategy: after a claim of `x`, follow the strategy of the layer
`lay x` on the projection of the play onto that layer; otherwise pass. -/
def comb (lay : Pt d → ℕ) (E : ℕ → Finset (Pt d)) (σs : ℕ → WStrategy d) : WStrategy d :=
  fun ms => match ms.getLast? with
    | some (.claim x) => σs (lay x) (proj (E (lay x)) ms)
    | _ => none

theorem comb_claim (lay : Pt d → ℕ) (E : ℕ → Finset (Pt d)) (σs : ℕ → WStrategy d)
    (ms : List (BMove d)) (x : Pt d) :
    comb lay E σs (ms ++ [.claim x]) = σs (lay x) (proj (E (lay x)) (ms ++ [.claim x])) := by
  simp [comb]

theorem proj_claim_mem {E : Finset (Pt d)} (ms : List (BMove d)) {x : Pt d} (hx : x ∈ E) :
    proj E (ms ++ [.claim x]) = proj E ms ++ [.claim x] := by
  simp [proj, List.filter_append, keep, hx]

theorem proj_claim_not_mem {E : Finset (Pt d)} (ms : List (BMove d)) {x : Pt d} (hx : x ∉ E) :
    proj E (ms ++ [.claim x]) = proj E ms := by
  simp [proj, List.filter_append, keep, hx]

theorem proj_down (E : Finset (Pt d)) (ms : List (BMove d)) :
    proj E (ms ++ [.down]) = proj E ms := by
  simp [proj, List.filter_append, keep]

variable {r : ℕ} (Ls : Fin (r + 1) → Set (Pt d)) (qs : Fin (r + 1) → ℝ)
  (rects : Fin (r + 1) → Finset (Rect d)) (lay : Pt d → ℕ) (E : ℕ → Finset (Pt d))
  (Rsf : ℕ → Finset (Rect d)) (c : ℝ) (σs : ℕ → WStrategy d)

/-- The interleaving invariant: along every legal play of the packet game against the interleaved
strategy, the projection onto each layer `E j` is a legal play of the claim game on `E j` against
the layer's strategy, reaching the traces on `E j` of Black's and White's points. -/
theorem comb_inv
    (hE : ∀ j x, x ∈ E j ↔ x ∈ packetSupport Ls rects ∧ lay x = j)
    (hwins : ∀ j, (claimGame (E j) (Rsf j) c).Wins (σs j))
    {ms : List (BMove d)} {st : (packetGame Ls qs rects).State}
    (hR : (packetGame Ls qs rects).Reach (comb lay E σs) ms st) :
    ∀ j, (claimGame (E j) (Rsf j) c).Reach (σs j) (proj (E j) ms)
      ⟨0, st.black ∩ ↑(E j), st.white ∩ ↑(E j)⟩ := by
  induction hR with
  | nil =>
    intro j
    have : (⟨0, (packetGame Ls qs rects).init.black ∩ ↑(E j),
        (packetGame Ls qs rects).init.white ∩ ↑(E j)⟩ : (claimGame (E j) (Rsf j) c).State) =
        (claimGame (E j) (Rsf j) c).init := by
      simp [StopGame.init, StopGame.State.black, StopGame.State.white]; rfl
    rw [this]; exact StopGame.Reach.nil
  | @claim ms st x hreach hfree hleg ih =>
    intro j
    rcases st with ⟨lvl, b, w⟩
    simp only [StopGame.State.black, StopGame.State.white] at ih
    have hxU : x ∈ packetSupport Ls rects := hfree.1.1
    have hxE : x ∈ E (lay x) := (hE _ x).2 ⟨hxU, rfl⟩
    -- the layer strategy's reply is legal in the layer game
    have hfree0 : (claimGame (E (lay x)) (Rsf (lay x)) c).Free
        ⟨0, b ∩ ↑(E (lay x)), w ∩ ↑(E (lay x))⟩ x :=
      ⟨hxE, fun h => hfree.2.1 h.1, fun h => hfree.2.2 h.1⟩
    have hleg0 := ((hwins (lay x)) _ _ (ih (lay x))).1 x hfree0
    rw [comb_claim, proj_claim_mem ms hxE] at *
    have hrepE : ∀ y, σs (lay x) (proj (E (lay x)) ms ++ [BMove.claim x]) = some y →
        y ∈ E (lay x) := by
      intro y hy
      rw [hy] at hleg0
      exact hleg0.1
    revert hrepE hleg0
    generalize hrep : σs (lay x) (proj (E (lay x)) ms ++ [BMove.claim x]) = rep
    intro hleg0 hrepE
    show (claimGame (E j) (Rsf j) c).Reach (σs j) (proj (E j) (ms ++ [BMove.claim x]))
      ⟨0, insert x b ∩ ↑(E j), (rep.elim w fun y => insert y w) ∩ ↑(E j)⟩
    by_cases hj : j = lay x
    · subst hj
      have hst : (⟨0, insert x b ∩ ↑(E (lay x)), (rep.elim w fun y => insert y w) ∩ ↑(E (lay x))⟩ :
          (claimGame (E (lay x)) (Rsf (lay x)) c).State) =
          (claimGame (E (lay x)) (Rsf (lay x)) c).afterClaim
            ⟨0, b ∩ ↑(E (lay x)), w ∩ ↑(E (lay x))⟩ x rep := by
        show StopGame.State.mk _ _ _ = StopGame.State.mk _ _ _
        congr 1
        · rw [Set.insert_inter_of_mem (by exact_mod_cast hxE)]; rfl
        · rcases hr : rep with _ | y
          · rfl
          · simp only [Option.elim]
            rw [Set.insert_inter_of_mem (by exact_mod_cast hrepE y hr)]; rfl
      rw [hst, proj_claim_mem ms hxE, ← hrep]
      rw [← hrep] at hleg0
      exact StopGame.Reach.claim (ih _) hfree0 hleg0
    · have hxj : x ∉ E j := fun h => hj ((hE j x).1 h).2.symm
      rw [proj_claim_not_mem _ hxj]
      have hst : (⟨0, insert x b ∩ ↑(E j), (rep.elim w fun y => insert y w) ∩ ↑(E j)⟩ :
          (claimGame (E j) (Rsf j) c).State) = ⟨0, b ∩ ↑(E j), w ∩ ↑(E j)⟩ := by
        congr 1
        · rw [Set.insert_inter_of_notMem (by exact_mod_cast hxj)]
        · rcases hr : rep with _ | y
          · rfl
          · simp only [Option.elim]
            have hyj : y ∉ E j := by
              intro h
              exact hj (((hE j y).1 h).2.symm.trans ((hE _ y).1 (hrepE y hr)).2)
            rw [Set.insert_inter_of_notMem (by exact_mod_cast hyj)]
      rw [hst]
      exact ih j
  | @down ms st i hreach hi ih =>
    intro j
    rw [proj_down]
    exact ih j

end Interleave

section Layers
variable {d r : ℕ} (Ls : Fin (r + 1) → Set (Pt d))

/-- The greatest level whose language contains the point, defaulting to `0` if none
does. Outside the union this default does not imply membership; `mem_lay` supplies
membership only with a premise that the point lies in some level. -/
noncomputable def lay (x : Pt d) : ℕ :=
  Nat.findGreatest (fun j => ∃ hj : j < r + 1, x ∈ Ls ⟨j, hj⟩) r

theorem lay_le (x : Pt d) : lay Ls x ≤ r := Nat.findGreatest_le r

theorem le_lay {x : Pt d} {i : Fin (r + 1)} (hx : x ∈ Ls i) : i.val ≤ lay Ls x :=
  Nat.le_findGreatest (m := i.val) (Nat.lt_succ_iff.1 i.isLt) ⟨i.isLt, hx⟩

theorem mem_lay {x : Pt d} {i : Fin (r + 1)} (hx : x ∈ Ls i) :
    x ∈ Ls ⟨lay Ls x, by have := lay_le Ls x; omega⟩ := by
  obtain ⟨_, h⟩ := Nat.findGreatest_spec (P := fun j => ∃ hj : j < r + 1, x ∈ Ls ⟨j, hj⟩)
    (m := i.val) (n := r) (Nat.lt_succ_iff.1 i.isLt) ⟨i.isLt, hx⟩
  exact h

/-- On a nonincreasing chain, a point of some level lies exactly in the levels up to its layer. -/
theorem mem_iff_le_lay (hanti : Antitone Ls) {x : Pt d} {i0 : Fin (r + 1)} (hx0 : x ∈ Ls i0)
    (i : Fin (r + 1)) : x ∈ Ls i ↔ i.val ≤ lay Ls x := by
  refine ⟨le_lay Ls, fun h => ?_⟩
  have hle : i ≤ (⟨lay Ls x, by have := lay_le Ls x; omega⟩ : Fin (r + 1)) :=
    Fin.le_iff_val_le_val.2 h
  exact hanti hle (mem_lay Ls hx0)

end Layers

/-- Counting a finite set by the fibres of a function into `T`. -/
theorem ncard_fiber {β : Type*} {A : Set β} (hA : A.Finite) (f : β → ℕ) (T : Finset ℕ)
    (hT : ∀ x ∈ A, f x ∈ T) :
    (A.ncard : ℝ) = ∑ j ∈ T, ((A ∩ {x | f x = j}).ncard : ℝ) := by
  rw [Set.ncard_eq_toFinset_card A hA,
    Finset.card_eq_sum_card_fiberwise (f := f) (t := T) (fun x hx => hT x (by simpa using hx))]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Set.ncard_coe_finset]
  congr 2
  ext x
  simp

/-- **Geometric feasibility by interleaved layer strategies** (proof of Theorem 9.2). Let
`L₀ ⊇ ⋯ ⊇ L_r` be nonincreasing and let a quota-`(1/2 - ε/2)` claim-game strategy exist for
every board, as in Lemma 9.1 with `η = ε/2` and constant `C`. If at every level the quota is
`≤ 0`, or is at most `1/2 - ε` while the number `r + 1 - i` of visible layers satisfies
`(r + 1 - i) C ≤ ε sᵢ`, then the chain is geometrically feasible (outside every box). White plays,
on each claim, Lemma 9.1's strategy of the layer `E_j = U ∩ (L_j \ L_{j+1})` of the claimed point. -/
theorem layered_feasible {d r : ℕ} {h : ℕ → ℝ} {C ε : ℝ} (hC0 : 0 < C) (hε0 : 0 < ε)
    (hε : ε < 1 / 2)
    (hlem : ∀ (E : Finset (Pt d)) (Rs : Finset (Rect d)),
      (claimGame E (Rs.filter fun R => C * h R.vol ≤ ((↑E ∩ R.pts : Set (Pt d)).ncard : ℝ))
        (1 / 2 - ε / 2)).Feasible)
    (hh : ∀ n, 0 ≤ h n) (Ls : Fin (r + 1) → Set (Pt d)) (hanti : Antitone Ls)
    (qs ss : Fin (r + 1) → ℝ)
    (hq : ∀ i, qs i ≤ 0 ∨ (qs i ≤ 1 / 2 - ε ∧ ((r + 1 - i.val : ℕ) : ℝ) * C ≤ ε * ss i))
    (a : ℝ) : GeomFeasible h Ls qs ss a := by
  intro rects hrects
  set U := packetSupport Ls rects with hU
  have hUfin : U.Finite := Set.finite_iUnion fun i =>
    (rects i).finite_toSet.biUnion fun R _ => (BasicAux.rect_pts_finite R).inter_of_right _
  have hU0 : ∀ x ∈ U, ∃ i, x ∈ Ls i := by
    intro x hx
    simp only [hU, packetSupport, Set.mem_iUnion] at hx
    obtain ⟨i, R, _, hx⟩ := hx
    exact ⟨i, hx.1⟩
  let E : ℕ → Finset (Pt d) := fun j => hUfin.toFinset.filter fun x => lay Ls x = j
  have hE : ∀ j x, x ∈ E j ↔ x ∈ U ∧ lay Ls x = j := by intro j x; simp [E]
  let Rs : Finset (Rect d) := Finset.univ.biUnion rects
  let Rsf : ℕ → Finset (Rect d) := fun j =>
    Rs.filter fun R => C * h R.vol ≤ ((↑(E j) ∩ R.pts : Set (Pt d)).ncard : ℝ)
  choose σs hσs using fun j => hlem (E j) Rs
  refine ⟨comb (lay Ls) E σs, fun ms st hR => ?_⟩
  have hinv := comb_inv Ls qs rects (lay Ls) E Rsf (1 / 2 - ε / 2) σs hE hσs hR
  rcases st with ⟨lvl, b, w⟩
  simp only [StopGame.State.black, StopGame.State.white] at hinv
  refine ⟨fun x hfree => ?_, fun hstop R hR => ?_⟩
  · -- every reply is legal
    have hxU : x ∈ U := hfree.1.1
    have hxE : x ∈ E (lay Ls x) := (hE _ x).2 ⟨hxU, rfl⟩
    have hfree0 : (claimGame (E (lay Ls x)) (Rsf (lay Ls x)) (1 / 2 - ε / 2)).Free
        ⟨0, b ∩ ↑(E (lay Ls x)), w ∩ ↑(E (lay Ls x))⟩ x :=
      ⟨hxE, fun h => hfree.2.1 h.1, fun h => hfree.2.2 h.1⟩
    have hleg0 := ((hσs (lay Ls x)) _ _ (hinv (lay Ls x))).1 x hfree0
    rw [comb_claim, proj_claim_mem ms hxE]
    revert hleg0
    generalize σs (lay Ls x) (proj (E (lay Ls x)) ms ++ [BMove.claim x]) = rep
    intro hleg0
    rcases rep with _ | y
    · trivial
    · obtain ⟨hyE, hyb, hyw⟩ := hleg0
      obtain ⟨hyU, hyl⟩ := (hE _ y).1 hyE
      have hxl : lvl.val ≤ lay Ls x := le_lay Ls hfree.1.2
      obtain ⟨i0, hi0⟩ := hU0 y hyU
      refine ⟨⟨hyU, (mem_iff_le_lay Ls hanti hi0 lvl).2 (by omega)⟩, fun h => hyb ?_,
        fun h => hyw ⟨h, hyE⟩⟩
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hyE⟩
  · -- the requirement at a stop
    change R ∈ rects lvl at hR
    change U ∩ Ls lvl ⊆ b ∪ w at hstop
    show qs lvl * ((Ls lvl ∩ R.pts).ncard : ℝ) ≤ ((w ∩ Ls lvl ∩ R.pts).ncard : ℝ)
    have hm0 : (0 : ℝ) ≤ ((Ls lvl ∩ R.pts).ncard : ℝ) := by positivity
    rcases hq lvl with hq0 | ⟨hq1, hq2⟩
    · exact le_trans (mul_nonpos_of_nonpos_of_nonneg hq0 hm0) (by positivity)
    have hk : (0 : ℝ) < 1 / 2 - ε / 2 := by linarith
    have hCh : 0 ≤ C * h R.vol := mul_nonneg hC0.le (hh _)
    have hmemU : ∀ x ∈ Ls lvl ∩ R.pts, x ∈ U := fun x hx =>
      Set.mem_iUnion.2 ⟨lvl, Set.mem_iUnion₂.2 ⟨R, hR, hx⟩⟩
    have hEi : ∀ j, lvl.val ≤ j → ∀ x ∈ E j, x ∈ Ls lvl := by
      intro j hj x hx
      obtain ⟨hxU, hxl⟩ := (hE j x).1 hx
      obtain ⟨i0, hi0⟩ := hU0 x hxU
      exact (mem_iff_le_lay Ls hanti hi0 lvl).2 (by omega)
    -- the layer bound
    have hper : ∀ j ∈ Finset.Icc lvl.val r,
        (1 / 2 - ε / 2) * (((↑(E j) ∩ R.pts : Set (Pt d)).ncard : ℝ) - C * h R.vol) ≤
          ((w ∩ ↑(E j) ∩ ↑(E j) ∩ R.pts : Set (Pt d)).ncard : ℝ) := by
      intro j hj
      have hj1 := (Finset.mem_Icc.1 hj).1
      by_cases hbig : C * h R.vol ≤ ((↑(E j) ∩ R.pts : Set (Pt d)).ncard : ℝ)
      · have hexh : ((claimGame (E j) (Rsf j) (1 / 2 - ε / 2)).visible
            (⟨0, b ∩ ↑(E j), w ∩ ↑(E j)⟩ : (claimGame (E j) (Rsf j) (1 / 2 - ε / 2)).State).level)
            ⊆ (b ∩ ↑(E j)) ∪ (w ∩ ↑(E j)) := by
          intro x hx
          have hx' : x ∈ E j := hx
          rcases hstop ⟨((hE j x).1 hx').1, hEi j hj1 x hx'⟩ with h | h
          · exact Or.inl ⟨h, hx⟩
          · exact Or.inr ⟨h, hx⟩
        have hRf : R ∈ Rsf j :=
          Finset.mem_filter.2 ⟨Finset.mem_biUnion.2 ⟨lvl, Finset.mem_univ _, hR⟩, hbig⟩
        have hw := ((hσs j) _ _ (hinv j)).2 hexh R hRf
        have hw' : (1 / 2 - ε / 2) * ((↑(E j) ∩ R.pts : Set (Pt d)).ncard : ℝ) ≤
            ((w ∩ ↑(E j) ∩ ↑(E j) ∩ R.pts : Set (Pt d)).ncard : ℝ) := hw
        nlinarith
      · push Not at hbig
        have : (0 : ℝ) ≤ ((w ∩ ↑(E j) ∩ ↑(E j) ∩ R.pts : Set (Pt d)).ncard : ℝ) := by positivity
        nlinarith
    have hfinA : (Ls lvl ∩ R.pts).Finite := (BasicAux.rect_pts_finite R).inter_of_right _
    have hfinW : (w ∩ Ls lvl ∩ R.pts).Finite := (BasicAux.rect_pts_finite R).inter_of_right _
    have hT : ∀ x ∈ Ls lvl ∩ R.pts, lay Ls x ∈ Finset.Icc lvl.val r := fun x hx =>
      Finset.mem_Icc.2 ⟨le_lay Ls hx.1, lay_le Ls x⟩
    have hA := ncard_fiber hfinA (lay Ls) _ hT
    have hW := ncard_fiber hfinW (lay Ls) (Finset.Icc lvl.val r) fun x hx => hT x ⟨hx.1.2, hx.2⟩
    have hfibA : ∀ j ∈ Finset.Icc lvl.val r,
        Ls lvl ∩ R.pts ∩ {x | lay Ls x = j} = ↑(E j) ∩ R.pts := by
      intro j hj
      ext x
      constructor
      · rintro ⟨hx, hxl⟩
        exact ⟨(hE j x).2 ⟨hmemU x hx, hxl⟩, hx.2⟩
      · rintro ⟨hx, hxR⟩
        exact ⟨⟨hEi j (Finset.mem_Icc.1 hj).1 x hx, hxR⟩, ((hE j x).1 hx).2⟩
    have hfibW : ∀ j ∈ Finset.Icc lvl.val r,
        w ∩ Ls lvl ∩ R.pts ∩ {x | lay Ls x = j} = w ∩ ↑(E j) ∩ ↑(E j) ∩ R.pts := by
      intro j hj
      ext x
      constructor
      · rintro ⟨⟨⟨hxw, hxL⟩, hxR⟩, hxl⟩
        have hxE : x ∈ E j := (hE j x).2 ⟨hmemU x ⟨hxL, hxR⟩, hxl⟩
        exact ⟨⟨⟨hxw, hxE⟩, hxE⟩, hxR⟩
      · rintro ⟨⟨⟨hxw, hx⟩, -⟩, hxR⟩
        exact ⟨⟨⟨hxw, hEi j (Finset.mem_Icc.1 hj).1 x hx⟩, hxR⟩, ((hE j x).1 hx).2⟩
    rw [Finset.sum_congr rfl fun j hj => by rw [hfibA j hj]] at hA
    rw [Finset.sum_congr rfl fun j hj => by rw [hfibW j hj]] at hW
    have hsum := Finset.sum_le_sum hper
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, ← hA, ← hW,
      nsmul_eq_mul] at hsum
    -- the small layers carry at most `ε m` points
    have hmass : ss lvl * h R.vol ≤ ((Ls lvl ∩ R.pts).ncard : ℝ) := (hrects lvl R hR).2
    have hsmall : ((r + 1 - lvl.val : ℕ) : ℝ) * (C * h R.vol) ≤
        ε * ((Ls lvl ∩ R.pts).ncard : ℝ) := by
      have h1 : ((r + 1 - lvl.val : ℕ) : ℝ) * C * h R.vol ≤ ε * ss lvl * h R.vol :=
        mul_le_mul_of_nonneg_right hq2 (hh _)
      have h2 : ε * (ss lvl * h R.vol) ≤ ε * ((Ls lvl ∩ R.pts).ncard : ℝ) :=
        mul_le_mul_of_nonneg_left hmass hε0.le
      nlinarith
    set m := ((Ls lvl ∩ R.pts).ncard : ℝ)
    have h3 : (1 / 2 - ε / 2) * (m - ε * m) ≤
        (1 / 2 - ε / 2) * (m - ((r + 1 - lvl.val : ℕ) : ℝ) * (C * h R.vol)) :=
      mul_le_mul_of_nonneg_left (by linarith) hk.le
    have h4 : (1 / 2 - ε) * m ≤ (1 / 2 - ε / 2) * (m - ε * m) := by
      nlinarith [mul_nonneg (sq_nonneg ε) hm0]
    have h5 : qs lvl * m ≤ (1 / 2 - ε) * m := mul_le_mul_of_nonneg_right hq1 hm0
    linarith


section Deco
variable {d : ℕ} {X : Set (Set (Pt d))}

variable (X) in
/-- The neighbourhood of the proof of Theorem 9.2: the chains from `K` each of whose steps
`L_j ⊋ L_{j+1}` contains the protected set `P_{L_j}` (the paths of the protected tree). -/
def hist (K : Set (Pt d)) : Set (History X) :=
  {H | H.1.headD ∅ = K ∧ ∀ j (hj : j + 1 < H.1.length), prot X H.1[j] ⊆ H.1[j + 1]}

variable (X) in
/-- The cutoff of Theorem 9.2: for positive accuracy `ε`, `max(1, (r+1)C/ε)` at a
language of point rank `r`, and `1` without finite point rank. Division is totalized; at
`ε = 0` the cutoff is `1`, rather than an infinite positive-accuracy limit. -/
noncomputable def cut (C ε : ℝ) (L : Set (Pt d)) : ℝ :=
  if ∃ r, PointRank X L r then max 1 (((rk X L : ℝ) + 1) * C / ε) else 1

theorem one_le_cut (C ε : ℝ) (L : Set (Pt d)) : 1 ≤ cut X C ε L := by
  unfold cut; split_ifs
  · exact le_max_left _ _
  · exact le_rfl

/-- Along a chain of `hist`, the point rank strictly decreases from a finite-rank language on:
`rk(L_{i+k}) + k ≤ rk(L_i)`. -/
theorem descent {H : History X}
    (hH : ∀ j (hj : j + 1 < H.1.length), prot X H.1[j] ⊆ H.1[j + 1]) (i : ℕ)
    (hr : ∀ hi : i < H.1.length, ∃ r, PointRank X H.1[i] r) :
    ∀ k (hk : i + k < H.1.length),
      (∃ r, PointRank X H.1[i + k] r) ∧ rk X H.1[i + k] + k ≤ rk X H.1[i]
  | 0, hk => ⟨hr hk, le_rfl⟩
  | k + 1, hk => by
    obtain ⟨ih1, ih2⟩ := descent hH i hr k (by omega)
    have hlt := CharAux.isChain_getElem H.2 (i + k) (by omega)
    have hmem : H.1[i + k + 1] ∈ X := H.2.2.1 _ (List.getElem_mem _)
    obtain ⟨h1, h2⟩ := rank_step ih1 hmem (hH (i + k) (by omega)) hlt
    show (∃ r, PointRank X H.1[i + k + 1] r) ∧ rk X H.1[i + k + 1] + (k + 1) ≤ rk X H.1[i]
    exact ⟨h1, by omega⟩

/-- The `q`-good decoration of the proof of Theorem 9.2: the neighbourhood `hist`, the cutoffs
`cut`, and the radius `a(H) = |H|` (the radii are irrelevant here: the feasibility holds outside
every box). -/
theorem deco_exists {h : ℕ → ℝ} {C ε : ℝ} (hC0 : 0 < C) (hε0 : 0 < ε) (hε : ε < 1 / 2)
    (hlem : ∀ (E : Finset (Pt d)) (Rs : Finset (Rect d)),
      (claimGame E (Rs.filter fun R => C * h R.vol ≤ ((↑E ∩ R.pts : Set (Pt d)).ncard : ℝ))
        (1 / 2 - ε / 2)).Feasible)
    (hh : ∀ n, 0 ≤ h n) (q : Set (Pt d) → ℝ)
    (hq : ∀ L, q L ≤ 0 ∨ (q L ≤ 1 / 2 - ε ∧ ∃ r, PointRank X L r)) {K : Set (Pt d)}
    (hK : K ∈ X) :
    IsQGoodDecoration X h q K hK (hist X K) (fun l => cut X C ε (l.getLastD ∅))
      (fun l => (l.length : ℝ)) := by
  refine ⟨fun H hH => hH.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- open
    refine (HistoriesAux.isOpen_iff _).2 fun H hH => ⟨prot X H.last, prot_finite _, prot_sub _,
      fun Γ M hs hFM => ?_⟩
    obtain ⟨-, -, hΓ⟩ := hs
    have hne := H.2.1
    have hlast : H.last = H.1[H.1.length - 1]'(by
        have := List.length_pos_iff.mpr hne; omega) := by
      unfold History.last
      rw [CharAux.getLastD_eq_getLast _ _ hne, List.getLast_eq_getElem]
    refine ⟨?_, fun j hj => ?_⟩
    · rw [hΓ]
      obtain ⟨x, t, e⟩ := List.exists_cons_of_ne_nil hne
      rw [e]
      have := hH.1
      rw [e] at this
      simpa using this
    · have hj' : j + 1 < H.1.length + 1 := by rw [hΓ] at hj; simpa using hj
      simp only [hΓ]
      rcases Nat.lt_or_ge (j + 1) H.1.length with hlt | hge
      · rw [List.getElem_append_left (by omega), List.getElem_append_left hlt]
        exact hH.2 j hlt
      · have hjl : j = H.1.length - 1 := by omega
        subst hjl
        rw [List.getElem_append_left (by omega), List.getElem_append_right (by omega)]
        simp only [List.getElem_singleton]
        rw [← hlast]
        exact hFM
  · -- the root
    refine ⟨rfl, fun j hj => ?_⟩
    simp [History.single] at hj
  · -- prefixes
    intro H hH n hn hc
    refine ⟨?_, fun j hj => ?_⟩
    · obtain ⟨x, t, e⟩ := List.exists_cons_of_ne_nil H.2.1
      have := hH.1
      simp only [e] at this ⊢
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
      simpa using this
    · simp only [List.length_take] at hj
      simp only [List.getElem_take]
      exact hH.2 j (by omega)
  · intro H _
    exact ⟨one_le_cut _ _ _, by positivity⟩
  · intro H _ Γ _ M hs
    rw [hs.2.2]
    simp
  · -- geometric feasibility
    intro H hH
    unfold DecoratedGood
    have hlen := List.length_pos_iff.mpr H.2.1
    refine layered_feasible hC0 hε0 hε hlem hh _ ?_ _ _ ?_ _
    · intro i j hij
      exact CharAux.chain_anti H.2 i j _ _ hij
    · intro i
      rcases hq (listFn H.1 H.2.1 i) with h0 | ⟨h1, hr⟩
      · exact Or.inl h0
      refine Or.inr ⟨h1, ?_⟩
      have hi : i.val < H.1.length := by have := i.isLt; omega
      have hLi : listFn H.1 H.2.1 i = H.1[i.val] := rfl
      rw [hLi] at hr
      simp only
      rw [CharAux.getLastD_take _ _ _ hi]
      have hd := (descent hH.2 i.val (fun _ => hr) (H.1.length - 1 - i.val) (by omega)).2
      have hcnt : H.1.length - 1 + 1 - i.val ≤ rk X H.1[i.val] + 1 := by omega
      unfold cut
      simp only [hr, ↓reduceIte]
      have hcnt' : ((H.1.length - 1 + 1 - i.val : ℕ) : ℝ) ≤ (rk X H.1[i.val] : ℝ) + 1 := by
        exact_mod_cast hcnt
      have hmax : ((rk X H.1[i.val] : ℝ) + 1) * C / ε ≤
          max 1 (((rk X H.1[i.val] : ℝ) + 1) * C / ε) := le_max_right _ _
      have : ε * (((rk X H.1[i.val] : ℝ) + 1) * C / ε) = ((rk X H.1[i.val] : ℝ) + 1) * C := by
        field_simp
      nlinarith [mul_le_mul_of_nonneg_left hmax hε0.le]

end Deco

/-- `1 < log 3`. -/
theorem one_lt_log_three : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

/-- `h_τ = h_g` for `g(x) = log^τ(2+x)`: `log^{1+τ}(2+V) = log^τ(2+V) · log(2+V)`. -/
theorem hLog_eq_hTau {τ : ℝ} : hLog (fun x => Real.log (2 + x) ^ τ) = hTau τ := by
  funext V
  have hV : (0 : ℝ) ≤ V := Nat.cast_nonneg V
  have hpos : 0 < Real.log (2 + (V : ℝ)) := Real.log_pos (by linarith)
  simp only [hLog, hTau]
  rw [Real.rpow_add hpos, Real.rpow_one, mul_comm]

/-- `g(x) = log^τ(2+x)` satisfies `g ≥ 1` on `[1,∞)`. -/
theorem g_one_le {τ : ℝ} (hτ : 0 < τ) (x : ℝ) (hx : 1 ≤ x) : 1 ≤ Real.log (2 + x) ^ τ := by
  have h3 : Real.log 3 ≤ Real.log (2 + x) := Real.log_le_log (by norm_num) (by linarith)
  exact Real.one_le_rpow (by linarith [one_lt_log_three]) hτ.le

/-- `g(x) = log^τ(2+x)` is nondecreasing on `[1,∞)`. -/
theorem g_mono {τ : ℝ} (hτ : 0 < τ) : MonotoneOn (fun x : ℝ => Real.log (2 + x) ^ τ) (Ici 1) := by
  intro x hx y _ hxy
  have hx' : (1 : ℝ) ≤ x := hx
  exact Real.rpow_le_rpow (Real.log_nonneg (by linarith)) (Real.log_le_log (by linarith)
    (by linarith)) hτ.le

theorem hTau_nonneg (τ : ℝ) (n : ℕ) : 0 ≤ hTau τ n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  exact Real.rpow_nonneg (Real.log_nonneg (by linarith)) _

end FiniteRankAux

/-- Finite Cantor–Bendixson rank of the family gives every member a finite point rank
(Definition 2.1), supplying the existential hypothesis of Theorems 8.3(1) and 9.2.
`FiniteRankAux.exists_rank_of_not_mem` proves the stronger bound `< r` from a specified
empty derivative `X^(r)`; this exported corollary discards that quantitative bound. -/
theorem finiteCBRank_pointRank {α : Type*} {X : Set (Set α)} (hX : FiniteCBRank X) {K : Set α}
    (hK : K ∈ X) : ∃ r, PointRank X K r := by
  obtain ⟨r, hr⟩ := hX
  obtain ⟨r', -, h⟩ := FiniteRankAux.exists_rank_of_not_mem hK (r := r) (by rw [hr]; exact id)
  exact ⟨r', h⟩

/-- **Lemma 9.1** (`lem:local-rectangle-strategy`): for `d ≥ 2`, `τ > 0` and every `0 < η < 1/2`
there is `C = C_{d,η,τ} > 0` such that, for every finite `E` and finite family `𝓡`, one White
strategy in the claim game on `E` gives `|W ∩ R| ≥ (1/2 - η)|E ∩ R|` at exhaustion for every
`R ∈ 𝓡` with `|E ∩ R| ≥ C h_d(V(R))`, `h_d = hTau τ`. -/
theorem lem_local_rectangle_strategy {d : ℕ} (hd : 2 ≤ d) {τ : ℝ} (hτ : 0 < τ) :
    ∀ η : ℝ, 0 < η → η < 1 / 2 →
      ∃ C : ℝ, 0 < C ∧ ∀ (E : Finset (Pt d)) (Rs : Finset (Rect d)),
        (claimGame E (Rs.filter fun R =>
            C * hTau τ R.vol ≤ ((↑E ∩ R.pts : Set (Pt d)).ncard : ℝ)) (1 / 2 - η)).Feasible := by
  exact prop_cf_conditional hd hτ fun _ hε hε' => claim_cf_potential_existence d (by omega) hε hε' hτ

/-- **Theorem 9.2**, every fixed `τ > 0`; `PointRank` uses the finite-evidence topology. -/
theorem thm_finite_rank_near_half {d : ℕ} (hd : 2 ≤ d) {X : Set (Set (Pt d))}
    (hX : LangClass X) {τ ε : ℝ} (hτ : 0 < τ) (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    ∃ G ∈ ValidGen X, ∀ K ∈ X, Nonvacuous (hTau τ) K → (∃ r, PointRank X K r) →
      Guarantees (dH (hTau τ)) G K (1 / 2 - ε) := by
  -- Lemma 9.1 with `η = ε/2`
  obtain ⟨C, hC0, hC⟩ := lem_local_rectangle_strategy hd hτ (ε / 2) (by linarith) (by linarith)
  -- `h_τ = h_g` with `g(x) = log^τ(2+x)`
  have hgh := FiniteRankAux.hLog_eq_hTau (τ := τ)
  -- the quota profile `q`
  let q : Set (Pt d) → ℝ := fun L =>
    if Nonvacuous (hTau τ) L ∧ ∃ r, PointRank X L r then 1 / 2 - ε else 0
  have hq01 : ∀ K ∈ X, q K ∈ Icc (0 : ℝ) 1 := by
    intro K _
    simp only [q]
    split_ifs
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨le_rfl, zero_le_one⟩
  have hq : ∀ L, q L ≤ 0 ∨ (q L ≤ 1 / 2 - ε ∧ ∃ r, PointRank X L r) := by
    intro L
    simp only [q]
    split_ifs with hL
    · exact Or.inr ⟨le_rfl, hL.2⟩
    · exact Or.inl le_rfl
  -- a `q`-protected tree at every `K ∈ X`
  have htree : ∀ K ∈ X, ∃ T, IsProtectedTree X (hLog fun x => Real.log (2 + x) ^ τ) q K T := by
    intro K hK
    rw [hgh]
    exact CharAux.tree_of_deco hX.countable hK
      (FiniteRankAux.deco_exists hC0 hε0 hε hC (FiniteRankAux.hTau_nonneg τ) q hq hK)
  -- Theorem 8.1(1)
  obtain ⟨G, hG, hGK⟩ := thm_fixed_quota_suff hd hX (FiniteRankAux.g_one_le hτ)
    (FiniteRankAux.g_mono hτ) q hq01 htree
  refine ⟨G, hG, fun K hK hnv hr => ?_⟩
  have h := hGK K hK
  rw [hgh] at h
  have hqK : q K = 1 / 2 - ε := by simp only [q, hnv, hr, and_self, ↓reduceIte]
  rwa [hqK] at h

/-- **Theorem 8.3(1)** (`thm:overview`): for every `τ > 0`
and `0 < ε < 1/2`, one globally fresh, universally eventually valid generator (depending on `τ`,
`ε`, `𝒳`, `d` only) gives `δ_{h_τ}(O,K) ≥ 1/2 - ε`, `h_τ(V) = (log(2+V))^{1+τ}`, on every full
enumeration of every nonvacuous target of finite point rank; ranks need no common bound. The point
rank is in the finite-evidence topology (`evidenceTopology`, `PointRank`).
This statement is exactly that of `thm_finite_rank_near_half`. 

-/
theorem thm_overview_1 {d : ℕ} (hd : 2 ≤ d) {X : Set (Set (Pt d))} (hX : LangClass X)
    {τ ε : ℝ} (hτ : 0 < τ) (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    ∃ G ∈ ValidGen X, ∀ K ∈ X, Nonvacuous (hTau τ) K → (∃ r, PointRank X K r) →
      Guarantees (dH (hTau τ)) G K (1 / 2 - ε) := by
  exact thm_finite_rank_near_half hd hX hτ hε0 hε


end BanachDensityHD
