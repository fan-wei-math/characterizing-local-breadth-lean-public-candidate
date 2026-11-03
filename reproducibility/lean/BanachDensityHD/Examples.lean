import BanachDensityHD.OneD

/-!
# Named witnesses and definitional tests

Kleinberg–Wei, *Characterizing Local Breadth in Language Generation*.
Historical source numbering is retained; current mappings are in the release registry.

-/

namespace BanachDensityHD

open Set Filter
open scoped Classical




/-! ## Definitional tests (Stage 2): degenerate and boundary cases, each proved -/

/-- Every rectangle is nonempty (singleton sides allowed). -/
example {d : ℕ} (R : Rect d) : R.pts.Nonempty := ⟨R.lo, Set.left_mem_Icc.2 R.le⟩

/-- A single lattice point is a rectangle with one point. -/
example {d : ℕ} (x : Pt d) : (⟨x, x, le_rfl⟩ : Rect d).pts = {x} := Set.Icc_self x

/-- The constant threshold `1` (ordinary Banach density) is admissible. -/
example : IsThreshold (fun _ => 1) := by
  refine ⟨fun _ _ => one_pos, fun _ _ _ _ _ => le_rfl, ?_⟩
  rintro ⟨M, hM⟩
  obtain ⟨n, hn⟩ := exists_nat_gt M
  have := hM ⟨n + 1, by simp [Set.mem_Ici], rfl⟩
  push_cast at this
  linarith

/-- Empty-infimum convention: with no level-`λ` test (empty target, positive `λ`, positive `h`),
the level infimum of `δ_h` is `1`. -/
example {d : ℕ} (h : ℕ → ℝ) (hpos : ∀ n, 0 < h n) (O : Set (Pt d)) {s : ℝ} (hs : 0 < s) :
    testInf h O ∅ s = 1 := by
  unfold testInf
  dsimp only
  rw [if_neg]
  rintro ⟨r, R, hR, -⟩
  simp [mass] at hR
  nlinarith [hpos R.vol]

/-- Monotone copy relation: the identical copy is never its own required child. -/
example {d : ℕ} (P L : Set (Pt d)) (k : ℕ) : ¬ CompatibleCopy P L k L k := by
  rintro ⟨-, -, -, h | ⟨-, h⟩⟩
  · exact (ssubset_irrefl L) h
  · exact lt_irrefl k h

/-- Monotone copy relation: the next copy of the same language is a required child. -/
example {d : ℕ} (P L : Set (Pt d)) (k : ℕ) (hP : P ⊆ L) : CompatibleCopy P L k L (k + 1) :=
  ⟨Nat.succ_pos k, hP, subset_rfl, Or.inr ⟨rfl, Nat.lt_succ_self k⟩⟩

/-- Monotone copy relation: a proper refinement may carry any positive accuracy index, smaller
ones included. -/
example {d : ℕ} (P L M : Set (Pt d)) (k : ℕ) (hP : P ⊆ M) (hM : M ⊂ L) :
    CompatibleCopy P L (k + 5) M 1 :=
  ⟨le_rfl, hP, hM.subset, Or.inl hM⟩

/-- Copy quotas are never negative. -/
example {d : ℕ} (α : Set (Pt d) → ℝ) (L : Set (Pt d)) (k : ℕ) : 0 ≤ copyQuota α L k :=
  le_max_right _ _

/-- Definitional test of the claim game: in
dimension `d = 2` the claim game is genuinely winnable with a positive quota. Two points `a, b`, one
rectangle containing both, quota `1/2`: after Black claims one point, White claims the other. This
only shows that the encoding of the game is not vacuous or malformed in `d ≥ 2`; it is not evidence
for the quantitative Lemma 9.1, whose proof is the manuscript's Appendix A. -/
example : (claimGame ({(fun _ => 0 : Pt 2), (fun i => if i = 0 then 1 else 0 : Pt 2)} :
      Finset (Pt 2))
    {Rect.mk (fun _ => 0) (fun i => if i = 0 then 1 else 0) (fun i => by by_cases h : i = 0 <;> simp [h])}
    (1 / 2)).Feasible := by
  set a : Pt 2 := fun _ => 0 with ha
  set b : Pt 2 := fun i => if i = 0 then 1 else 0 with hb
  have hab : a ≠ b := by
    intro h; have := congrFun h 0; simp [ha, hb] at this
  set R : Rect 2 := Rect.mk a b (fun i => by by_cases h : i = 0 <;> simp [ha, hb, h]) with hR
  set S := claimGame ({a, b} : Finset (Pt 2)) {R} (1 / 2) with hS
  let σ : WStrategy 2 := fun ms => match ms with
    | [BMove.claim x] => some (if x = a then b else a)
    | _ => none
  refine ⟨σ, ?_⟩
  have hvis : ∀ l, S.visible l = ({a, b} : Set (Pt 2)) := fun l => by
    rw [← Finset.coe_pair]; rfl
  -- the reachable states
  have inv : ∀ ms st, StopGame.Reach S σ ms st →
      (ms = [] ∧ st.black = ∅ ∧ st.white = ∅) ∨
      (ms = [BMove.claim a] ∧ st.black = {a} ∧ st.white = {b}) ∨
      (ms = [BMove.claim b] ∧ st.black = {b} ∧ st.white = {a}) := by
    intro ms st h
    induction h with
    | nil => left; exact ⟨rfl, rfl, rfl⟩
    | @claim ms st x h hfree hleg ih =>
      obtain ⟨hxv, hxb, hxw⟩ := hfree
      rw [hvis st.level] at hxv
      rcases ih with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩
      · rcases hxv with rfl | rfl
        · right; left
          refine ⟨rfl, ?_, ?_⟩
          · show insert a st.black = {a}; rw [h1]; simp
          · show (σ ([] ++ [BMove.claim a])).elim st.white (fun y => insert y st.white) = {b}
            rw [h2]; simp [σ]
        · right; right
          refine ⟨rfl, ?_, ?_⟩
          · show insert b st.black = {b}; rw [h1]; simp
          · show (σ ([] ++ [BMove.claim b])).elim st.white (fun y => insert y st.white) = {a}
            rw [h2]; simp [σ, hab.symm]
      · exfalso; rcases hxv with rfl | rfl
        · exact hxb (by rw [h1]; rfl)
        · exact hxw (by rw [h2]; rfl)
      · exfalso; rcases hxv with rfl | rfl
        · exact hxw (by rw [h2]; rfl)
        · exact hxb (by rw [h1]; rfl)
    | @down ms st i h hi ih =>
      exfalso
      have : st.level.val = 0 := by
        have h0 : S.r = 0 := rfl
        have := st.level.isLt; omega
      omega
  intro ms st h
  refine ⟨?_, ?_⟩
  · intro x hfree
    obtain ⟨hxv, hxb, hxw⟩ := hfree
    rw [hvis st.level] at hxv
    rcases inv ms st h with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩
    · rcases hxv with rfl | rfl
      · show S.Free _ (if a = a then b else a)
        rw [if_pos rfl]
        refine ⟨?_, ?_, ?_⟩
        · show b ∈ S.visible st.level; rw [hvis]; simp
        · show b ∉ insert a st.black; rw [h1]; simp [hab.symm]
        · show b ∉ st.white; rw [h2]; simp
      · show S.Free _ (if b = a then b else a)
        rw [if_neg hab.symm]
        refine ⟨?_, ?_, ?_⟩
        · show a ∈ S.visible st.level; rw [hvis]; simp
        · show a ∉ insert b st.black; rw [h1]; simp [hab]
        · show a ∉ st.white; rw [h2]; simp
    · exfalso; rcases hxv with rfl | rfl
      · exact hxb (by rw [h1]; rfl)
      · exact hxw (by rw [h2]; rfl)
    · exfalso; rcases hxv with rfl | rfl
      · exact hxw (by rw [h2]; rfl)
      · exact hxb (by rw [h1]; rfl)
  · intro hstop R' hR'
    have hR'' : R' = R := Finset.mem_singleton.1 hR'
    subst hR''
    have hL : S.L st.level = ({a, b} : Set (Pt 2)) := by rw [← Finset.coe_pair]; rfl
    have hq : S.quota st.level = 1 / 2 := rfl
    have hpts : ({a, b} : Set (Pt 2)) ∩ R.pts = {a, b} := by
      apply inter_eq_left.2
      intro x hx
      rcases hx with rfl | rfl
      · exact Set.left_mem_Icc.2 (Rect.le _)
      · exact Set.right_mem_Icc.2 (Rect.le _)
    rw [hL, hq, hpts, Set.ncard_pair hab]
    rcases inv ms st h with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩
    · exfalso
      have : a ∈ st.black ∪ st.white := hstop (by rw [hvis]; simp)
      simp [h1, h2] at this
    · rw [h2]
      have : ({b} : Set (Pt 2)) ∩ {a, b} ∩ R.pts = {b} := by
        ext x; constructor
        · rintro ⟨⟨hx, -⟩, -⟩; exact hx
        · rintro rfl
          exact ⟨⟨rfl, by simp⟩, Set.right_mem_Icc.2 (Rect.le _)⟩
      rw [this]; norm_num
    · rw [h2]
      have : ({a} : Set (Pt 2)) ∩ {a, b} ∩ R.pts = {a} := by
        ext x; constructor
        · rintro ⟨⟨hx, -⟩, -⟩; exact hx
        · rintro rfl
          exact ⟨⟨rfl, by simp⟩, Set.left_mem_Icc.2 (Rect.le _)⟩
      rw [this]; norm_num


end BanachDensityHD
