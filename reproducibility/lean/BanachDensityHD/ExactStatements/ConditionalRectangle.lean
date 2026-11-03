import BanachDensityHD.AppendixA

/-! Positive-dimensional conditional derivation of A.5.
This proof uses only the assumed scale/potential data, not Claim A.6.
The distinct manuscript-versus-bookkeeping potential-domain issue is retained.
-/
namespace BanachDensityHD.ExactStatements
open Set Filter AppendixAAux
open scoped Classical
noncomputable section

theorem conditional_rectangle_positive_dimension {d : ℕ} (_hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ)
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
end BanachDensityHD.ExactStatements
