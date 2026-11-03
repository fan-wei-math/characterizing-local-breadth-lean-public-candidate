import BanachDensity1D.Nov1.Witness

/-! # Upper bounds supplied by the relabelled B.1 witnesses. -/

namespace BanachDensity1D.FullRangeAux
open Set Filter ChainsAux PriorZero.Construction
open scoped Topology

lemma lifted_window_far {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1)
    (p m R : ℕ) (hp : R < p) (H : List (Set ℤ)) :
    Icc (embed ρ p) (embed ρ ((p : ℤ) + m)) ∈
      farIntervals ((K0 :: H).map (lift ρ)) m R := by
  have hgap : m + phi ρ p ≤ phi ρ (p + m) := by
    simpa only [Nat.add_comm] using (phi_strictMono h0 h1).add_le_nat m p
  have hple : p ≤ phi ρ p := (phi_strictMono h0 h1).le_apply
  have he : (p : ℤ) + m = ((p + m : ℕ) : ℤ) := by push_cast; rfl
  have hc : (Icc (embed ρ p) (embed ρ ((p : ℤ) + m))).ncard ≥ m + 1 := by
    rw [he, embed_nat, embed_nat, Set.ncard_Icc, Int.card_Icc]
    omega
  refine ⟨?_, by omega, ?_⟩
  · refine ⟨embed ρ p, embed ρ ((p : ℤ) + m), ?_⟩
    change _ = lift ρ K0 ∩ _
    rw [lift_K0 h0 h1]
    apply (inter_eq_right.mpr ?_).symm
    intro x hx
    exact le_trans (embed_nonneg ρ (by positivity)) hx.1
  · apply disjoint_left.mpr
    intro x hx hy
    rw [embed_nat] at hx
    have hpi : (R : ℤ) < phi ρ p := by exact_mod_cast lt_of_lt_of_le hp hple
    have := hx.1
    have := hy.2
    omega

lemma raw_trace_upper {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1)
    {p m : ℕ} {H : List (Set ℤ)}
    (h : PrefixTrace (p : ℤ) (Icc (p : ℤ) ((p : ℤ) + m)) m H) :
    def_raw_pairing_score ((K0 :: H).map (lift ρ))
      (Icc (embed ρ p) (embed ρ ((p : ℤ) + m))) ≤ ρ / 2 + 1 / (m + 1 : ℝ) := by
  let J := Icc (embed ρ p) (embed ρ ((p : ℤ) + m))
  have hgap : m + phi ρ p ≤ phi ρ (p + m) := by
    simpa only [Nat.add_comm] using (phi_strictMono h0 h1).add_le_nat m p
  have he : (p : ℤ) + m = ((p + m : ℕ) : ℤ) := by push_cast; rfl
  have hc : m + 1 ≤ J.ncard := by
    dsimp [J]
    rw [he, embed_nat, embed_nat, Set.ncard_Icc, Int.card_Icc]
    omega
  have hp : (0 : ℝ) < J.ncard := by exact_mod_cast lt_of_lt_of_le (Nat.zero_lt_succ m) hc
  have hdis := core_Icc_discrepancy h0 h1.le
    ((phi_strictMono h0 h1).monotone (show p ≤ p + m by omega))
  rw [← embed_nat ρ p, ← embed_nat ρ (p + m), ← he] at hdis
  change |((core ρ ∩ J).ncard : ℝ) - ρ * J.ncard| < 1 at hdis
  have hsum := root_trace_layerSum h0 h1 h
  change layerSum ((K0 :: H).map (lift ρ)) J = ((core ρ ∩ J).ncard + 1) / 2 at hsum
  have hnat : 2 * layerSum ((K0 :: H).map (lift ρ)) J ≤ (core ρ ∩ J).ncard + 1 := by omega
  have hreal : 2 * (layerSum ((K0 :: H).map (lift ρ)) J : ℝ) ≤ (core ρ ∩ J).ncard + 1 := by exact_mod_cast hnat
  have hsup := (abs_lt.mp hdis).2
  have hinv : 1 / (J.ncard : ℝ) ≤ 1 / (m + 1 : ℝ) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast hc
  change def_raw_pairing_score _ J ≤ _
  rw [score_eq, one_div_mul_eq_div]
  have hs : (layerSum ((K0 :: H).map (lift ρ)) J : ℝ) / J.ncard ≤ ρ / 2 + 1 / (J.ncard : ℝ) := by
    apply (div_le_iff₀ hp).mpr
    field_simp
    nlinarith
  linarith

lemma obstruction_cn_upper (C : PriorZero.Construction) {ρ : ℝ}
    (h0 : 0 ≤ ρ) (h1 : ρ < 1) (m n : ℕ) (hnm : n ≤ m)
    {P : List (Set ℤ)} (hP : P ∈ (mapTree (lift ρ) (C.obstruction m)).paths) :
    cn P n ≤ ρ / 2 + 1 / (m + 1 : ℝ) := by
  obtain ⟨H, hH, rfl⟩ := (mapTree_paths _ _ P).mp hP
  obtain ⟨ell, Q, hQ, rfl⟩ := hH
  obtain ⟨B, hB⟩ := C.tower_trace ell m [] hQ m (by simp)
  obtain ⟨D, hD⟩ := C.isolated_eventually m
  have hseq : ∀ R, cnSeq ((K0 :: Q).map (lift ρ)) n R ≤ ρ / 2 + 1 / (m + 1 : ℝ) := by
    intro R
    let r := B + D + R + 1
    have ht := hB r (by dsimp [r]; omega) (hD r (by dsimp [r]; omega))
    have hr : R < C.endpoint r := lt_of_lt_of_le (by dsimp [r]; omega) (C.index_le_endpoint r)
    have hf := lifted_window_far h0 h1 (C.endpoint r) m R hr Q
    have hf' : Icc (embed ρ (C.endpoint r)) (embed ρ ((C.endpoint r : ℤ) + m)) ∈
        farIntervals ((K0 :: Q).map (lift ρ)) n R := ⟨hf.1, hnm.trans hf.2.1, hf.2.2⟩
    exact (ciInf_le (cnSeq_bddBelow _ n R) ⟨_, hf'⟩).trans (raw_trace_upper h0 h1 ht)
  have ha := lifted_obstruction C h0 h1 m
  have hpath := path_isChain (family_K0 C h0 h1) ha
    ((mapTree_paths _ _ _).mpr ⟨_, ⟨ell, Q, hQ, rfl⟩, rfl⟩)
  have hinf : (start ((K0 :: Q).map (lift ρ))).Infinite := by
    rw [hpath.2]
    exact K0_infinite
  exact le_of_tendsto (cn_tendsto hpath.1.1 hpath.1.2.2 hinf n).1 (Eventually.of_forall hseq)

lemma bn_upper (C : PriorZero.Construction) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (n : ℕ) :
    bn (family C ρ) K0 n ≤ ρ / 2 := by
  have hbound : ∀ m, n ≤ m → bn (family C ρ) K0 n ≤ ρ / 2 + 1 / (m + 1 : ℝ) := by
    intro m hnm
    have ha := lifted_obstruction C h0 h1 m
    apply (ciInf_le (bn_bddBelow K0_infinite n) ⟨_, ha⟩).trans
    have : Nonempty (mapTree (lift ρ) (C.obstruction m)).paths := (paths_nonempty _).to_subtype
    exact ciSup_le (fun P => obstruction_cn_upper C h0 h1 m n hnm P.property)
  have ht : Tendsto (fun m : ℕ => ρ / 2 + 1 / (m + 1 : ℝ)) atTop (𝓝 (ρ / 2)) := by
    simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact ge_of_tendsto ht (eventually_atTop.2 ⟨n, hbound⟩)

end BanachDensity1D.FullRangeAux
