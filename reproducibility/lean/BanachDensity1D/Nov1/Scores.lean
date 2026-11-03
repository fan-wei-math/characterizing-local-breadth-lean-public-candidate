import BanachDensity1D.Nov1.Intervals
import BanachDensity1D.Nov1.Relabel

/-! # Pairing estimates for a common balanced core. -/

namespace BanachDensity1D.FullRangeAux
open Set Filter ChainsAux

lemma terminal_mem_layers {H : List (Set ℤ)} (hne : H ≠ []) : chainEnd H ∈ layers H := by
  induction H with
  | nil => contradiction
  | cons L t ih =>
    cases t with
    | nil => simp [chainEnd, layers]
    | cons M t =>
      have ht := ih (by simp)
      simpa [chainEnd, layers] using List.mem_cons_of_mem (L \ M) ht

lemma terminal_core {H : List (Set ℤ)} (hne : H ≠ []) {ρ : ℝ}
    (hall : ∀ L ∈ H, core ρ ⊆ L) : core ρ ⊆ chainEnd H := by
  induction H with
  | nil => contradiction
  | cons L t ih =>
    cases t with
    | nil => simpa [chainEnd] using hall L (by simp)
    | cons M t =>
      apply ih (by simp)
      intro A hA
      exact hall A (List.mem_cons_of_mem L hA)

lemma terminal_pairing_le {H : List (Set ℤ)} (hne : H ≠ []) (J : Set ℤ) :
    (chainEnd H ∩ J).ncard / 2 ≤ layerSum H J := by
  exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.mpr
    ⟨chainEnd H, terminal_mem_layers hne, rfl⟩)

lemma raw_core_lower {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {H : List (Set ℤ)} (hne : H ≠ []) (hall : ∀ L ∈ H, core ρ ⊆ L)
    {J : Set ℤ} (hJ : IsRelInterval PriorZero.Construction.K0 J) (hpos : 0 < J.ncard) :
    ρ / 2 - 1 / (J.ncard : ℝ) ≤ def_raw_pairing_score H J := by
  have hfin := Set.finite_of_ncard_pos hpos
  have hsub : core ρ ∩ J ⊆ chainEnd H ∩ J := inter_subset_inter_left _ (terminal_core hne hall)
  have hcard := ncard_le_ncard hsub (hfin.subset inter_subset_right)
  have hpair := terminal_pairing_le hne J
  have hnat : (core ρ ∩ J).ncard ≤ 2 * layerSum H J + 1 := by omega
  have hreal : ((core ρ ∩ J).ncard : ℝ) ≤ 2 * (layerSum H J : ℝ) + 1 := by exact_mod_cast hnat
  have hd := (abs_lt.mp (core_relative_discrepancy hρ0 hρ1 hJ hpos)).1
  have hp : (0 : ℝ) < J.ncard := by exact_mod_cast hpos
  rw [score_eq, one_div_mul_eq_div]
  apply (le_div_iff₀ hp).mpr
  have hcancel : (ρ / 2 - 1 / (J.ncard : ℝ)) * J.ncard = ρ * J.ncard / 2 - 1 := by
    field_simp
  rw [hcancel]
  linarith

lemma cn_core_lower {C : PriorZero.Construction} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {H : List (Set ℤ)} (hH : IsChain (family C ρ) H)
    (hstart : start H = PriorZero.Construction.K0) {n : ℕ} (hn : 0 < n) :
    ρ / 2 - 1 / (n : ℝ) ≤ cn H n := by
  have hA : (start H).Infinite := hstart ▸ PriorZero.Construction.K0_infinite
  rw [(cn_tendsto hH.1 hH.2.2 hA n).2.1]
  have hb : BddAbove (range (cnSeq H n)) :=
    ⟨1/2, by rintro _ ⟨R, rfl⟩; exact cnSeq_le_half hH.1 hH.2.2 hA n R⟩
  apply le_trans (b := cnSeq H n 0) ?_ (le_ciSup hb 0)
  have : Nonempty (farIntervals H n 0) := (farIntervals_nonempty hA n 0).to_subtype
  apply le_ciInf
  intro J
  have hpos : 0 < J.val.ncard := lt_of_lt_of_le hn J.property.2.1
  have hJ : IsRelInterval PriorZero.Construction.K0 J.val := hstart ▸ J.property.1
  have hlower := raw_core_lower hρ0 hρ1 hH.1 (fun L hL => by
    obtain ⟨M, _, rfl⟩ := hH.2.1 L hL
    exact core_subset_lift ρ M) hJ hpos
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hnm : (n : ℝ) ≤ J.val.ncard := by exact_mod_cast J.property.2.1
  have hinv := one_div_le_one_div_of_le hnreal hnm
  linarith

lemma bn_core_lower (C : PriorZero.Construction) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    {n : ℕ} (hn : 0 < n) :
    ρ / 2 - 1 / (n : ℝ) ≤ bn (family C ρ) PriorZero.Construction.K0 n := by
  have hK := family_K0 C hρ0 hρ1
  have : Nonempty {T : LTree // def_aot (family C ρ) PriorZero.Construction.K0 T} :=
    ⟨⟨.leaf _, rfl, trivial⟩⟩
  apply le_ciInf
  intro T
  obtain ⟨H, hH⟩ := paths_nonempty T.val
  have hpath := path_isChain hK T.property hH
  exact (cn_core_lower hρ0 hρ1.le hpath.1 hpath.2 hn).trans
    (le_ciSup (pathSup_bdd T.property.2 (by rw [T.property.1]; exact PriorZero.Construction.K0_infinite) n) ⟨H, hH⟩)

end BanachDensity1D.FullRangeAux
