import BanachDensity1D.Nov1.Balanced

/-! # Integer interval forms of the mechanical-core discrepancy estimate. -/

namespace BanachDensity1D.FullRangeAux
open Set Filter

/-- Natural floors in the implementation give precisely the manuscript's integer-floor core. -/
lemma coreNat_iff_intFloor {ρ : ℝ} (hρ0 : 0 ≤ ρ) (j : ℕ) :
    j ∈ coreNat ρ ↔
      ⌊((j + 1 : ℕ) : ℝ) * ρ⌋ - ⌊(j : ℝ) * ρ⌋ = (1 : ℤ) := by
  have h0 : 0 ≤ (j : ℝ) * ρ := by positivity
  have h1 : 0 ≤ ((j + 1 : ℕ) : ℝ) * ρ := by positivity
  rw [← Int.natCast_floor_eq_floor h0, ← Int.natCast_floor_eq_floor h1]
  change _ = _ + 1 ↔ _ - _ = (1 : ℤ)
  omega

open Classical in
lemma core_Ico_image (ρ : ℝ) (a b : ℕ) :
    core ρ ∩ Ico (a : ℤ) (b : ℤ) =
      (fun j : ℕ => (j : ℤ)) ''
        (((Finset.Ico a b).filter (fun j => j ∈ coreNat ρ)) : Set ℕ) := by
  ext x
  constructor
  · rintro ⟨⟨hx0, hxcore⟩, hlo, hup⟩
    refine ⟨x.toNat, ?_, Int.toNat_of_nonneg hx0⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hxcore⟩
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨hJ, hc⟩ := Finset.mem_filter.mp hj
    obtain ⟨hlo, hup⟩ := Finset.mem_Ico.mp hJ
    refine ⟨⟨by positivity, ?_⟩, ?_, ?_⟩
    · simpa using hc
    · change (a : ℤ) ≤ (j : ℤ)
      exact_mod_cast hlo
    · change (j : ℤ) < (b : ℤ)
      exact_mod_cast hup

lemma core_Ico_discrepancy {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {a b : ℕ} (hab : a ≤ b) :
    |((core ρ ∩ Ico (a : ℤ) (b : ℤ)).ncard : ℝ) - ρ * ((b : ℝ) - a)| < 1 := by
  rw [core_Ico_image, ncard_image_of_injective _ (Nat.cast_injective), ncard_coe_finset]
  exact interval_discrepancy hρ0 hρ1 hab

lemma int_Icc_ncard {a b : ℕ} (hab : a ≤ b) :
    ((Icc (a : ℤ) (b : ℤ)).ncard : ℝ) = (b : ℝ) + 1 - a := by
  have hc : (Icc (a : ℤ) (b : ℤ)).ncard = b + 1 - a := by
    rw [Set.ncard_Icc, Int.card_Icc]
    omega
  rw [hc, Nat.cast_sub (by omega)]
  push_cast
  ring

/-- The exact uniform interval estimate, expressed using the integer window's actual cardinality. -/
lemma core_Icc_discrepancy {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {a b : ℕ} (hab : a ≤ b) :
    |((core ρ ∩ Icc (a : ℤ) (b : ℤ)).ncard : ℝ) -
      ρ * ((Icc (a : ℤ) (b : ℤ)).ncard : ℝ)| < 1 := by
  have he : Ico (a : ℤ) ((b + 1 : ℕ) : ℤ) = Icc (a : ℤ) (b : ℤ) := by
    ext x
    simp only [mem_Ico, mem_Icc]
    push_cast
    omega
  have hd := core_Ico_discrepancy hρ0 hρ1 (show a ≤ b + 1 by omega)
  rw [he] at hd
  rw [int_Icc_ncard hab]
  simpa only [Nat.cast_add, Nat.cast_one] using hd

/-- Every nonempty relative interval of N has nonnegative integer endpoints. -/
lemma relative_interval_K0 {J : Set ℤ} (hJ : IsRelInterval PriorZero.Construction.K0 J)
    (hpos : 0 < J.ncard) : ∃ a b : ℕ, a ≤ b ∧ J = Icc (a : ℤ) (b : ℤ) := by
  obtain ⟨a, b, rfl⟩ := hJ
  obtain ⟨x, hx⟩ := nonempty_of_ncard_ne_zero (Nat.ne_zero_of_lt hpos)
  have hx0 : 0 ≤ x := hx.1
  have hxa := hx.2.1
  have hxb := hx.2.2
  have hb0 : 0 ≤ b := by omega
  have hm0 : 0 ≤ max a 0 := le_max_right _ _
  refine ⟨(max a 0).toNat, b.toNat, ?_, ?_⟩
  · omega
  · ext y
    simp only [mem_inter_iff, PriorZero.Construction.K0, mem_Ici, mem_Icc,
      Int.toNat_of_nonneg hm0, Int.toNat_of_nonneg hb0]
    omega

lemma core_relative_discrepancy {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {J : Set ℤ} (hJ : IsRelInterval PriorZero.Construction.K0 J) (hpos : 0 < J.ncard) :
    |((core ρ ∩ J).ncard : ℝ) - ρ * (J.ncard : ℝ)| < 1 := by
  obtain ⟨a, b, hab, rfl⟩ := relative_interval_K0 hJ hpos
  exact core_Icc_discrepancy hρ0 hρ1 hab

end BanachDensity1D.FullRangeAux
