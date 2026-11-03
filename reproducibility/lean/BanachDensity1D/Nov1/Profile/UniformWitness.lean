import BanachDensity1D.Nov1.Profile.WitnessSurplus

/-! # One target-dependent surplus bound for every witness stage and every partial interval. -/

namespace BanachDensity1D.ProfileAux
open Set Finset

lemma uniform_witness_lower {m : ℕ → ℕ} (hm : ∀ s, 0 < m s)
    (α : Cut → ℝ) (hα : ∀ q, 0 ≤ α q ∧ α q ≤ 1 / 2)
    (i : ℕ) {c : ℝ} (h0 : 0 ≤ c) (hc : c < α (cutEnumeration i)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : Requirement m hm) (a b : ℕ), a ≤ b →
      b ≤ (R.witness α).length → -C ≤ intervalSum (R.witnessValue α c (cutEnumeration i)) a b := by
  have hc1 : c < 1 / 2 := hc.trans_le (hα (cutEnumeration i)).2
  have hp : 0 < 1 - 2 * c := by linarith
  obtain ⟨N, hN⟩ := exists_nat_ge (c / (1 - 2 * c))
  let S := max (i + 1) N
  let M := ∑ r ∈ range S, m r
  let C : ℝ := 1 + c + c * M
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hCM := mul_nonneg h0 hM
  have hC : 0 ≤ C := by dsimp [C]; linarith
  have hC1 : 1 ≤ C := by dsimp [C]; linarith
  have hCc : c ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro R a b hab hb
  by_cases hlarge : S ≤ R.s + 1
  · have hi : i < R.s + 1 := by have := le_max_left (i + 1) N; dsimp [S] at hlarge; omega
    have hpad : c ≤ (R.s + 1 : ℝ) * (1 - 2 * c) := by
      have hNS : N ≤ R.s + 1 := (le_max_right (i + 1) N).trans hlarge
      have hNR : (N : ℝ) ≤ R.s + 1 := by exact_mod_cast hNS
      have hbound := hN.trans hNR
      exact (div_le_iff₀ hp).mp hbound
    rcases lt_trichotomy R.root (cutEnumeration i) with hlt | heq | hgt
    · have h := R.witness_protected_lower α h0 hc1.le hi hlt hpad hab
      linarith
    · have hcle : c ≤ α R.root := by simpa only [heq] using hc.le
      have h := R.witness_root_lower α (hα R.root).1 (hα R.root).2 hcle hab hb
      rw [heq] at h
      linarith
    · rw [R.witness_invisible α c hi hgt]
      simp only [intervalSum, sum_const_zero]
      linarith
  · have hrs : R.s < S := by omega
    have hmM : m R.s ≤ M := single_le_sum (fun r hr => Nat.zero_le (m r)) (mem_range.mpr hrs)
    have hmMR : (m R.s : ℝ) ≤ M := by exact_mod_cast hmM
    have hmul := mul_le_mul_of_nonneg_left hmMR h0
    have hbound := R.witness_small_lower α h0 hc1.le (cutEnumeration i) hb (a := a)
    dsimp [C]
    linarith

end BanachDensity1D.ProfileAux
