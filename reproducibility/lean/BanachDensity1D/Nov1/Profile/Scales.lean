import BanachDensity1D.Nov1.Profile.Words

/-! # Filter-compatible scales for the staged profile construction. -/

namespace BanachDensity1D.ProfileAux
open Set Filter

/-- The manuscript's positive monotone threshold on the positive integers. -/
def PositiveThreshold (h : ℕ → ℝ) : Prop :=
  (∀ n, 1 ≤ n → 0 < h n) ∧
  (∀ m n, 1 ≤ m → m ≤ n → h m ≤ h n) ∧
  (∀ B : ℝ, ∃ N : ℕ, 1 ≤ N ∧ B < (N : ℝ) / h N)

lemma scale_exists {h : ℕ → ℝ} (hh : PositiveThreshold h)
    (A L s : ℕ) (hA : 1 ≤ A) :
    ∃ m : ℕ, max 1 L ≤ m ∧ (s : ℝ) ≤ (m : ℝ) / h (A * m) := by
  have hh1 := hh.1 1 le_rfl
  let B : ℝ := 2 * A * (s + (max 1 L : ℕ) / h 1 + 1)
  obtain ⟨N, hN, hratio⟩ := hh.2.2 B
  have hhN := hh.1 N hN
  have hlow := hh.2.1 1 N le_rfl hN
  have hNlarge : (2 * A * max 1 L : ℕ) < N := by
    have hB : ((2 * A * max 1 L : ℕ) : ℝ) / h 1 < (N : ℝ) / h N := by
      apply lt_of_le_of_lt ?_ hratio
      dsimp [B]
      push_cast
      have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
      have hAr : (0 : ℝ) < A := by exact_mod_cast hA
      have hLr : (0 : ℝ) < max 1 L := by exact_mod_cast (show 0 < max 1 L by omega)
      field_simp
      nlinarith
    have hNh : (N : ℝ) / h N ≤ (N : ℝ) / h 1 := div_le_div_of_nonneg_left (by positivity) hh1 hlow
    have := (div_lt_div_iff_of_pos_right hh1).mp (lt_of_lt_of_le hB hNh)
    exact_mod_cast this
  let m := N / A
  have hAm : A * m ≤ N := Nat.mul_div_le N A
  have hNlt : N < A * (m + 1) := by
    have hr := Nat.mod_lt N (show 0 < A by omega)
    have he := Nat.mod_add_div N A
    dsimp [m]
    nlinarith [he, hr]
  have hmL : max 1 L ≤ m := by
    have : max 1 L * A ≤ N := by nlinarith [hA]
    exact (Nat.le_div_iff_mul_le (by omega)).mpr this
  have hm1 : 1 ≤ m := le_trans (le_max_left _ _) hmL
  have hmhalf : N ≤ 2 * A * m := by nlinarith
  have hhAm := hh.1 (A * m) (by nlinarith)
  have hhAmN := hh.2.1 (A * m) N (by nlinarith) hAm
  refine ⟨m, hmL, ?_⟩
  apply (le_div_iff₀ hhAm).mpr
  have hNs : 2 * (A : ℝ) * s < (N : ℝ) / h N := by
    apply lt_of_le_of_lt ?_ hratio
    dsimp [B]
    have hpos : 0 ≤ (max 1 L : ℕ) / h 1 := div_nonneg (by positivity) hh1.le
    have hAr : (0 : ℝ) ≤ A := Nat.cast_nonneg A
    nlinarith
  have hNs' := (lt_div_iff₀ hhN).mp hNs
  have hnreal : (N : ℝ) ≤ 2 * A * m := by exact_mod_cast hmhalf
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hmul := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hhAmN hs) (show (0 : ℝ) ≤ 2 * A by positivity)
  have hlt : 2 * (A : ℝ) * ((s : ℝ) * h (A * m)) < 2 * A * m := by
    calc
      _ ≤ 2 * (A : ℝ) * ((s : ℝ) * h N) := hmul
      _ = 2 * (A : ℝ) * s * h N := by ring
      _ < N := hNs'
      _ ≤ _ := hnreal
  exact le_of_lt ((mul_lt_mul_iff_right₀ (show (0 : ℝ) < 2 * A by positivity)).mp hlt)

end BanachDensity1D.ProfileAux
