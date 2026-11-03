import BanachDensity1D.Nov1.Profile.Stride

/-! # Quantitative control of interleaved local padding on arbitrary atom intervals. -/

namespace BanachDensity1D.ProfileAux
open Finset

noncomputable def paddedValue (G : ℕ) (B : ℕ → ℝ) (p : ℝ) (n : ℕ) : ℝ :=
  if n % G = 0 then B (n / G) else p

lemma padded_sum {G : ℕ} (hG : 0 < G) (B : ℕ → ℝ) (p : ℝ) (a b : ℕ) :
    intervalSum (paddedValue G B p) a b = intervalSum B (a ⌈/⌉ G) (b ⌈/⌉ G) +
      p * (((b - a : ℕ) : ℝ) - ((b ⌈/⌉ G - a ⌈/⌉ G : ℕ) : ℝ)) := by
  have hi := stride_sum hG (fun _ => (1 : ℝ)) a b
  simp only [intervalSum, sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one] at hi
  change intervalSum (fun n => if n % G = 0 then (1 : ℝ) else 0) a b = _ at hi
  calc
    _ = intervalSum (fun n => if n % G = 0 then B (n / G) else 0) a b +
        p * (((b - a : ℕ) : ℝ) -
          intervalSum (fun n => if n % G = 0 then (1 : ℝ) else 0) a b) := by
      unfold intervalSum
      rw [mul_sub, mul_sum]
      rw [show (p * ((b - a : ℕ) : ℝ)) = ∑ n ∈ Ico a b, p by simp [mul_comm]]
      rw [← sum_sub_distrib, ← sum_add_distrib]
      apply sum_congr rfl
      intro n hn
      unfold paddedValue
      split_ifs <;> ring
    _ = _ := by rw [stride_sum hG, hi]

lemma stride_count_le_length {G : ℕ} (hG : 0 < G) (a b : ℕ) :
    (b ⌈/⌉ G - a ⌈/⌉ G : ℕ) ≤ b - a := by
  have hs := stride_sum hG (fun _ => (1 : ℝ)) a b
  have hle : intervalSum (fun n => if n % G = 0 then (1 : ℝ) else 0) a b ≤ ((b - a : ℕ) : ℝ) := by
    have hh := sum_le_sum (s := Ico a b) (f := fun n => if n % G = 0 then (1 : ℝ) else 0)
      (g := fun _ => (1 : ℝ)) (fun n hn => by split_ifs <;> norm_num)
    simpa only [intervalSum, sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one] using hh
  rw [hs] at hle
  simp only [intervalSum, sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one] at hle
  exact_mod_cast hle

lemma padded_lower_count {G : ℕ} (hG : 0 < G) (B : ℕ → ℝ) {p C : ℝ}
    (hp : 0 ≤ p) (hB : ∀ r, -C ≤ B r) (a b : ℕ) :
    -C * ((b ⌈/⌉ G - a ⌈/⌉ G : ℕ) : ℝ) ≤ intervalSum (paddedValue G B p) a b := by
  rw [padded_sum hG]
  have hbase := sum_le_sum (s := Ico (a ⌈/⌉ G) (b ⌈/⌉ G)) (f := fun _ => -C)
    (g := B) (fun r hr => hB r)
  simp only [sum_const, Nat.card_Ico, nsmul_eq_mul] at hbase
  have hcount : ((b ⌈/⌉ G - a ⌈/⌉ G : ℕ) : ℝ) ≤ ((b - a : ℕ) : ℝ) := by
    exact_mod_cast stride_count_le_length hG a b
  have hpad := mul_nonneg hp (sub_nonneg.mpr hcount)
  change _ ≤ intervalSum B _ _ + _
  change _ ≤ intervalSum B _ _ at hbase
  nlinarith

/-- Enough padding per base atom gives a uniform interval loss, independent of
how many complete groups the interval crosses. -/
lemma padded_uniform_lower {G : ℕ} (hG : 0 < G) (B : ℕ → ℝ) {p C : ℝ}
    (hC : 0 ≤ C) (hp : 0 ≤ p) (hB : ∀ r, -C ≤ B r)
    (hpad : C ≤ ((G - 1 : ℕ) : ℝ) * p) {a b : ℕ} (hab : a ≤ b) :
    -C ≤ intervalSum (paddedValue G B p) a b := by
  let x := a ⌈/⌉ G
  let y := b ⌈/⌉ G
  have hxy : x ≤ y := (ceilDiv_le_iff_le_mul hG).mpr
    (hab.trans ((ceilDiv_le_iff_le_mul hG).mp (show y ≤ y from le_rfl)))
  let N := y - x
  by_cases hN : N = 0
  · have hh := padded_lower_count hG B hp hB a b
    change -C * (N : ℝ) ≤ _ at hh
    rw [hN, Nat.cast_zero, mul_zero] at hh
    linarith
  · have hNpos : 0 < N := by omega
    have hlast : G * (y - 1) < b := by
      have hy : ¬ y ≤ y - 1 := by omega
      exact lt_of_not_ge (fun h => hy ((ceilDiv_le_iff_le_mul hG).mpr h))
    have hfirst : a ≤ G * x := (ceilDiv_le_iff_le_mul hG).mp le_rfl
    have he : y - 1 = x + (N - 1) := by dsimp [N]; omega
    rw [he, Nat.mul_add] at hlast
    have hlen : G * (N - 1) + 1 ≤ b - a := by omega
    have hlenR : (G : ℝ) * ((N : ℝ) - 1) + 1 ≤ ((b - a : ℕ) : ℝ) := by
      have h := (show ((G * (N - 1) + 1 : ℕ) : ℝ) ≤ ((b - a : ℕ) : ℝ) by exact_mod_cast hlen)
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one] using h
    have hNm1 : 0 ≤ (N : ℝ) - 1 := by
      have h1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
      linarith
    have hGeq : ((G - 1 : ℕ) : ℝ) = (G : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [hGeq] at hpad
    have hlower := mul_le_mul_of_nonneg_right hpad hNm1
    have hgap : (G - 1 : ℝ) * ((N : ℝ) - 1) ≤ ((b - a : ℕ) : ℝ) - N := by linarith
    have hcontrib := mul_le_mul_of_nonneg_left hgap hp
    have hbase := sum_le_sum (s := Ico x y) (f := fun _ => -C) (g := B) (fun r hr => hB r)
    simp only [sum_const, Nat.card_Ico, nsmul_eq_mul] at hbase
    change (N : ℝ) * -C ≤ intervalSum B x y at hbase
    rw [padded_sum hG]
    change -C ≤ intervalSum B x y + p * (((b - a : ℕ) : ℝ) - N)
    nlinarith

end BanachDensity1D.ProfileAux
