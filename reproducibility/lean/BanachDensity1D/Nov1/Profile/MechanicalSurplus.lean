import BanachDensity1D.Nov1.Profile.Words
import BanachDensity1D.Nov1.Profile.Stride

/-! # Uniform alpha-surplus of every consecutive block of mechanical base atoms. -/

namespace BanachDensity1D.ProfileAux
open Finset

open Classical in
noncomputable def mechanicalSurplus (α c : ℝ) (r : ℕ) : ℝ :=
  if isPair α r then 1 - 2 * c else -c

lemma mechanical_surplus_lower {α c : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2)
    (hc : c ≤ α) {a b : ℕ} (hab : a ≤ b) :
    -1 < intervalSum (mechanicalSurplus α c) a b := by
  classical
  let p := ((Ico a b).filter (isPair α)).card
  have hlocal := local_surplus hα0 hα1 hab
  change -1 < (p : ℝ) - α * ((b : ℝ) - a + p) at hlocal
  have he : intervalSum (mechanicalSurplus α c) a b =
      (p : ℝ) - c * ((b : ℝ) - a + p) := by
    have hterm (r : ℕ) : mechanicalSurplus α c r =
        (if isPair α r then (1 : ℝ) else 0) - c * (1 + if isPair α r then (1 : ℝ) else 0) := by
      unfold mechanicalSurplus
      split_ifs <;> ring
    unfold intervalSum
    simp_rw [hterm]
    rw [sum_sub_distrib, ← mul_sum, sum_add_distrib]
    simp only [sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one, sum_boole]
    rw [Nat.cast_sub hab]
  have hlen : 0 ≤ (b : ℝ) - a + p := by
    have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
    have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg _
    linarith
  have hprod := mul_nonneg (sub_nonneg.mpr hc) hlen
  rw [he]
  nlinarith

lemma mechanical_stride_lower {α c : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2)
    (hc : c ≤ α) {G : ℕ} (hG : 0 < G) {a b : ℕ} (hab : a ≤ b) :
    -1 < intervalSum (fun n => if n % G = 0 then mechanicalSurplus α c (n / G) else 0) a b := by
  rw [stride_sum hG]
  have hceil : a ⌈/⌉ G ≤ b ⌈/⌉ G := (ceilDiv_le_iff_le_mul hG).mpr
    (hab.trans ((ceilDiv_le_iff_le_mul hG).mp le_rfl))
  exact mechanical_surplus_lower hα0 hα1 hc hceil

end BanachDensity1D.ProfileAux
