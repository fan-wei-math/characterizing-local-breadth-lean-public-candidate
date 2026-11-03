import BanachDensity1D.Nov1.Profile.Blocks

/-! # Uniform interval losses across stages with nonnegative complete-stage surplus. -/

namespace BanachDensity1D.ProfileAux
open Finset

noncomputable def intervalSum (f : ℕ → ℝ) (a b : ℕ) : ℝ := ∑ i ∈ Ico a b, f i

lemma intervalSum_split (f : ℕ → ℝ) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    intervalSum f a b + intervalSum f b c = intervalSum f a c :=
  sum_Ico_consecutive f hab hbc

lemma intervalSum_blocks (f : ℕ → ℝ) {o : ℕ → ℕ} (ho : Monotone o)
    {k l : ℕ} (hkl : k ≤ l) :
    intervalSum f (o k) (o l) = ∑ j ∈ Ico k l, intervalSum f (o j) (o (j + 1)) := by
  induction l, hkl using Nat.le_induction with
  | base => simp [intervalSum]
  | @succ l hkl ih =>
    rw [sum_Ico_succ_top hkl]
    rw [← ih]
    exact (intervalSum_split f (ho hkl) (ho (Nat.le_succ l))).symm

noncomputable def blockOwner (o : ℕ → ℕ) (ho : StrictMono o) (n : ℕ) : ℕ :=
  Nat.find (show ∃ k, n < o (k + 1) from ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) ho.le_apply⟩)

lemma blockOwner_bounds {o : ℕ → ℕ} (ho : StrictMono o) {n : ℕ} (hn : o 0 ≤ n) :
    o (blockOwner o ho n) ≤ n ∧ n < o (blockOwner o ho n + 1) := by
  let hex : ∃ k, n < o (k + 1) := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) ho.le_apply⟩
  change o (Nat.find hex) ≤ n ∧ n < o (Nat.find hex + 1)
  refine ⟨?_, Nat.find_spec hex⟩
  by_cases hz : Nat.find hex = 0
  · simpa only [hz] using hn
  · have hprev := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    have he : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rw [he] at hprev
    omega

/-- Only the two endpoint stages can cause a loss; complete interior stages
contribute nonnegative surplus. The bound is independent of interval length. -/
lemma interval_lower_across_blocks (f : ℕ → ℝ) {o : ℕ → ℕ} (ho : StrictMono o)
    {C : ℝ} (hC : 0 ≤ C)
    (hlocal : ∀ k a b, o k ≤ a → a ≤ b → b ≤ o (k + 1) → -C ≤ intervalSum f a b)
    (hwhole : ∀ k, 0 ≤ intervalSum f (o k) (o (k + 1)))
    {a b : ℕ} (ha : o 0 ≤ a) (hab : a ≤ b) : -2 * C ≤ intervalSum f a b := by
  let k := blockOwner o ho a
  let l := blockOwner o ho b
  have hk := blockOwner_bounds ho ha
  have hl := blockOwner_bounds ho (ha.trans hab)
  change o k ≤ a ∧ a < o (k + 1) at hk
  change o l ≤ b ∧ b < o (l + 1) at hl
  have hkl : k ≤ l := by
    by_contra hnot
    have hm := ho.monotone (show l + 1 ≤ k by omega)
    omega
  by_cases he : k = l
  · have h := hlocal k a b hk.1 hab (by change b ≤ o (k + 1); rw [he]; exact hl.2.le)
    linarith
  · have hnext : k + 1 ≤ l := by omega
    have hleft := hlocal k a (o (k + 1)) hk.1 hk.2.le le_rfl
    have hright := hlocal l (o l) b le_rfl hl.1 hl.2.le
    have hmid : 0 ≤ intervalSum f (o (k + 1)) (o l) := by
      rw [intervalSum_blocks f ho.monotone hnext]
      exact sum_nonneg (fun j hj => hwhole j)
    have hsplit1 := intervalSum_split f hk.2.le (ho.monotone hnext)
    have hsplit2 := intervalSum_split f (hk.2.le.trans (ho.monotone hnext)) hl.1
    linarith

end BanachDensity1D.ProfileAux
