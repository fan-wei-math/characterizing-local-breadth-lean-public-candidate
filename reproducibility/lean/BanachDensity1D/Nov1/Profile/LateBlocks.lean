import BanachDensity1D.Nov1.Profile.BlockSums

/-! # Finite initial stages cannot destroy a uniform interval-surplus bound. -/

namespace BanachDensity1D.ProfileAux
open Finset

lemma intervalSum_prefix_bound (f : ℕ → ℝ) (N : ℕ) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ N) :
    -(∑ i ∈ range N, |f i|) ≤ intervalSum f a b := by
  have hsub : Ico a b ⊆ range N := by intro i hi; have := (mem_Ico.mp hi).2; simp; omega
  have habs : (∑ i ∈ Ico a b, |f i|) ≤ ∑ i ∈ range N, |f i| :=
    sum_le_sum_of_subset_of_nonneg hsub (fun i hi hni => abs_nonneg (f i))
  have hlow : -(∑ i ∈ Ico a b, |f i|) ≤ intervalSum f a b := by
    rw [← sum_neg_distrib]
    exact sum_le_sum (fun i hi => neg_abs_le (f i))
  linarith

/-- Nonnegative complete stages are needed only eventually; the finite initial
prefix contributes a fixed constant, independent of the later interval. -/
lemma eventual_block_surplus (f : ℕ → ℝ) {o : ℕ → ℕ} (ho : StrictMono o)
    (hzero : o 0 = 0) {C : ℝ} (hC : 0 ≤ C)
    (hlocal : ∀ k a b, o k ≤ a → a ≤ b → b ≤ o (k + 1) → -C ≤ intervalSum f a b)
    (K : ℕ) (hwhole : ∀ k ≥ K, 0 ≤ intervalSum f (o k) (o (k + 1))) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ a b : ℕ, a ≤ b → -D ≤ intervalSum f a b := by
  let D0 := ∑ i ∈ range (o K), |f i|
  have hD0 : 0 ≤ D0 := sum_nonneg (fun i hi => abs_nonneg (f i))
  have hlate {a b : ℕ} (ha : o K ≤ a) (hab : a ≤ b) : -2 * C ≤ intervalSum f a b := by
    let o' : ℕ → ℕ := fun n => o (n + K)
    have ho' : StrictMono o' := fun i j hij => ho (Nat.add_lt_add_right hij K)
    apply interval_lower_across_blocks f ho' hC
      (fun k a b hk hab hb => hlocal (k + K) a b hk hab (by simpa only [o', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb))
      (fun k => by simpa only [o', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwhole (k + K) (by omega))
      (by simpa only [o', Nat.zero_add] using ha) hab
  refine ⟨D0 + 2 * C, by linarith, ?_⟩
  intro a b hab
  by_cases ha : o K ≤ a
  · have h := hlate ha hab
    linarith
  · by_cases hb : b ≤ o K
    · have h := intervalSum_prefix_bound f (o K) hab hb
      change -D0 ≤ _ at h
      linarith
    · have hleft := intervalSum_prefix_bound f (o K) (a := a) (b := o K) (by omega) le_rfl
      have hright := hlate (a := o K) le_rfl (show o K ≤ b by omega)
      have he := intervalSum_split f (show a ≤ o K by omega) (show o K ≤ b by omega)
      change -D0 ≤ _ at hleft
      linarith

end BanachDensity1D.ProfileAux
