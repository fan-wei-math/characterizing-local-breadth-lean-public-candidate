import BanachDensity1D.Nov1.Profile.BlockSums

/-! # Exact sums of base-atom contributions interleaved with zero padding. -/

namespace BanachDensity1D.ProfileAux
open Finset

lemma stride_mem_iff {G : ℕ} (hG : 0 < G) (a b r : ℕ) :
    r ∈ Ico (a ⌈/⌉ G) (b ⌈/⌉ G) ↔ G * r ∈ Ico a b := by
  simp only [mem_Ico, ceilDiv_le_iff_le_mul hG]
  have hlt : r < b ⌈/⌉ G ↔ G * r < b := by
    simpa only [not_le] using not_congr (ceilDiv_le_iff_le_mul (b := b) (c := r) hG)
  rw [hlt]

lemma stride_sum {G : ℕ} (hG : 0 < G) (B : ℕ → ℝ) (a b : ℕ) :
    intervalSum (fun n => if n % G = 0 then B (n / G) else 0) a b =
      intervalSum B (a ⌈/⌉ G) (b ⌈/⌉ G) := by
  classical
  unfold intervalSum
  rw [← sum_filter]
  have hmul {n : ℕ} (hn : n % G = 0) : G * (n / G) = n := by
    have he := Nat.mod_add_div n G
    omega
  refine sum_bij (fun n hn => n / G) ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hnI, hnmod⟩ := mem_filter.mp hn
    exact (stride_mem_iff hG a b (n / G)).mpr (by simpa only [hmul hnmod] using hnI)
  · intro n hn m hm he
    have hnmod := (mem_filter.mp hn).2
    have hmmod := (mem_filter.mp hm).2
    rw [← hmul hnmod, ← hmul hmmod, he]
  · intro r hr
    refine ⟨G * r, mem_filter.mpr ⟨(stride_mem_iff hG a b r).mp hr, by simp⟩, ?_⟩
    exact Nat.mul_div_cancel_left r hG
  · intro n hn
    rfl

end BanachDensity1D.ProfileAux
