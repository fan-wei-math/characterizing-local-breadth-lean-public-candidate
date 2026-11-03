import BanachDensityHD.Nov1.IntervalFiltered

/-! # Adversarial witnesses bound the actual filtered limit. -/

namespace BanachDensityHD.Nov1
open Set Filter
open scoped Topology

lemma intervalDensity_tendsto (h : ℕ → ℝ) (hp : ∀ n, 1 ≤ n → 0 < h n)
    (hm : MonotoneOn h (Ici 1)) (O L : Set ℤ) :
    Tendsto (intervalTestInf h O L) atTop (𝓝 (intervalDensity h O L)) := by
  have ht := (deltaH_tendsto h hp (ray 1 '' O) (ray 1 '' L)).1
  rw [ray_filtered_density_eq (by omega) h hp hm O L] at ht
  apply ht.congr'
  exact eventually_atTop.2 ⟨1, fun s hs => testInf_ray_eq (by omega) h hp hm O L (lt_of_lt_of_le zero_lt_one hs)⟩

lemma intervalTests_bddBelow (h : ℕ → ℝ) (O L : Set ℤ) (s : ℝ) :
    BddBelow (intervalTests h O L s) := by
  refine ⟨0, ?_⟩
  rintro r ⟨a, b, hab, hlevel, rfl⟩
  positivity

/-- Arbitrarily high *filtered* witness levels give an upper bound on the
filtered density, regardless of what occurs between the witness stages. -/
lemma interval_density_le_of_witnesses (h : ℕ → ℝ)
    (hp : ∀ n, 1 ≤ n → 0 < h n) (hm : MonotoneOn h (Ici 1)) (O L : Set ℤ) (α : ℝ)
    (hw : ∀ n : ℕ, ∃ a b : ℤ, 0 < (L ∩ Icc a b).ncard ∧
      (n : ℝ) * h (Icc a b).ncard ≤ (L ∩ Icc a b).ncard ∧
      (((O ∩ L) ∩ Icc a b).ncard : ℝ) ≤ α * (L ∩ Icc a b).ncard) :
    intervalDensity h O L ≤ α := by
  classical
  have hbound : ∀ s : ℝ, intervalTestInf h O L s ≤ α := by
    intro s
    obtain ⟨n, hn⟩ := exists_nat_ge s
    obtain ⟨a, b, hpos, hlevel, hcount⟩ := hw n
    obtain ⟨x, _, hlo, hup⟩ := nonempty_of_ncard_ne_zero (Nat.ne_zero_of_lt hpos)
    have hab : a ≤ b := hlo.trans hup
    have hvol : 1 ≤ (Icc a b).ncard := by
      have hnon : (Icc a b).Nonempty := ⟨a, le_rfl, hab⟩
      have hcard := (ncard_pos (finite_Icc a b)).mpr hnon
      omega
    have hlev := (mul_le_mul_of_nonneg_right hn (hp _ hvol).le).trans hlevel
    let r : ℝ := (((O ∩ L) ∩ Icc a b).ncard : ℝ) / (L ∩ Icc a b).ncard
    have hr : r ∈ intervalTests h O L s := ⟨a, b, hab, hlev, rfl⟩
    have hle : r ≤ α := (div_le_iff₀ (by exact_mod_cast hpos)).mpr hcount
    have hne : (intervalTests h O L s).Nonempty := ⟨r, hr⟩
    change (if _ then _ else _) ≤ _
    rw [ite_eq_left hne]
    exact (csInf_le (intervalTests_bddBelow h O L s) hr).trans hle
  exact le_of_tendsto (intervalDensity_tendsto h hp hm O L) (Eventually.of_forall hbound)

end BanachDensityHD.Nov1
