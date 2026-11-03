import BanachDensityHD.Nov1.IntervalBounds
import BanachDensity1D.Basic

/-! # Reuse an ordinary 1D lower guarantee for the identical filtered target.

Only the existing positive-volume filter is used; h(1) may be smaller than one.
The same output set and hence the same universally valid generator is retained.
-/

namespace BanachDensityHD.Nov1
open Set Filter
open scoped Topology

lemma ordinary_interval_le_filtered (h : ℕ → ℝ)
    (hp : ∀ n, 1 ≤ n → 0 < h n) (hm : MonotoneOn h (Ici 1))
    (O L : Set ℤ) (hL : L.Infinite) :
    BanachDensity1D.outputDensity O L ≤ intervalDensity h O L := by
  classical
  change (⨆ n : ℕ, BanachDensity1D.BasicAux.banachInf (O ∩ L) L n) ≤ _
  apply ciSup_le
  intro n
  have hh1 := hp 1 le_rfl
  have hbound : ∀ s : ℝ, (n : ℝ) / h 1 ≤ s →
      BanachDensity1D.BasicAux.banachInf (O ∩ L) L n ≤ intervalTestInf h O L s := by
    intro s hs
    have hs0 : 0 ≤ s := (div_nonneg (Nat.cast_nonneg n) hh1.le).trans hs
    change _ ≤ if (intervalTests h O L s).Nonempty then _ else _
    split_ifs with hne
    · apply le_csInf hne
      rintro r ⟨a, b, hab, hlevel, rfl⟩
      have hvol : 1 ≤ (Icc a b).ncard := by
        have hcard := (ncard_pos (finite_Icc a b)).mpr (show (Icc a b).Nonempty from ⟨a, le_rfl, hab⟩)
        omega
      have hmin : h 1 ≤ h (Icc a b).ncard := hm (by simp) hvol hvol
      have hmass : (n : ℝ) ≤ (L ∩ Icc a b).ncard := by
        calc
          _ = ((n : ℝ) / h 1) * h 1 := by field_simp
          _ ≤ s * h 1 := mul_le_mul_of_nonneg_right hs hh1.le
          _ ≤ s * h (Icc a b).ncard := mul_le_mul_of_nonneg_left hmin hs0
          _ ≤ _ := hlevel
      exact ciInf_le (BanachDensity1D.BasicAux.banachInf_bddBelow (O ∩ L) L n)
        (⟨(a, b), by exact_mod_cast hmass⟩ : {R : ℤ × ℤ // n ≤ (L ∩ Icc R.1 R.2).ncard})
    · exact BanachDensity1D.BasicAux.banachInf_le_one inter_subset_right hL n
  exact ge_of_tendsto (intervalDensity_tendsto h hp hm O L)
    (eventually_atTop.2 ⟨(n : ℝ) / h 1, hbound⟩)

end BanachDensityHD.Nov1
