import BanachDensity1D.Nov1.Profile.WordStatistics

/-! # Scheduled witnesses have genuinely divergent filter levels and escape finite sets. -/

namespace BanachDensity1D.ProfileAux.Staged
open Set
variable {m : ℕ → ℕ} {hm : ∀ s, 0 < m s}

lemma witness_filter_level (α : Cut → ℝ) (hα : ∀ q, 0 ≤ α q ∧ α q ≤ 1 / 2)
    (f : ℕ → Requirement m hm) (h : ℕ → ℝ) (hh : PositiveThreshold h)
    (hscale : ∀ s : ℕ, (s + 1 : ℝ) ≤ (m s : ℝ) / h ((2 + 2 * (s + 1)) * m s)) (k : ℕ) :
    ((f k).s + 1 : ℝ) * h (witnessWindow α f k).ncard ≤
      (language (atoms α f) (f k).root ∩ witnessWindow α f k).ncard := by
  let R := f k
  have hmass : m R.s ≤ (language (atoms α f) R.root ∩ witnessWindow α f k).ncard := by
    rw [witnessWindow_mass α f k (hα R.root).1 (hα R.root).2]
    exact (points_bounds (hα R.root).1 (hα R.root).2 _).1
  have hpop := ncard_le_ncard (inter_subset_right (s := language (atoms α f) R.root))
    (witnessWindow_finite α f k)
  have hvol : 1 ≤ (witnessWindow α f k).ncard := by have := hm R.s; omega
  have hupper := witnessWindow_volume α f k
  have hD : 1 ≤ (2 + 2 * (R.s + 1)) * m R.s := by have := hm R.s; nlinarith
  have hhD := hh.1 _ hD
  have hcomp := hh.2.1 _ _ hvol hupper
  have hscaled := (le_div_iff₀ hhD).mp (hscale R.s)
  have hs : (0 : ℝ) ≤ R.s + 1 := by positivity
  have hproduct := mul_le_mul_of_nonneg_left hcomp hs
  have hmassreal : (m R.s : ℝ) ≤ (language (atoms α f) R.root ∩ witnessWindow α f k).ncard := by
    exact_mod_cast hmass
  exact hproduct.trans (hscaled.trans hmassreal)

lemma witness_far (α : Cut → ℝ) (f : ℕ → Requirement m hm) {U : Set ℤ} (hU : U.Finite) :
    ∃ B : ℕ, ∀ k ≥ B, Disjoint U (witnessWindow α f k) := by
  obtain ⟨b, hb⟩ := hU.bddAbove
  refine ⟨b.toNat + 1, ?_⟩
  intro k hk
  apply disjoint_left.mpr
  rintro x hxU hxW
  have hxb := hb hxU
  have hidx : k ≤ Blocks.offset (blocks α f) k :=
    (Blocks.offset_strictMono _ (blocks_nonempty α f)).le_apply
  have hpos := index_le_position (atoms α f) (Blocks.offset (blocks α f) k)
  have hxlo : (position (atoms α f) (Blocks.offset (blocks α f) k) : ℤ) ≤ x := hxW.1
  have hbNat := Int.self_le_toNat b
  omega

end BanachDensity1D.ProfileAux.Staged
