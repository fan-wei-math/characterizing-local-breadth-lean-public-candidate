import BanachDensityHD.Nov1.ThresholdTransport

/-! # The positive-u threshold normalization appearing in the Nov. 1 delta.

This proves equality of density/achievability notions. Transport of structural
tree certificates is a separate obligation when claiming a literal structural equivalence.
-/

namespace BanachDensityHD.Nov1
open Set

/-- Normalize a positive nondecreasing u by a single positive constant, without
altering any existing characterization declaration or any density guarantee. -/
theorem positive_log_normalization (u : ℝ → ℝ)
    (hu : ∀ x, 1 ≤ x → 0 < u x) (hum : MonotoneOn u (Ici 1)) :
    ∃ g : ℝ → ℝ, (∀ x, 1 ≤ x → 1 ≤ g x) ∧ MonotoneOn g (Ici 1) ∧
      ∀ (d : ℕ) (O L : Set (Pt d)), deltaH (hLog u) O L = deltaH (hLog g) O L := by
  let c : ℝ := min 1 (u 1)
  have hc : 0 < c := lt_min one_pos (hu 1 le_rfl)
  have hc1 : c ≤ u 1 := min_le_right _ _
  let g : ℝ → ℝ := fun x => u x / c
  have hg : ∀ x, 1 ≤ x → 1 ≤ g x := by
    intro x hx
    apply (one_le_div hc).mpr
    exact hc1.trans (hum (by simp) hx hx)
  have hgm : MonotoneOn g (Ici 1) := by
    intro x hx y hy hxy
    exact div_le_div_of_nonneg_right (hum hx hy hxy) hc.le
  refine ⟨g, hg, hgm, ?_⟩
  intro d O L
  have hpos : ∀ n, 1 ≤ n → 0 < hLog g n := by
    intro n hn
    apply mul_pos (lt_of_lt_of_le zero_lt_one (hg n (by exact_mod_cast hn)))
    apply Real.log_pos
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have he : (fun v => c * hLog g v) = hLog u := by
    funext v
    dsimp [hLog, g]
    field_simp
  rw [← he]
  exact deltaH_scale (hLog g) hpos O L hc

lemma achievable_of_density_eq {d : ℕ} (h g : ℕ → ℝ)
    (he : ∀ O L : Set (Pt d), deltaH h O L = deltaH g O L)
    (X : Set (Set (Pt d))) (α : Set (Pt d) → ℝ) :
    Achievable h X α ↔ Achievable g X α := by
  have hd : @dH d h = dH g := by
    funext O L
    exact congrArg (fun r : ℝ => (r : EReal)) (he O L)
  simp only [Achievable, hd]

end BanachDensityHD.Nov1
