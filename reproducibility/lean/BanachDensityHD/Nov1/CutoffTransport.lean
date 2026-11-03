import BanachDensityHD.Trees

/-! # Geometric cutoff transport under positive constant threshold rescaling.

The tree-decoration reindexing is a correspondence argument in the report;
these lemmas check its only changed mathematical predicate in the kernel.
-/
namespace BanachDensityHD.Nov1
open Set BasicAux

lemma geomFeasible_cutoff_mono {d r : ℕ} (h : ℕ → ℝ)
    (hp : ∀ n, 1 ≤ n → 0 ≤ h n) (L : Fin (r + 1) → Set (Pt d))
    (q s t : Fin (r + 1) → ℝ) (a : ℝ) (hst : ∀ i, s i ≤ t i)
    (hf : GeomFeasible h L q s a) : GeomFeasible h L q t a := by
  intro rects hr
  apply hf rects
  intro i R hR
  obtain ⟨hdisj, hmass⟩ := hr i R hR
  exact ⟨hdisj, (mul_le_mul_of_nonneg_right (hst i) (hp _ (rect_vol_pos R))).trans hmass⟩

/-- Multiplying h by c and dividing every cutoff by c leaves every packet
test exactly the same, and hence preserves the very same game strategy. -/
lemma geomFeasible_scale {d r : ℕ} (h : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (L : Fin (r + 1) → Set (Pt d)) (q s : Fin (r + 1) → ℝ) (a : ℝ) :
    GeomFeasible (fun n => c * h n) L q (fun i => s i / c) a ↔
      GeomFeasible h L q s a := by
  have he : ∀ i n, s i / c * (c * h n) = s i * h n := by
    intro i n
    field_simp
  simp only [GeomFeasible, he]

/-- Cutoffs can always be raised to one after constant rescaling. This
avoids introducing an extra lower-bound hypothesis on a positive u. -/
lemma geomFeasible_normalized_cutoffs {d r : ℕ} (h : ℕ → ℝ)
    (hp : ∀ n, 1 ≤ n → 0 ≤ h n) (c : ℝ) (hc : 0 < c)
    (L : Fin (r + 1) → Set (Pt d)) (q s : Fin (r + 1) → ℝ) (a : ℝ)
    (hf : GeomFeasible h L q s a) :
    GeomFeasible (fun n => h n / c) L q (fun i => max 1 (c * s i)) a := by
  intro rects hr
  apply hf rects
  intro i R hR
  obtain ⟨hdisj, hm⟩ := hr i R hR
  have hcalc : c * s i * (h R.vol / c) = s i * h R.vol := by field_simp
  refine ⟨hdisj, ?_⟩
  rw [← hcalc]
  exact (mul_le_mul_of_nonneg_right (le_max_right _ _)
    (div_nonneg (hp _ (rect_vol_pos R)) hc.le)).trans hm

end BanachDensityHD.Nov1
