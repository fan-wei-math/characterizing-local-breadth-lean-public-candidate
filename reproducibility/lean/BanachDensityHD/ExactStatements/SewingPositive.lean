import BanachDensityHD.Characterization

/-! Lemma 7.11 for positive u, with the same partition independent of u. -/
namespace BanachDensityHD.ExactStatements
open Set SewingAux
open scoped Classical

theorem h_sum_le_positive {d : ℕ} (hd : 2 ≤ d) (R : Rect d) (g : ℝ → ℝ) (hg0 : ∀ x, 1 ≤ x → 0 < g x)
    (hgm : MonotoneOn g (Ici 1)) :
    ∑ a ∈ (met_finite R).toFinset, hLog g (vv R a) ≤ (12 * (d : ℝ) ^ 2 + 4 * d) * hLog g R.vol := by
  have hV : (1 : ℝ) ≤ R.vol := by exact_mod_cast BasicAux.rect_vol_pos R
  have hgV := hg0 _ hV
  have hpt : ∀ a ∈ (met_finite R).toFinset,
      hLog g (vv R a) ≤ g R.vol * Real.log (2 + (vv R a : ℝ)) := by
    intro a ha
    rw [Set.Finite.mem_toFinset] at ha
    have h1 : (1 : ℝ) ≤ vv R a := by exact_mod_cast one_le_vv ha
    have h2 : (vv R a : ℝ) ≤ R.vol := by exact_mod_cast vv_le_vol R a
    unfold hLog
    exact mul_le_mul_of_nonneg_right (hgm (mem_Ici.2 h1) (mem_Ici.2 hV) h2)
      (Real.log_nonneg (by linarith))
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum]
  calc g R.vol * ∑ a ∈ (met_finite R).toFinset, Real.log (2 + (vv R a : ℝ))
      ≤ g R.vol * ((12 * (d : ℝ) ^ 2 + 4 * d) * Real.log (2 + R.vol)) :=
        mul_le_mul_of_nonneg_left (log_sum_le hd R) (by linarith)
    _ = (12 * (d : ℝ) ^ 2 + 4 * d) * hLog g R.vol := by unfold hLog; ring

theorem sewing_positive (d : ℕ) (hd : 2 ≤ d) :
    ∃ Pb : Set (Rect d),
      (∀ C ∈ Pb, ∀ C' ∈ Pb, C ≠ C' → Disjoint C.pts C'.pts) ∧ (∀ x : Pt d, ∃ C ∈ Pb, x ∈ C.pts) ∧
      ∀ R : Rect d, {C ∈ Pb | (C.pts ∩ R.pts).Nonempty}.Finite ∧
        (∑ᶠ C ∈ {C ∈ Pb | (C.pts ∩ R.pts).Nonempty}, Real.log (2 + (C.pts ∩ R.pts).ncard)) ≤
          (12 * d ^ 2 + 4 * d) * Real.log (2 + R.vol) ∧
        ∀ g : ℝ → ℝ, (∀ x, 1 ≤ x → 0 < g x) → MonotoneOn g (Ici 1) →
          (∑ᶠ C ∈ {C ∈ Pb | (C.pts ∩ R.pts).Nonempty}, hLog g (C.pts ∩ R.pts).ncard) ≤
            (12 * d ^ 2 + 4 * d) * hLog g R.vol := by
  open SewingAux in
  refine ⟨Pb d, ?_, ?_, fun R => ⟨?_, ?_, fun g hg1 hgm => ?_⟩⟩
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hne
    rw [Set.disjoint_left]
    intro x hxa hxb
    exact hne (congrArg board (idx_unique hxa hxb))
  · intro x
    obtain ⟨a, ha⟩ := exists_board x
    exact ⟨board a, ⟨a, rfl⟩, ha⟩
  · rw [metBoards_eq]; exact (met_finite R).image _
  · rw [finsum_eq R (fun C => Real.log (2 + (C.pts ∩ R.pts).ncard))]
    exact log_sum_le hd R
  · rw [finsum_eq R (fun C => hLog g (C.pts ∩ R.pts).ncard)]
    exact h_sum_le_positive hd R g hg1 hgm


end BanachDensityHD.ExactStatements
