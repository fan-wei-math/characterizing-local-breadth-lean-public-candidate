import BanachDensityHD.Nov1
import BanachDensity1D.Nov1.FullRange

/-! Structural b-values of the actual staged rational-cut family in Appendix B.
The B.5 heading repeats B.4's lower sign; its proof's upper conclusion is exposed
separately here. The manuscript is not edited.
-/
namespace BanachDensityHD.ExactStatements
open Set BanachDensity1D.ProfileAux

/-- B.5's upper conclusion for the specifically constructed staged family,
not for a substitute collection sharing the same optimum. -/
theorem staged_bK_upper {m : ℕ → ℕ} {hm : ∀ s, 0 < m s}
    (α : Cut → ℝ) (hα : ∀ q, 0 ≤ α q ∧ α q ≤ 1 / 2)
    (f : ℕ → Requirement m hm) (hf : ∀ R, ∀ B : ℕ, ∃ k ≥ B, f k = R)
    (h : ℕ → ℝ) (hh : PositiveThreshold h)
    (hscale : ∀ s : ℕ, (s + 1 : ℝ) ≤ (m s : ℝ) / h ((2 + 2 * (s + 1)) * m s))
    (q : Cut) :
    BanachDensity1D.bK (range (language (Staged.atoms α f)))
      (language (Staged.atoms α f) q) ≤ α q := by
  obtain ⟨G, hGa, hGv, hGd⟩ :=
    BanachDensity1D.thm_oneD_lower_conclusion (Staged.family_langClass α f hf)
  obtain ⟨w, hw, hW⟩ := Staged.filtered_upper_witnesses α hα f hf h hh hscale q G hGa hGv
  have hmono : MonotoneOn h (Ici 1) := by
    intro a ha b hb hab
    exact hh.2.1 a b ha hab
  exact (hGd _ (mem_range_self q) w hw).trans
    ((Nov1.ordinary_interval_le_filtered h hh.1 hmono _ _
      (Staged.language_infinite α f hf q)).trans
      (Nov1.interval_density_le_of_witnesses h hh.1 hmono _ _ (α q) hW))

/-- B.4/B.5 together give the exact b-value at each rational-cut target. -/
theorem staged_bK_exact {m : ℕ → ℕ} {hm : ∀ s, 0 < m s}
    (α : Cut → ℝ) (hα : ∀ q, 0 ≤ α q ∧ α q ≤ 1 / 2)
    (f : ℕ → Requirement m hm) (hf : ∀ R, ∀ B : ℕ, ∃ k ≥ B, f k = R)
    (h : ℕ → ℝ) (hh : PositiveThreshold h)
    (hscale : ∀ s : ℕ, (s + 1 : ℝ) ≤ (m s : ℝ) / h ((2 + 2 * (s + 1)) * m s))
    (q : Cut) :
    BanachDensity1D.bK (range (language (Staged.atoms α f)))
      (language (Staged.atoms α f) q) = α q := by
  apply le_antisymm (staged_bK_upper α hα f hf h hh hscale q)
  simpa only [Equiv.apply_symm_apply] using
    Staged.bK_lower α hα f hf (cutEnumeration.symm q)

end BanachDensityHD.ExactStatements
