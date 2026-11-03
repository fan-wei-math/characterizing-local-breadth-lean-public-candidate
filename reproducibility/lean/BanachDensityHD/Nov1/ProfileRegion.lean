import BanachDensityHD.Basic

/-! # Exact profile-region conclusion from a common top strategy and adversarial bounds.

The profile domain is [0,1]-valued, as in the manuscript. The construction
and filtered bounds are separate obligations; this file proves their logical
combination without confusing independent coordinate optima with simultaneous attainment.
-/

namespace BanachDensityHD.Nov1
open Set

/-- Achievability with coordinates indexed by the prescribed sequence. -/
def IndexedAchievable {d : ℕ} (h : ℕ → ℝ) (K : ℕ → Set (Pt d)) (β : ℕ → ℝ) : Prop :=
  ∃ G ∈ ValidGen (range K), ∀ i, Guarantees (dH h) G (K i) (β i)

/-- The ambient profile space required by the manuscript is [0,1]^N. -/
def ProfileDomain (β : ℕ → ℝ) : Prop := ∀ i, β i ∈ Icc (0 : ℝ) 1

lemma indexed_downward {d : ℕ} {h : ℕ → ℝ} {K : ℕ → Set (Pt d)}
    {α β : ℕ → ℝ} (htop : IndexedAchievable h K α) (hle : ∀ i, β i ≤ α i) :
    IndexedAchievable h K β := by
  obtain ⟨G, hG, htop⟩ := htop
  refine ⟨G, hG, ?_⟩
  intro i w hw
  exact le_trans (by exact_mod_cast hle i) (htop i w hw)

/-- The same top generator witnesses every smaller admissible profile. Coordinate
upper bounds are tested against every valid generator, not separately optimized generators. -/
lemma exact_product_of_top_and_upper {d : ℕ} {h : ℕ → ℝ}
    {K : ℕ → Set (Pt d)} {α : ℕ → ℝ}
    (htop : IndexedAchievable h K α)
    (hupper : ∀ G ∈ ValidGen (range K), ∀ i, ∃ w,
      IsFullEnumeration w (K i) ∧ deltaH h (G.outputSet w) (K i) ≤ α i) :
    ∀ β, ProfileDomain β →
      (IndexedAchievable h K β ↔ ∀ i, β i ∈ Icc (0 : ℝ) (α i)) := by
  intro β hβ
  constructor
  · rintro ⟨G, hG, hg⟩ i
    obtain ⟨w, hw, hbound⟩ := hupper G hG i
    refine ⟨(hβ i).1, ?_⟩
    have hreal : β i ≤ deltaH h (G.outputSet w) (K i) := by
      have h := hg i w hw
      change ((β i : ℝ) : EReal) ≤ ((deltaH _ (G.outputSet w) (K i) : ℝ) : EReal) at h
      exact_mod_cast h
    exact hreal.trans hbound
  · intro hle
    exact indexed_downward htop (fun i => (hle i).2)

end BanachDensityHD.Nov1
