import BanachDensity1D.Nov1.Profile.LowerConstruction
import BanachDensity1D.Nov1.Profile.UpperConstruction

/-! # Reusable one-dimensional core of Nov. 1 profile realization.

This packages the actual construction, one simultaneous ordinary-density lower
strategy and filtered adversarial witnesses. The manuscript-facing Z^d product
statement is exported by the HD ray-transport module.
-/

namespace BanachDensity1D.Nov1
open Set ProfileAux

/-- The one-dimensional construction behind `prop:profile-realization` for an
arbitrary prescribed sequence and arbitrary positive monotone unbounded-ratio h.
Indices are zero-based in Lean: index i corresponds to manuscript i+1. -/
theorem profile_realization_core (h : ℕ → ℝ) (hh : PositiveThreshold h)
    (α : ℕ → ℝ) (hα : ∀ i, 0 ≤ α i ∧ α i ≤ 1 / 2) :
    ∃ K : ℕ → Set ℤ, Function.Injective K ∧ LangClass (range K) ∧
      (∀ i, K i ⊆ Ici (0 : ℤ)) ∧
      (∃ G : Generator, G.Admissible ∧ G.EventuallyValidOn (range K) ∧
        ∀ i : ℕ, ∀ w, IsFullEnumeration w (K i) → α i ≤ outputDensity (G.outputSet w) (K i)) ∧
      (∀ G : Generator, G.Admissible → G.EventuallyValidOn (range K) → ∀ i : ℕ,
        ∃ w, IsFullEnumeration w (K i) ∧ ∀ s : ℕ, ∃ a b : ℤ,
          0 < (K i ∩ Icc a b).ncard ∧
          (s : ℝ) * h (Icc a b).ncard ≤ (K i ∩ Icc a b).ncard ∧
          (((G.outputSet w ∩ K i) ∩ Icc a b).ncard : ℝ) ≤ α i * (K i ∩ Icc a b).ncard) := by
  classical
  obtain ⟨m, hmMono, hmLower, hmScale⟩ := increasing_scales hh
  have hm : ∀ s, 0 < m s := fun s => (Nat.zero_lt_succ s).trans_le (hmLower s)
  obtain ⟨f, hf⟩ := Requirement.schedule_exists (m := m) (hm := hm)
  let a : Cut → ℝ := fun q => α (cutEnumeration.symm q)
  have ha : ∀ q, 0 ≤ a q ∧ a q ≤ 1 / 2 := fun q => hα _
  let A := Staged.atoms a f
  let K : ℕ → Set ℤ := fun i => language A (cutEnumeration i)
  have hKr : range K = range (language A) := by
    ext L
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨cutEnumeration i, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨cutEnumeration.symm q, by simp [K]⟩
  have hclass : LangClass (range K) := by
    rw [hKr]
    exact Staged.family_langClass a f hf
  have hinj : Function.Injective K := (Staged.language_injective a f hf).comp cutEnumeration.injective
  refine ⟨K, hinj, hclass, fun i => language_nonneg A _, ?_, ?_⟩
  · obtain ⟨G, hGa, hGv, hGd⟩ := Staged.common_ordinary_generator a ha f hf
    refine ⟨G, hGa, by rwa [hKr], ?_⟩
    intro i w hw
    simpa only [a, Equiv.symm_apply_apply] using hGd i w hw
  · intro G hGa hGv i
    have hGv' : G.EventuallyValidOn (range (language A)) := hKr ▸ hGv
    obtain ⟨w, hw, hW⟩ := Staged.filtered_upper_witnesses a ha f hf h hh hmScale (cutEnumeration i) G hGa hGv'
    refine ⟨w, hw, ?_⟩
    simpa only [a, Equiv.symm_apply_apply] using hW

end BanachDensity1D.Nov1
