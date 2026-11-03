import BanachDensity1D.Nov1.Profile.Core
import BanachDensityHD.Nov1.ModelBridge
import BanachDensityHD.Nov1.ProfileRegion

/-! # The Nov. 1 exact filtered profile-realization theorem.

The reusable 1D construction supplies a common ordinary lower strategy and
filtered adversaries. A full ambient bijection extends the nonnegative coordinate
ray; hence even off-ray outputs of a competing generator are accounted for.
-/

namespace BanachDensityHD.Nov1
open Set

lemma threshold_to_oned {h : ℕ → ℝ} (hh : IsThreshold h) :
    BanachDensity1D.ProfileAux.PositiveThreshold h := by
  refine ⟨hh.1, ?_, ?_⟩
  · intro m n hm hmn
    exact hh.2.1 hm (hm.trans hmn) hmn
  · intro B
    obtain ⟨r, ⟨N, hN, rfl⟩, hr⟩ := not_bddAbove_iff.mp hh.2.2 B
    exact ⟨N, hN, hr⟩

lemma achievable_indexed {d : ℕ} (h : ℕ → ℝ) (K : ℕ → Set (Pt d))
    (β : Set (Pt d) → ℝ) :
    Achievable h (range K) β ↔ IndexedAchievable h K (fun i => β (K i)) := by
  constructor
  · rintro ⟨G, hG, hg⟩
    exact ⟨G, hG, fun i => hg (K i) (mem_range_self i)⟩
  · rintro ⟨G, hG, hg⟩
    refine ⟨G, hG, ?_⟩
    rintro L ⟨i, rfl⟩
    exact hg i

/-- The common strategy and the coordinate upper adversaries, with the actual
HD filtered density. No target-dependent choice of lower generator is made. -/
theorem profile_strategies {d : ℕ} (hd : 2 ≤ d) (h : ℕ → ℝ) (hh : IsThreshold h)
    (α : ℕ → ℝ) (hα : ∀ i, 0 ≤ α i ∧ α i ≤ 1 / 2) :
    ∃ K : ℕ → Set (Pt d), Function.Injective K ∧ LangClass (range K) ∧
      IndexedAchievable h K α ∧
      (∀ G ∈ ValidGen (range K), ∀ i, ∃ w,
        IsFullEnumeration w (K i) ∧ deltaH h (G.outputSet w) (K i) ≤ α i) := by
  classical
  obtain ⟨K, hKi, hKc, hKn, ⟨G, hGf, hGv, hGtop⟩, hupper⟩ :=
    BanachDensity1D.Nov1.profile_realization_core h (threshold_to_oned hh) α hα
  obtain ⟨e, he⟩ := ray_extension hd
  let L : ℕ → Set (Pt d) := fun i => e '' K i
  have hrange : range L = (fun M => e '' M) '' range K := indexed_image_range e K
  have hLi : Function.Injective L := by
    intro i j hij
    apply hKi
    have hp := congrArg (fun M => e.symm '' M) hij
    simpa only [L, image_inverse] using hp
  have hLc : LangClass (range L) := by
    rw [hrange]
    refine ⟨hKc.nonempty.image _, hKc.countable.image _, ?_⟩
    rintro M ⟨N, hN, rfl⟩
    exact (hKc.infinite N hN).image e.injective.injOn
  refine ⟨L, hLi, hLc, ?_, ?_⟩
  · let H := transportGenerator e G
    have hHv : H ∈ ValidGen (range L) := by
      rw [hrange]
      exact ⟨transported_fresh e ((oned_fresh_iff G).mp hGf),
        transported_valid e (oned_valid_to_hd hGv)⟩
    refine ⟨H, hHv, ?_⟩
    intro i w hw
    have hw' : BanachDensity1D.IsFullEnumeration (e.symm ∘ w) (K i) :=
      enumeration_pullback e hw
    have hlo := (hGtop i (e.symm ∘ w) hw').trans
      (ordinary_interval_le_filtered h hh.1 hh.2.1 _ _ (hKc.infinite _ (mem_range_self i)))
    have heq : deltaH h (H.outputSet w) (L i) =
        intervalDensity h (G.outputSet (e.symm ∘ w)) (K i) := by
      rw [transported_outputSet]
      exact equiv_filtered_density (by omega) e he h hh.1 hh.2.1 _ _ (hKn i)
    change ((α i : ℝ) : EReal) ≤ ((deltaH h (H.outputSet w) (L i) : ℝ) : EReal)
    exact_mod_cast (heq.symm ▸ hlo)
  · intro H hHv i
    let J := transportGenerator e.symm H
    have hJf : BanachDensity1D.Generator.Admissible J :=
      (oned_fresh_iff J).mpr (transported_fresh e.symm hHv.1)
    have hJvhd : Generator.EventuallyValidOn J (range K) := by
      have hv := transported_valid e.symm hHv.2
      rw [hrange, image_family_inverse] at hv
      exact hv
    have hJv := hd_valid_to_oned ((oned_fresh_iff J).mp hJf) hJvhd
    obtain ⟨w, hw, hW⟩ := hupper J hJf hJv i
    refine ⟨e ∘ w, enumeration_pushforward e hw, ?_⟩
    rw [pullback_outputSet]
    change deltaH h (e '' J.outputSet w) (e '' K i) ≤ α i
    rw [equiv_filtered_density (by omega) e he h hh.1 hh.2.1 _ _ (hKn i)]
    exact interval_density_le_of_witnesses h hh.1 hh.2.1 _ _ _ hW

end BanachDensityHD.Nov1

namespace BanachDensityHD
open Set Nov1

/-- **Nov. 1 `prop:profile-realization`.** For every prescribed sequence in
[0,1/2], a countable family of distinct infinite languages has exactly the
prescribed product region of lower guarantees in the ambient [0,1]-profile space.
The existential top generator precedes every coordinate and enumeration. -/
theorem prop_profile_realization {d : ℕ} (hd : 2 ≤ d) (h : ℕ → ℝ) (hh : IsThreshold h)
    (α : ℕ → ℝ) (hα : ∀ i, 0 ≤ α i ∧ α i ≤ 1 / 2) :
    ∃ K : ℕ → Set (Pt d), Function.Injective K ∧ LangClass (range K) ∧
      (∃ G ∈ ValidGen (range K), ∀ i, Guarantees (dH h) G (K i) (α i)) ∧
      (∀ β : ℕ → ℝ, ProfileDomain β →
        (IndexedAchievable h K β ↔ ∀ i, β i ∈ Icc (0 : ℝ) (α i))) ∧
      (∀ β : Set (Pt d) → ℝ, (∀ i, β (K i) ∈ Icc (0 : ℝ) 1) →
        (Achievable h (range K) β ↔ ∀ i, β (K i) ∈ Icc (0 : ℝ) (α i))) := by
  obtain ⟨K, hi, hc, htop, hup⟩ := profile_strategies hd h hh α hα
  have hexact := exact_product_of_top_and_upper htop hup
  refine ⟨K, hi, hc, htop, hexact, ?_⟩
  intro β hβ
  rw [achievable_indexed]
  exact hexact (fun i => β (K i)) hβ

end BanachDensityHD
