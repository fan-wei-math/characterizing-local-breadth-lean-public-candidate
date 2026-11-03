import BanachDensity1D

/-!
# Oct 31 manuscript notation and boundary-case bridges

These additions reuse the completed one-dimensional library. No pre-existing
statement, definition, proof, attribute or notation is changed.
-/

namespace BanachDensity1D.Oct31

open Set

/-- Oct 31 Definition 1.3 for `d = 1`: count only points in both the
output set and the target, without requiring `A ⊆ B` as an input premise. -/
noncomputable def relativeBanach (A B : Set ℤ) : ℝ :=
  ⨆ n : ℕ, ⨅ R : {R : ℤ × ℤ // n ≤ (B ∩ Icc R.1 R.2).ncard},
    ((A ∩ B ∩ Icc R.1.1 R.1.2).ncard : ℝ) / (B ∩ Icc R.1.1 R.1.2).ncard

/-- The current manuscript numerator is exactly the existing output-density
convention. Infinite-target convergence and bounds are already proved by
`BasicAux.outputDensity_tendsto`. -/
theorem relativeBanach_eq_outputDensity (A B : Set ℤ) :
    relativeBanach A B = outputDensity A B := rfl

/-- Oct 31 Corollary 1.6 with no nonemptiness premise. For a nonempty class
this is the existing pointwise finite-rank corollary; for the empty class the
existing admissible `fresh` generator handles the vacuous requirements.
The rank bound may depend on the language. -/
theorem finite_point_rank_all {X : Set (Set ℤ)} (hcount : X.Countable)
    (hinf : ∀ L ∈ X, L.Infinite) (hrank : ∀ L ∈ X, ∃ r, CBrank X L r) :
    (∃ G : Generator, G.Admissible ∧ G.EventuallyValidOn X ∧
      ∀ K ∈ X, ∀ w, IsFullEnumeration w K →
        1 / 2 ≤ outputDensity (G.outputSet w) K) ∧
    (∀ G : Generator, G.Admissible → G.EventuallyValidOn X →
      ∀ K ∈ X, ∃ w, IsFullEnumeration w K ∧
        outputDensity (G.outputSet w) K ≤ 1 / 2) := by
  classical
  by_cases hne : X.Nonempty
  · exact cor_intro_one_dimensional_rank ⟨hne, hcount, hinf⟩ hrank
  · have hX : X = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst X
    refine ⟨⟨fresh, fresh_admissible, ?_, ?_⟩, ?_⟩
    · intro K hK
      simp at hK
    · intro K hK
      simp at hK
    · intro G hGa hG K hK
      simp at hK

end BanachDensity1D.Oct31
