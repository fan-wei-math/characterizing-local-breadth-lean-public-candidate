import BanachDensity1D.Nov1.Profile.Requirements

/-! # Finite positive evidence admits a proper lower rational cutoff. -/

namespace BanachDensity1D.ProfileAux
open Set

lemma finite_cut_cover (A : ℕ → Atom) {F : Set ℤ} (hF : F.Finite)
    (q : Cut) {a : ℚ} (ha0 : 0 ≤ a) (haq : a < q)
    (hsub : F ⊆ language A q) :
    ∃ p : Cut, a < (p : ℚ) ∧ p < q ∧ F ⊆ language A p := by
  induction F, hF using Set.Finite.induction_on with
  | empty =>
    let p := betweenLabel a q ha0 haq q.property.2.le
    have hp := betweenLabel_spec a q ha0 haq q.property.2.le
    exact ⟨p, hp.1, hp.2, empty_subset _⟩
  | @insert x F hx hfin ih =>
    obtain ⟨p, hap, hpq, hFp⟩ := ih (fun y hy => hsub (Or.inr hy))
    obtain ⟨n, hxn, hnq⟩ := hsub (Or.inl rfl)
    let b : ℚ := max p (A n).label
    have hb0 : 0 ≤ b := le_trans p.property.1.le (le_max_left _ _)
    have hbq : b < (q : ℚ) := max_lt hpq hnq
    let r := betweenLabel b q hb0 hbq q.property.2.le
    have hr := betweenLabel_spec b q hb0 hbq q.property.2.le
    have hpr : p < r := lt_of_le_of_lt (le_max_left _ _) hr.1
    have hnr : (A n).label < r := lt_of_le_of_lt (le_max_right _ _) hr.1
    refine ⟨r, lt_of_lt_of_le hap hpr.le, hr.2, ?_⟩
    rintro y (rfl | hy)
    · exact ⟨n, hxn, hnr⟩
    · exact language_mono A hpr.le (hFp hy)

/-- All possible next cutoffs are countable and form a nonempty rational interval. -/
abbrev ChildCut (a : ℚ) (q : Cut) := {p : Cut // a < (p : ℚ) ∧ p < q}

lemma childCut_nonempty (a : ℚ) (q : Cut) (ha0 : 0 ≤ a) (haq : a < q) :
    Nonempty (ChildCut a q) := by
  let p := betweenLabel a q ha0 haq q.property.2.le
  have hp := betweenLabel_spec a q ha0 haq q.property.2.le
  exact ⟨⟨p, hp⟩⟩

noncomputable def childCuts (a : ℚ) (q : Cut) (ha0 : 0 ≤ a) (haq : a < q) :
    ℕ → ChildCut a q := by
  letI := childCut_nonempty a q ha0 haq
  exact Classical.choose (repeated_schedule (ChildCut a q))

lemma childCuts_surjective (a : ℚ) (q : Cut) (ha0 : 0 ≤ a) (haq : a < q) :
    Function.Surjective (childCuts a q ha0 haq) := by
  intro p
  letI := childCut_nonempty a q ha0 haq
  have hr := Classical.choose_spec (repeated_schedule (ChildCut a q))
  obtain ⟨k, _, hk⟩ := hr p 0
  exact ⟨k, hk⟩

end BanachDensity1D.ProfileAux
