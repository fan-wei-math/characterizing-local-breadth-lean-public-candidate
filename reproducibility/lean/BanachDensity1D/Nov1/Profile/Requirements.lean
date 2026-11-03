import BanachDensity1D.Nov1.Profile.Cutoffs
import BanachDensity1D.Nov1.Profile.Schedule

/-! # Countable decreasing-cutoff requirements for witness stages. -/

namespace BanachDensity1D.ProfileAux
open Set

/-- A terminal history to be realized by a repeated witness block. The parameter
s is zero-based, so the manuscript's positive parameter is s+1. -/
structure Requirement (m : ℕ → ℕ) (hm : ∀ s, 0 < m s) where
  s : ℕ
  cuts : Fin (m s) → Cut
  decreasing : StrictAnti cuts
  above : ∀ r, lowerCut (cuts ⟨0, hm s⟩) (s + 1) < (cuts r : ℚ)

namespace Requirement
variable {m : ℕ → ℕ} {hm : ∀ s, 0 < m s}

def root (R : Requirement m hm) : Cut := R.cuts ⟨0, hm R.s⟩

lemma cuts_le_root (R : Requirement m hm) (r : Fin (m R.s)) : R.cuts r ≤ R.root :=
  R.decreasing.antitone (by exact Nat.zero_le r.val)

instance : Countable (Requirement m hm) := by
  let f : Requirement m hm → Σ s, Fin (m s) → Cut := fun R => ⟨R.s, R.cuts⟩
  apply Function.Injective.countable (f := f)
  intro R S h
  cases R
  cases S
  cases h
  rfl

/-- For every q and parameter there are rational histories of the prescribed length. -/
lemma exists_root (q : Cut) (s : ℕ) : ∃ R : Requirement m hm, R.s = s ∧ R.root = q := by
  let a := lowerCut q (s + 1)
  have ha0 : 0 ≤ a := lowerCut_nonneg q (s + 1)
  have haq : a < (q : ℚ) := lowerCut_lt q (s + 1)
  let δ : ℚ := ((q : ℚ) - a) / (m s + 1)
  have hden : (0 : ℚ) < m s + 1 := by positivity
  have hδ : 0 < δ := div_pos (sub_pos.mpr haq) hden
  have he : ((m s : ℚ) + 1) * δ = (q : ℚ) - a := by
    dsimp [δ]
    field_simp
  let cuts : Fin (m s) → Cut := fun r =>
    ⟨(q : ℚ) - (r.val : ℚ) * δ, by
      have hr : (r.val : ℚ) < m s := by exact_mod_cast r.isLt
      have hr0 : (0 : ℚ) ≤ r.val := Nat.cast_nonneg _
      constructor <;> nlinarith [q.property.2]⟩
  have hroot : cuts ⟨0, hm s⟩ = q := by apply Subtype.ext; simp [cuts]
  have hdec : StrictAnti cuts := by
    intro r t hrt
    change (q : ℚ) - (t.val : ℚ) * δ < (q : ℚ) - (r.val : ℚ) * δ
    have hrt' : (r.val : ℚ) < t.val := by exact_mod_cast hrt
    nlinarith
  refine ⟨⟨s, cuts, hdec, ?_⟩, rfl, hroot⟩
  intro r
  rw [hroot]
  change a < (q : ℚ) - (r.val : ℚ) * δ
  have hr : (r.val : ℚ) < m s := by exact_mod_cast r.isLt
  nlinarith

instance : Nonempty (Requirement m hm) := by
  obtain ⟨R, _⟩ := exists_root (m := m) (hm := hm) (cutEnumeration 0) 0
  exact ⟨R⟩

/-- Every terminal history is scheduled beyond every finite stage. -/
theorem schedule_exists : ∃ f : ℕ → Requirement m hm,
    ∀ R, ∀ B : ℕ, ∃ k ≥ B, f k = R := repeated_schedule _

/-- The lower label bound for the r-th base atom. -/
noncomputable def baseLower (R : Requirement m hm) (r : Fin (m R.s)) : ℚ :=
  if h : r.val + 1 < m R.s then (R.cuts ⟨r.val + 1, h⟩ : ℚ)
  else lowerCut R.root (R.s + 1)

lemma baseLower_bounds (R : Requirement m hm) (r : Fin (m R.s)) :
    0 ≤ R.baseLower r ∧ R.baseLower r < (R.cuts r : ℚ) := by
  dsimp [baseLower]
  split_ifs with h
  · refine ⟨(R.cuts ⟨r.val + 1, h⟩).property.1.le, ?_⟩
    exact R.decreasing (show r < ⟨r.val + 1, h⟩ by exact Nat.lt_succ_self _)
  · exact ⟨lowerCut_nonneg _ _, R.above r⟩

noncomputable def baseLabel (R : Requirement m hm) (r : Fin (m R.s)) : Cut :=
  betweenLabel (R.baseLower r) (R.cuts r) (R.baseLower_bounds r).1
    (R.baseLower_bounds r).2 (R.cuts r).property.2.le

lemma baseLabel_bounds (R : Requirement m hm) (r : Fin (m R.s)) :
    R.baseLower r < (R.baseLabel r : ℚ) ∧ R.baseLabel r < R.cuts r :=
  betweenLabel_spec _ _ _ _ _

lemma baseLabel_above_barrier (R : Requirement m hm) (r : Fin (m R.s)) :
    lowerCut R.root (R.s + 1) < (R.baseLabel r : ℚ) := by
  have hlow : lowerCut R.root (R.s + 1) ≤ R.baseLower r := by
    dsimp [baseLower]
    split_ifs with h
    · exact (R.above ⟨r.val + 1, h⟩).le
    · exact le_rfl
  exact lt_of_le_of_lt hlow (R.baseLabel_bounds r).1

lemma baseLabel_below_root (R : Requirement m hm) (r : Fin (m R.s)) :
    R.baseLabel r < R.root := lt_of_lt_of_le (R.baseLabel_bounds r).2 (R.cuts_le_root r)

/-- Exactly r's difference/terminal layer contains this base label. -/
lemma baseLabel_in_layer (R : Requirement m hm) (r t : Fin (m R.s)) :
    R.baseLabel r < R.cuts t ↔ t ≤ r := by
  constructor
  · intro ht
    by_contra htr
    have hrt : r < t := lt_of_not_ge htr
    have hnext : r.val + 1 < m R.s := lt_of_le_of_lt (show r.val + 1 ≤ t.val by omega) t.isLt
    have hlow : R.baseLower r = (R.cuts ⟨r.val + 1, hnext⟩ : ℚ) := by
      simp [baseLower, hnext]
    have htcut := R.decreasing.antitone (show (⟨r.val + 1, hnext⟩ : Fin (m R.s)) ≤ t from Nat.succ_le_of_lt hrt)
    have hb := (R.baseLabel_bounds r).1
    rw [hlow] at hb
    change (R.baseLabel r : ℚ) < R.cuts t at ht
    change (R.cuts t : ℚ) ≤ R.cuts ⟨r.val + 1, hnext⟩ at htcut
    linarith
  · intro htr
    exact lt_of_lt_of_le (R.baseLabel_bounds r).2 (R.decreasing.antitone htr)

end Requirement
end BanachDensity1D.ProfileAux
