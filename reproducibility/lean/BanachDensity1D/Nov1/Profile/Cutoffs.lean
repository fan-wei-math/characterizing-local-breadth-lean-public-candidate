import BanachDensity1D.Nov1.Profile.Atoms

/-! # Finite rational cutoff barriers in the staged profile construction. -/

namespace BanachDensity1D.ProfileAux
open Set

noncomputable def lowerCandidates (q : Cut) (s : ℕ) : Finset ℚ :=
  insert 0 ((Finset.range s).image fun j => if (cutEnumeration j : ℚ) < q then
    (cutEnumeration j : ℚ) else 0)

noncomputable def upperCandidates (q : Cut) (s : ℕ) : Finset ℚ :=
  insert 1 ((Finset.range s).image fun j => if (q : ℚ) < cutEnumeration j then
    (cutEnumeration j : ℚ) else 1)

noncomputable def lowerCut (q : Cut) (s : ℕ) : ℚ :=
  (lowerCandidates q s).max' ⟨0, by simp [lowerCandidates]⟩
noncomputable def upperCut (q : Cut) (s : ℕ) : ℚ :=
  (upperCandidates q s).min' ⟨1, by simp [upperCandidates]⟩

lemma lowerCut_nonneg (q : Cut) (s : ℕ) : 0 ≤ lowerCut q s :=
  Finset.le_max' _ 0 (by simp [lowerCandidates])

lemma lowerCut_lt (q : Cut) (s : ℕ) : lowerCut q s < (q : ℚ) := by
  classical
  apply (Finset.max'_lt_iff _ _).mpr
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact q.property.1
  · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    split_ifs with hj
    · exact hj
    · exact q.property.1

lemma le_lowerCut (q : Cut) {s i : ℕ} (hi : i < s) (hiq : (cutEnumeration i : ℚ) < q) :
    (cutEnumeration i : ℚ) ≤ lowerCut q s := by
  classical
  apply Finset.le_max'
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, by simp [hiq]⟩

lemma upperCut_le_one (q : Cut) (s : ℕ) : upperCut q s ≤ 1 :=
  Finset.min'_le _ 1 (by simp [upperCandidates])

lemma lt_upperCut (q : Cut) (s : ℕ) : (q : ℚ) < upperCut q s := by
  classical
  apply (Finset.lt_min'_iff _ _).mpr
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact q.property.2
  · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    split_ifs with hj
    · exact hj
    · exact q.property.2

lemma upperCut_le (q : Cut) {s i : ℕ} (hi : i < s) (hiq : (q : ℚ) < cutEnumeration i) :
    upperCut q s ≤ (cutEnumeration i : ℚ) := by
  classical
  apply Finset.min'_le
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, by simp [hiq]⟩

/-- Rational density, made explicit by a midpoint within the open unit interval. -/
def betweenLabel (a b : ℚ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) : Cut :=
  ⟨(a + b) / 2, by constructor <;> linarith⟩

lemma betweenLabel_spec (a b : ℚ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    a < (betweenLabel a b ha hab hb : ℚ) ∧
      (betweenLabel a b ha hab hb : ℚ) < b := by
  dsimp [betweenLabel]
  constructor <;> linarith

/-- Local padding belongs to the previously listed larger languages only. -/
noncomputable def paddingLabel (q : Cut) (s : ℕ) : Cut :=
  betweenLabel q (upperCut q s) q.property.1.le (lt_upperCut q s) (upperCut_le_one q s)

lemma padding_above (q : Cut) (s : ℕ) : q < paddingLabel q s :=
  (betweenLabel_spec _ _ _ _ _).1

lemma padding_below (q : Cut) {s i : ℕ} (hi : i < s) (hiq : q < cutEnumeration i) :
    paddingLabel q s < cutEnumeration i := by
  change (paddingLabel q s : ℚ) < (cutEnumeration i : ℚ)
  have hbelow : (paddingLabel q s : ℚ) < upperCut q s :=
    (betweenLabel_spec q (upperCut q s) q.property.1.le (lt_upperCut q s) (upperCut_le_one q s)).2
  exact lt_of_lt_of_le hbelow (upperCut_le q hi hiq)

noncomputable def firstCutoffs (k : ℕ) : Finset ℚ :=
  insert 1 ((Finset.range k).image fun i => (cutEnumeration i : ℚ))
noncomputable def firstMinimum (k : ℕ) : ℚ :=
  (firstCutoffs k).min' ⟨1, by simp [firstCutoffs]⟩

lemma firstMinimum_pos (k : ℕ) : 0 < firstMinimum k := by
  classical
  apply (Finset.lt_min'_iff _ _).mpr
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · norm_num
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact (cutEnumeration i).property.1

lemma firstMinimum_le_one (k : ℕ) : firstMinimum k ≤ 1 :=
  Finset.min'_le _ 1 (by simp [firstCutoffs])

noncomputable def endLabel (k : ℕ) : Cut :=
  betweenLabel 0 (firstMinimum k) le_rfl (firstMinimum_pos k) (firstMinimum_le_one k)

lemma endLabel_below {k i : ℕ} (hi : i < k) : endLabel k < cutEnumeration i := by
  change (endLabel k : ℚ) < (cutEnumeration i : ℚ)
  classical
  have hmin : firstMinimum k ≤ (cutEnumeration i : ℚ) := by
    apply Finset.min'_le
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩
  exact lt_of_lt_of_le
    (betweenLabel_spec 0 (firstMinimum k) le_rfl (firstMinimum_pos k) (firstMinimum_le_one k)).2 hmin

end BanachDensity1D.ProfileAux
