import BanachDensity1D.Nov1.Profile.LayerScores
import BanachDensity1D.Nov1.Profile.FilteredWindows
import BanachDensity1D.Nov1.Profile.TreeRequirements
import BanachDensity1D.Nov1.Profile.FilteredAdversary

/-! # Filtered adversarial upper witnesses for the actual staged family. -/

namespace BanachDensity1D.ProfileAux.Staged
open Set
variable {m : ℕ → ℕ} {hm : ∀ s, 0 < m s}

lemma witnessWindow_eq_Icc (α : Cut → ℝ) (f : ℕ → Requirement m hm) (k : ℕ) :
    witnessWindow α f k = Icc
      (position (atoms α f) (Blocks.offset (blocks α f) k) : ℤ)
      ((position (atoms α f) (Blocks.offset (blocks α f) k + ((f k).witness α).length) : ℤ) - 1) := by
  ext x
  simp only [witnessWindow, mem_Ico, mem_Icc]
  omega

lemma upper_tree_future (α : Cut → ℝ) (hα : ∀ q, 0 ≤ α q ∧ α q ≤ 1 / 2)
    (f : ℕ → Requirement m hm) (hf : ∀ R, ∀ B : ℕ, ∃ k ≥ B, f k = R)
    (h : ℕ → ℝ) (hh : PositiveThreshold h)
    (hscale : ∀ s : ℕ, (s + 1 : ℝ) ≤ (m s : ℝ) / h ((2 + 2 * (s + 1)) * m s))
    (q : Cut) (s : ℕ) :
    FilteredRace.Future (language (atoms α f) q) (FilterWindow h (language (atoms α f) q) s (α q)) []
      (cutTree (atoms α f) (lowerCut q (s + 1)) (lowerCut_nonneg q (s + 1))
        (m s - 1) q (lowerCut_lt q (s + 1))) := by
  intro P hP U hU
  obtain ⟨R, hrs, hroot, hP⟩ := path_requirement hm (atoms α f) q s hP
  obtain ⟨B, hB⟩ := witness_far α f hU
  obtain ⟨k, hk, hfk⟩ := hf R B
  let a : ℤ := position (atoms α f) (Blocks.offset (blocks α f) k)
  let b : ℤ := (position (atoms α f) (Blocks.offset (blocks α f) k + ((f k).witness α).length) : ℤ) - 1
  have heW : witnessWindow α f k = Icc a b := witnessWindow_eq_Icc α f k
  have hmass := witnessWindow_mass α f k (hα (f k).root).1 (hα (f k).root).2
  have hpos : 0 < (language (atoms α f) q ∩ witnessWindow α f k).ncard := by
    have hp : 0 < (language (atoms α f) (f k).root ∩ witnessWindow α f k).ncard := by
      rw [hmass]
      exact lt_of_lt_of_le (hm (f k).s) (points_bounds (hα (f k).root).1 (hα (f k).root).2 _).1
    simpa only [hfk, hroot] using hp
  have hlevel := witness_filter_level α hα f h hh hscale k
  have hscore := witness_score_upper α f k (hα (f k).root).1 (hα (f k).root).2
  rw [hfk, hroot, ← hP] at hscore
  have hWpos : 1 ≤ (witnessWindow α f k).ncard := by
    have hle := ncard_le_ncard (inter_subset_right (s := language (atoms α f) q)) (witnessWindow_finite α f k)
    omega
  have hlev : (s : ℝ) * h (witnessWindow α f k).ncard ≤
      (language (atoms α f) q ∩ witnessWindow α f k).ncard := by
    calc
      _ ≤ (s + 1 : ℝ) * h (witnessWindow α f k).ncard :=
        mul_le_mul_of_nonneg_right (by linarith) (hh.1 _ hWpos).le
      _ ≤ _ := by simpa only [hfk, hrs, hroot] using hlevel
  refine ⟨a, b, ?_, ?_⟩
  · exact ⟨by simpa only [heW] using hpos, by simpa only [heW] using hlev,
      by simpa only [List.nil_append, heW] using hscore⟩
  · have hd := (hB k hk).mono_right (inter_subset_right (s := language (atoms α f) q))
    simpa only [heW] using hd

/-- For each target and every valid competing generator, the construction
supplies a full enumeration with permanently sealed witnesses at every h-level. -/
theorem filtered_upper_witnesses (α : Cut → ℝ) (hα : ∀ q, 0 ≤ α q ∧ α q ≤ 1 / 2)
    (f : ℕ → Requirement m hm) (hf : ∀ R, ∀ B : ℕ, ∃ k ≥ B, f k = R)
    (h : ℕ → ℝ) (hh : PositiveThreshold h)
    (hscale : ∀ s : ℕ, (s + 1 : ℝ) ≤ (m s : ℝ) / h ((2 + 2 * (s + 1)) * m s))
    (q : Cut) (G : Generator) (hGa : G.Admissible)
    (hG : G.EventuallyValidOn (range (language (atoms α f)))) :
    ∃ w, IsFullEnumeration w (language (atoms α f) q) ∧ ∀ s : ℕ, ∃ a b : ℤ,
      0 < (language (atoms α f) q ∩ Icc a b).ncard ∧
      (s : ℝ) * h (Icc a b).ncard ≤ (language (atoms α f) q ∩ Icc a b).ncard ∧
      (((G.outputSet w ∩ language (atoms α f) q) ∩ Icc a b).ncard : ℝ) ≤
        α q * (language (atoms α f) q ∩ Icc a b).ncard := by
  apply adversarial_filtered_witnesses (family_langClass α f hf) (mem_range_self q) h (α q) ?_ G hGa hG
  intro s
  refine ⟨cutTree (atoms α f) (lowerCut q (s + 1)) (lowerCut_nonneg q (s + 1))
    (m s - 1) q (lowerCut_lt q (s + 1)), ?_, upper_tree_future α hα f hf h hh hscale q s⟩
  exact cutTree_admissible (atoms α f) (fun p q hpq => language_proper α f hf hpq)
    _ _ _ _ _

end BanachDensity1D.ProfileAux.Staged
