import BanachDensityHD.TreeCorrespondence.ProofRoute
import BanachDensityHD.Nov1

namespace BanachDensityHD.ExactStatements
open Set TreeCorrespondence
open scoped Classical

namespace OccurrenceTree
variable {c : ℝ}
/-- Change only cutoffs on the same original occurrence tree. -/
def cutoffMap {ι : Type} {d : ℕ} (T : TreeCorrespondence.OccurrenceTree ι d)
    (f : ℝ → ℝ) : TreeCorrespondence.OccurrenceTree ι d :=
  { T with cutoff := fun p => f (T.cutoff p) }

theorem normalized {ι : Type} {d : ℕ} (T : TreeCorrespondence.OccurrenceTree ι d)
    {X : Set (Set (Pt d))} {h : ℕ → ℝ} {q : Set (Pt d) → ℝ} {K : Set (Pt d)}
    (hc : 0 < c) (hp : ∀ n, 1 ≤ n → 0 ≤ h n) (ht : T.Protected X h q K) :
    (cutoffMap T (fun s => max 1 (c * s))).Protected X (fun n => h n / c) q K := by
  obtain ⟨hr, hv, he, hch, hf⟩ := ht
  refine ⟨hr, ?_, he, hch, ?_⟩
  · intro p hp
    exact ⟨(hv p hp).1, (hv p hp).2.1, le_max_left _ _, (hv p hp).2.2.2⟩
  · intro p hpath
    exact Nov1.geomFeasible_normalized_cutoffs h hp c hc _ _ _ _ (hf p hpath)

theorem unnormalized {ι : Type} {d : ℕ} (T : TreeCorrespondence.OccurrenceTree ι d)
    {X : Set (Set (Pt d))} {h : ℕ → ℝ} {q : Set (Pt d) → ℝ} {K : Set (Pt d)}
    (hc : 0 < c) (hc1 : c ≤ 1) (ht : T.Protected X (fun n => h n / c) q K) :
    (cutoffMap T (fun s => s / c)).Protected X h q K := by
  obtain ⟨hr, hv, he, hch, hf⟩ := ht
  refine ⟨hr, ?_, he, hch, ?_⟩
  · intro p hp
    exact ⟨(hv p hp).1, (hv p hp).2.1,
      (one_le_div hc).2 (hc1.trans (hv p hp).2.2.1), (hv p hp).2.2.2⟩
  · intro p hp
    have hs := (Nov1.geomFeasible_scale (fun n => h n / c) c hc
      (TreeCorrespondence.OccurrenceTree.along T.language p) (fun i => q (TreeCorrespondence.OccurrenceTree.along T.language p i))
      (TreeCorrespondence.OccurrenceTree.along T.cutoff p) (T.radius p)).2 (hf p hp)
    have heq : (fun n => c * (h n / c)) = h := by funext n; field_simp
    rw [heq] at hs
    exact hs
end OccurrenceTree

/-- Complete tree-existence equivalence, including roots, prefixes, countability,
all required children, increasing radii and every finite path game. -/
theorem protected_normalization {d : ℕ} (X : Set (Set (Pt d))) (h : ℕ → ℝ)
    (q : Set (Pt d) → ℝ) (K : Set (Pt d)) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (hp : ∀ n, 1 ≤ n → 0 ≤ h n) :
    (∃ T, IsProtectedTree X h q K T) ↔
    ∃ T, IsProtectedTree X (fun n => h n / c) q K T := by
  rw [← paperProtectedTree_iff, ← paperProtectedTree_iff]
  constructor
  · rintro ⟨ι, T, ht⟩
    exact ⟨ι, OccurrenceTree.cutoffMap T _, OccurrenceTree.normalized T hc hp ht⟩
  · rintro ⟨ι, T, ht⟩
    exact ⟨ι, OccurrenceTree.cutoffMap T _, OccurrenceTree.unnormalized T hc hc1 ht⟩

/-- A normalization with the exact threshold identity needed for complete
certificate transport, rather than only scalar density equality. -/
theorem normalization_data (u : ℝ → ℝ)
    (hu : ∀ x, 1 ≤ x → 0 < u x) (hum : MonotoneOn u (Ici 1)) :
    ∃ (c : ℝ) (g : ℝ → ℝ), 0 < c ∧ c ≤ 1 ∧
      (∀ x, 1 ≤ x → 1 ≤ g x) ∧ MonotoneOn g (Ici 1) ∧
      hLog g = (fun n => hLog u n / c) ∧
      ∀ (d : ℕ) (O L : Set (Pt d)), deltaH (hLog u) O L = deltaH (hLog g) O L := by
  let c : ℝ := min 1 (u 1)
  have hc : 0 < c := lt_min one_pos (hu 1 le_rfl)
  let g : ℝ → ℝ := fun x => u x / c
  have hg : ∀ x, 1 ≤ x → 1 ≤ g x := by
    intro x hx
    exact (one_le_div hc).2 ((min_le_right _ _).trans (hum (by simp) hx hx))
  have hgm : MonotoneOn g (Ici 1) := by
    intro x hx y hy hxy
    exact div_le_div_of_nonneg_right (hum hx hy hxy) hc.le
  have he : hLog g = (fun n => hLog u n / c) := by
    funext n; dsimp [hLog, g]; ring
  refine ⟨c, g, hc, min_le_left _ _, hg, hgm, he, ?_⟩
  intro d O L
  have hp : ∀ n, 1 ≤ n → 0 < hLog g n := by
    intro n hn
    apply mul_pos (lt_of_lt_of_le zero_lt_one (hg n (by exact_mod_cast hn)))
    apply Real.log_pos
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hec : (fun n => c * hLog g n) = hLog u := by
    rw [he]; funext n; field_simp
  rw [← hec]
  exact Nov1.deltaH_scale (hLog g) hp O L hc

/-- Theorem 7.1(1) with precisely positive nondecreasing u. The complete
protected tree is transported, with all occurrence structure retained. -/
theorem fixed_quota_suff_positive {d : ℕ} (hd : 2 ≤ d)
    {X : Set (Set (Pt d))} (hX : LangClass X) {u : ℝ → ℝ}
    (hu : ∀ x, 1 ≤ x → 0 < u x) (hum : MonotoneOn u (Ici 1))
    (q : Set (Pt d) → ℝ) (hq : ∀ K ∈ X, q K ∈ Icc (0 : ℝ) 1)
    (ht : ∀ K ∈ X, ∃ T, IsProtectedTree X (hLog u) q K T) :
    Achievable (hLog u) X q := by
  obtain ⟨c, g, hc, hc1, hg, hgm, he, hden⟩ := normalization_data u hu hum
  have hp : ∀ n, 1 ≤ n → 0 ≤ hLog u n := by
    intro n hn
    apply le_of_lt (mul_pos (hu n (by exact_mod_cast hn)) ?_)
    apply Real.log_pos
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have ht' : ∀ K ∈ X, ∃ T, IsProtectedTree X (hLog g) q K T := by
    intro K hK
    rw [he]
    exact (protected_normalization X (hLog u) q K c hc hc1 hp).1 (ht K hK)
  exact (Nov1.achievable_of_density_eq _ _ (hden d) X q).2
    (thm_fixed_quota_suff hd hX hg hgm q hq ht')

/-- Theorem 7.1(2), including the printed epsilon slack, for positive u. -/
theorem fixed_quota_nec_positive {d : ℕ} (hd : 2 ≤ d)
    {X : Set (Set (Pt d))} (hX : LangClass X) {u : ℝ → ℝ}
    (hu : ∀ x, 1 ≤ x → 0 < u x) (hum : MonotoneOn u (Ici 1))
    (α : Set (Pt d) → ℝ) (hα : ∀ K ∈ X, α K ∈ Icc (0 : ℝ) 1)
    (hach : Achievable (hLog u) X α) :
    ∀ ε : ℝ, 0 < ε → ∀ K ∈ X, ∃ T,
      IsProtectedTree X (hLog u) (fun L => max (α L - ε) 0) K T := by
  obtain ⟨c, g, hc, hc1, hg, hgm, he, hden⟩ := normalization_data u hu hum
  have ha := (Nov1.achievable_of_density_eq _ _ (hden d) X α).1 hach
  intro ε hε K hK
  have ht := thm_fixed_quota_nec hd hX hg hgm α hα ha ε hε K hK
  rw [he] at ht
  apply (protected_normalization X (hLog u) _ K c hc hc1 ?_).2 ht
  intro n hn
  apply le_of_lt (mul_pos (hu n (by exact_mod_cast hn)) ?_)
  apply Real.log_pos
  have := Nat.cast_nonneg (α := ℝ) n
  linarith

end BanachDensityHD.ExactStatements
