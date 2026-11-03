import BanachDensityHD.ExactStatements.CopySchedule
import BanachDensityHD.ExactStatements.PositiveThreshold

namespace BanachDensityHD.ExactStatements
open Set
open scoped Classical

/-- Complete copy-tree transport retains every original path, root, copy,
protected set, radius and required child; only cutoffs change. -/
theorem copy_normalized {d : ℕ} {X : Set (Set (Pt d))} {h : ℕ → ℝ}
    (Q : Set (Pt d) → ℕ → ℝ) {K : Set (Pt d)} {k : ℕ} {T : DTree d}
    {c : ℝ} (hc : 0 < c) (hp : ∀ n, 1 ≤ n → 0 ≤ h n)
    (ht : BroadCertificate X h (fun v => Q v.L v.k) K k T) :
    ∃ S, BroadCertificate X (fun n => h n / c) (fun v => Q v.L v.k) K k S := by
  let f : Deco d → Deco d := recode id (fun s => max 1 (c * s))
  have hr : True := trivial
  have hs := broadCertificate_map (g := fun n => h n / c)
    (Q' := fun v => Q v.L v.k) ht f (fun _ => True) hr ht.2.1
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ _ hvk => ⟨le_max_left _ _, hvk⟩)
    (fun n hn => ⟨n, hn, fun _ he => ⟨trivial, he⟩⟩)
    (fun _ _ _ _ hf => Nov1.geomFeasible_normalized_cutoffs h hp c hc _ _ _ _ hf)
  exact ⟨treeMap T f (fun _ => True) hr, hs⟩

/-- Inverse complete transport: multiply the threshold back and divide cutoffs. -/
theorem copy_unnormalized {d : ℕ} {X : Set (Set (Pt d))} {h : ℕ → ℝ}
    (Q : Set (Pt d) → ℕ → ℝ) {K : Set (Pt d)} {k : ℕ} {T : DTree d}
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (ht : BroadCertificate X (fun n => h n / c) (fun v => Q v.L v.k) K k T) :
    ∃ S, BroadCertificate X h (fun v => Q v.L v.k) K k S := by
  let f : Deco d → Deco d := recode id (fun s => s / c)
  have hr : True := trivial
  have hs := broadCertificate_map (g := h) (Q' := fun v => Q v.L v.k)
    ht f (fun _ => True) hr ht.2.1 (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ hvs hvk => ⟨(one_le_div hc).2 (hc1.trans hvs), hvk⟩)
    (fun n hn => ⟨n, hn, fun _ he => ⟨trivial, he⟩⟩) (fun p hne _ _ hf => ?_)
  · exact ⟨treeMap T f (fun _ => True) hr, hs⟩
  · have hx := (Nov1.geomFeasible_scale (fun n => h n / c) c hc
      (pathFn Deco.L p hne) (pathFn (fun v => Q v.L v.k) p hne)
      (pathFn Deco.s p hne) (p.getLast hne).a).2 hf
    have he : (fun n => c * (h n / c)) = h := by funext n; field_simp
    rw [he] at hx
    exact hx

/-- Theorem 7.2 and the unnumbered exact-profile characterization, with
positive u and the literal dyadic schedule of Definition 7.14. -/
theorem exact_profile_positive_dyadic {d : ℕ} (hd : 2 ≤ d)
    {X : Set (Set (Pt d))} (hX : LangClass X) {u : ℝ → ℝ}
    (hu : ∀ x, 1 ≤ x → 0 < u x) (hum : MonotoneOn u (Ici 1))
    (α : Set (Pt d) → ℝ) (hα : ∀ K ∈ X, α K ∈ Icc (0 : ℝ) 1) :
    Achievable (hLog u) X α ↔
      ∀ K ∈ X, ∀ k : ℕ, 1 ≤ k → ∃ T, DyadicCopyProtected X (hLog u) α K k T := by
  obtain ⟨c, g, hc, hc1, hg, hgm, he, hden⟩ := normalization_data u hu hum
  have hp : ∀ n, 1 ≤ n → 0 ≤ hLog u n := by
    intro n hn
    apply le_of_lt (mul_pos (hu n (by exact_mod_cast hn)) ?_)
    apply Real.log_pos
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  rw [all_dyadic_iff_reciprocal]
  rw [Nov1.achievable_of_density_eq _ _ (hden d) X α, thm_main_broad hd hX hg hgm α hα]
  constructor
  · intro h K hK k hk
    obtain ⟨T, ht⟩ := h K hK k hk
    rw [he] at ht
    exact copy_unnormalized (copyQuota α) hc hc1 ht
  · intro h K hK k hk
    obtain ⟨T, ht⟩ := h K hK k hk
    rw [he]
    exact copy_normalized (copyQuota α) hc hp ht

end BanachDensityHD.ExactStatements
