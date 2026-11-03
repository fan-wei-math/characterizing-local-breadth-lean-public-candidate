import BanachDensityHD.ExactStatements.TreeMap
import BanachDensityHD.ExactStatements.CopyForest

namespace BanachDensityHD.ExactStatements
open Set
open scoped Classical

/-- Only accuracy and cutoff data change; languages, protection and radii stay exact. -/
def recode {d : ℕ} (index : ℕ → ℕ) (cutoff : ℝ → ℝ) (v : Deco d) : Deco d :=
  .mk v.L (index v.k) v.P (cutoff v.s) v.a

lemma geomFeasible_quota_mono {d r : ℕ} (h : ℕ → ℝ)
    (L : Fin (r + 1) → Set (Pt d)) (q q' s : Fin (r + 1) → ℝ) (a : ℝ)
    (hle : ∀ i, q' i ≤ q i) (hf : GeomFeasible h L q s a) :
    GeomFeasible h L q' s a :=
  TreesAux.collapse h L q' s L q s a a id id (fun _ => rfl) (fun _ => rfl)
    hle (fun _ => rfl) (fun _ => le_rfl) monotone_id rfl le_rfl hf

lemma dyadic_le_reciprocal (k : ℕ) (hk : 1 ≤ k) :
    (1 / 2 : ℝ) ^ k ≤ 1 / (k : ℝ) := by
  have hp : (k : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  simpa only [one_div_pow] using one_div_le_one_div_of_le hk' hp

/-- Dyadic games have at least the reciprocal quotas, on the same complete tree. -/
theorem reciprocal_of_dyadic {d : ℕ} {X : Set (Set (Pt d))} {h : ℕ → ℝ}
    {α : Set (Pt d) → ℝ} {K : Set (Pt d)} {k : ℕ} {T : DTree d}
    (ht : DyadicCopyProtected X h α K k T) : IsBroadCopyProtectedTree X h α K k T := by
  obtain ⟨hr, hk, hv, he, hc, hf⟩ := ht
  refine ⟨hr, hk, hv, he, hc, ?_⟩
  intro p hp hne
  apply geomFeasible_quota_mono h _ _ _ _ _ ?_ (hf p hp hne)
  intro i
  have hvk := (hv p hp (p.get ⟨i.val, by have := i.isLt; have := List.length_pos_iff.2 hne; omega⟩)
    (List.get_mem _ _)).2.2.2.2
  exact max_le_max_right _ (sub_le_sub_left (dyadic_le_reciprocal _ hvk) _)

/-- Restrict reciprocal certificates to power-of-two copy indices, then relabel
2^k by k. All required dyadic children and all retained original paths survive. -/
theorem dyadic_of_reciprocal {d : ℕ} {X : Set (Set (Pt d))} {h : ℕ → ℝ}
    {α : Set (Pt d) → ℝ} {K : Set (Pt d)} {k : ℕ} (hk : 1 ≤ k)
    {T : DTree d} (ht : IsBroadCopyProtectedTree X h α K (2 ^ k) T) :
    ∃ S, DyadicCopyProtected X h α K k S := by
  let f : Deco d → Deco d := recode Nat.log2 id
  let Good : Deco d → Prop := fun v => ∃ n, 1 ≤ n ∧ v.k = 2 ^ n
  have hr : Good T.root := ⟨k, hk, ht.2.1⟩
  have hroot : (f T.root).k = k := by simp [f, recode, ht.2.1, Nat.log2_two_pow]
  have hq : ∀ v, Good v → dyadicQuota α (f v).L (f v).k = copyQuota α v.L v.k := by
    rintro v ⟨n, hn, he⟩
    simp [dyadicQuota, copyQuota, f, recode, he, Nat.log2_two_pow, one_div_pow]
  have hb : BroadCertificate X h (fun v => copyQuota α v.L v.k) K (2 ^ k) T := ht
  have hs := broadCertificate_map (g := h)
    (Q' := fun v => dyadicQuota α v.L v.k) hb f Good hr hroot
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun v hv hvs _ => ?_)
    (fun n hn => ?_) (fun p hp hpath hgood hf => ?_)
  · exact ⟨treeMap T f Good hr, hs⟩
  · obtain ⟨n, hn, he⟩ := hv
    exact ⟨hvs, by simpa [f, recode, he, Nat.log2_two_pow] using hn⟩
  · refine ⟨2 ^ n, Nat.one_le_pow _ _ (by decide), fun v he => ⟨⟨n, hn, he⟩, ?_⟩⟩
    simp [f, recode, he, Nat.log2_two_pow]
  · have hqe : pathFn (fun v => dyadicQuota α (f v).L (f v).k) p hp =
        pathFn (fun v => copyQuota α v.L v.k) p hp := by
      funext i
      exact hq _ (hgood _ (List.get_mem _ _))
    rw [hqe]
    exact hf

/-- Complete certificate-existence equivalence for the two schedules, including
actual countable trees and universal broad-copy child structure. -/
theorem all_dyadic_iff_reciprocal {d : ℕ} (X : Set (Set (Pt d))) (h : ℕ → ℝ)
    (α : Set (Pt d) → ℝ) :
    (∀ K ∈ X, ∀ k : ℕ, 1 ≤ k → ∃ T, DyadicCopyProtected X h α K k T) ↔
    (∀ K ∈ X, ∀ k : ℕ, 1 ≤ k → ∃ T, IsBroadCopyProtectedTree X h α K k T) := by
  constructor
  · intro hd K hK k hk
    obtain ⟨T, ht⟩ := hd K hK k hk
    exact ⟨T, reciprocal_of_dyadic ht⟩
  · intro hr K hK k hk
    obtain ⟨T, ht⟩ := hr K hK (2 ^ k) (Nat.one_le_pow _ _ (by decide))
    exact dyadic_of_reciprocal hk ht

end BanachDensityHD.ExactStatements
