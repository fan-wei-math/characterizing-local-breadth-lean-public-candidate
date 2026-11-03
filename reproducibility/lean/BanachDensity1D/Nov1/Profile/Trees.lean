import BanachDensity1D.Nov1.Profile.CutRefinement

/-! # Canonical finite-height rational-cut obstruction trees. -/

namespace BanachDensity1D.ProfileAux
open Set

noncomputable def cutTree (A : ℕ → Atom) (a : ℚ) (ha0 : 0 ≤ a) :
    (n : ℕ) → (q : Cut) → a < (q : ℚ) → LTree
  | 0, q, _ => .leaf (language A q)
  | n + 1, q, hq => .node (language A q) (fun i =>
      cutTree A a ha0 n (childCuts a q ha0 hq i).val (childCuts a q ha0 hq i).property.1)

@[simp] lemma cutTree_label (A : ℕ → Atom) (a : ℚ) (ha0 : 0 ≤ a)
    (n : ℕ) (q : Cut) (hq : a < (q : ℚ)) : (cutTree A a ha0 n q hq).label = language A q := by
  cases n <;> rfl

lemma cutTree_admissible (A : ℕ → Atom)
    (hproper : ∀ p q : Cut, p < q → language A p ⊂ language A q)
    (a : ℚ) (ha0 : 0 ≤ a) (n : ℕ) (q : Cut) (hq : a < (q : ℚ)) :
    def_aot (range (language A)) (language A q) (cutTree A a ha0 n q hq) := by
  refine ⟨cutTree_label _ _ _ _ _ _, ?_⟩
  induction n generalizing q with
  | zero => trivial
  | succ n ih =>
    refine ⟨?_, ?_⟩
    · intro i
      simp only [cutTree_label]
      exact ⟨mem_range_self _, hproper _ _ (childCuts a q ha0 hq i).property.2,
        ih _ (childCuts a q ha0 hq i).property.1⟩
    · intro F hF hsub
      obtain ⟨p, hap, hpq, hFp⟩ := finite_cut_cover A hF q ha0 hq hsub
      obtain ⟨i, hi⟩ := childCuts_surjective a q ha0 hq (⟨p, hap, hpq⟩ : ChildCut a q)
      refine ⟨i, ?_⟩
      rw [cutTree_label, hi]
      exact hFp

/-- Every path is a strictly decreasing rational history of exactly n+1 cuts,
all above a, with its labels obtained from those cuts. -/
lemma cutTree_path (A : ℕ → Atom) (a : ℚ) (ha0 : 0 ≤ a)
    (n : ℕ) (q : Cut) (hq : a < (q : ℚ)) {H : List (Set ℤ)}
    (hH : H ∈ (cutTree A a ha0 n q hq).paths) :
    ∃ C : List Cut, C.length = n + 1 ∧ C.head? = some q ∧
      C.Pairwise (fun p q => q < p) ∧ (∀ p ∈ C, a < (p : ℚ) ∧ p ≤ q) ∧
      H = C.map (language A) := by
  induction n generalizing q H with
  | zero =>
    have he : H = [language A q] := hH
    refine ⟨[q], by simp, by simp, by simp, ?_, he⟩
    intro p hp
    have hpq : p = q := List.mem_singleton.mp hp
    subst p
    exact ⟨hq, le_rfl⟩
  | succ n ih =>
    obtain ⟨i, P, hP, rfl⟩ := hH
    obtain ⟨C, hlen, hhead, hpair, hbounds, rfl⟩ := ih _
      (childCuts a q ha0 hq i).property.1 hP
    have hlt := (childCuts a q ha0 hq i).property.2
    refine ⟨q :: C, by simp [hlen], by simp, ?_, ?_, rfl⟩
    · apply List.pairwise_cons.mpr
      exact ⟨fun p hp => lt_of_le_of_lt (hbounds p hp).2 hlt, hpair⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨hq, le_rfl⟩
      · exact ⟨(hbounds p hp).1, (hbounds p hp).2.trans hlt.le⟩

end BanachDensity1D.ProfileAux
