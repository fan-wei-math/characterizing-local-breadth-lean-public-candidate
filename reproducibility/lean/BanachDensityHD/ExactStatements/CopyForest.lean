import BanachDensityHD.Characterization

/-! Literal broad, dyadic-copy certificates and their nonstrict parent-scan forest. -/
namespace BanachDensityHD.ExactStatements
open Set Filter SuffAux
open scoped Classical

noncomputable def dyadicQuota {d : ℕ} (α : Set (Pt d) → ℝ) (L : Set (Pt d)) (k : ℕ) : ℝ :=
  max (α L - (1 / 2 : ℝ) ^ k) 0

/-- Definition 7.14 with exactly the manuscript's dyadic quotas. The broad
child clause includes every positive copy index, including equal-language edges. -/
def DyadicCopyProtected {d : ℕ} (X : Set (Set (Pt d))) (h : ℕ → ℝ)
    (α : Set (Pt d) → ℝ) (K : Set (Pt d)) (k : ℕ) (T : DTree d) : Prop :=
  T.root.L = K ∧ T.root.k = k ∧
  (∀ p ∈ T.paths, ∀ v ∈ p, v.L ∈ X ∧ ↑v.P ⊆ v.L ∧ 1 ≤ v.s ∧ 0 ≤ v.a ∧ 1 ≤ v.k) ∧
  (∀ p v w, p ++ [v, w] ∈ T.paths → w.L ⊆ v.L ∧ v.a < w.a) ∧
  (∀ p ∈ T.paths, ∀ (hp : p ≠ []), ∀ M ∈ X, ∀ n, 1 ≤ n →
      ↑(p.getLast hp).P ⊆ M → M ⊆ (p.getLast hp).L →
      ∃ w : Deco d, w.L = M ∧ w.k = n ∧ p ++ [w] ∈ T.paths) ∧
  (∀ p ∈ T.paths, ∀ (hp : p ≠ []),
      GeomFeasible h (pathFn Deco.L p hp)
        (fun i => dyadicQuota α (pathFn Deco.L p hp i) (pathFn Deco.k p hp i))
        (pathFn Deco.s p hp) (p.getLast hp).a)

/-- Nonstrict scanning retains every earlier occurrence of the same language
as an ancestor. No quotient by a language label or accuracy index is taken. -/
theorem equal_language_ancestor {d : ℕ} (lab P : ℕ → Set (Pt d)) (z v : ℕ)
    (hzv : z ≤ v) (hP : P z ⊆ lab z) (he : lab v = lab z) :
    IsAncestor (scanParent false lab P) z v := by
  induction v using Nat.strong_induction_on with
  | h v ih =>
    by_cases hz : z = v
    · subst v; exact IsAncestor.refl z
    have hzlt : z < v := by omega
    have hp : PossibleParent false lab P z v := ⟨hzlt, by simpa [he], by simpa [he] using hP⟩
    obtain ⟨p, hs, hzp, hpv, hvp, hpz⟩ := ForestAux.scan_retains hzlt hp
      (fun i hi hpi => by simpa [he] using ForestAux.sub_of_test hpi.2.1)
    have hep : lab p = lab z := Set.Subset.antisymm hpz (he ▸ hvp)
    exact IsAncestor.step (ih p hpv hzp hep) hs

/-- Lemma 7.15 for the stated enumeration convention: adjacent accuracy copies
of each language lie on one ancestor chain in the literal nonstrict forest. -/
theorem adjacent_copy_ancestry {d : ℕ} (lab P : ℕ → Set (Pt d)) (acc : ℕ → ℕ)
    (hP : ∀ z, P z ⊆ lab z)
    (horder : ∀ i j, lab i = lab j → acc i < acc j → i < j)
    {z w : ℕ} (he : lab z = lab w) (hk : acc w = acc z + 1) :
    IsAncestor (scanParent false lab P) z w := by
  exact equal_language_ancestor lab P z w (horder z w he (by omega)).le (hP z) he.symm

/-- Lemma 7.16 for each specified original copy, using exactly the manuscript's
nonstrict scan and critical-vertex guess, independently of any schedule choice. -/
theorem capture_specified_copy {d : ℕ} (lab P : ℕ → Set (Pt d)) (z : ℕ)
    (hP : (P z).Finite ∧ P z ⊆ lab z) (w : ℕ → Pt d)
    (hw : IsFullEnumeration w (lab z)) :
    ∃ T, ∀ t ≥ T, ∃ v, guess ⊤ lab w t = some v ∧
      IsAncestor (scanParent false lab P) z v :=
  ForestAux.capture_gen false ⊤ lab P (fun h => False.elim (Bool.false_ne_true h)) z
    (ENat.natCast_lt_top z) hP w hw

/-- The literal dyadic certificates supply the actual occurrence assignment
and board-game path invariant for any enumeration of copies. -/
theorem dyadic_treeFam {d : ℕ} {X : Set (Set (Pt d))} (hX : LangClass X) {h : ℕ → ℝ}
    {α : Set (Pt d) → ℝ} (Tf : Set (Pt d) → ℕ → DTree d)
    (hTf : ∀ K ∈ X, ∀ k, 1 ≤ k → DyadicCopyProtected X h α K k (Tf K k))
    (lab : ℕ → Set (Pt d)) (acc : ℕ → ℕ)
    (hlab : ∀ j, lab j ∈ X) (hacc : ∀ j, 1 ≤ acc j) :
    TreeFam false ⊤ lab acc Tf h (fun v => dyadicQuota α v.L v.k) := by
  refine ⟨fun j _ => ?_, fun r j p _ _ hpj hrel l hl hL hk hP => ?_,
    fun r _ l hl => ?_, fun r _ l hl v hv => ?_,
    fun j _ => hX.infinite _ (hlab j), fun h => False.elim (Bool.false_ne_true h)⟩
  · have hT := hTf (lab j) (hlab j) (acc j) (hacc j)
    exact ⟨hT.1, hT.2.1⟩
  · have hT := hTf (lab r) (hlab r) (acc r) (hacc r)
    have hne := paths_ne hl
    have hlast : l.getLast hne = lastOf l := (CharAux.getLastD_eq_getLast _ _ hne).symm
    exact hT.2.2.2.2.1 l hl hne (lab j) (hlab j) (acc j) (hacc j)
      (by simpa [hlast] using hP) (by simpa [hlast, hL] using hrel)
  · have hT := hTf (lab r) (hlab r) (acc r) (hacc r)
    have hne := paths_ne hl
    refine ⟨hne, anti_of_step l (fun i hi => ?_), ?_⟩
    · exact (hT.2.2.2.1 _ _ _ (tree_edge hl i hi)).1
    · have ht := hT.2.2.2.2.2 l hl hne
      simp only [pathFn_eq] at ht
      rw [← CharAux.getLastD_eq_getLast _ TreesAux.d0 hne] at ht
      exact ht
  · have hv := (hTf (lab r) (hlab r) (acc r) (hacc r)).2.2.1 l hl v hv
    exact ⟨hv.2.1, by linarith [hv.2.2.1]⟩

/-- Lemma 7.17: the one generator built from these supplied dyadic trees
satisfies the quota of each specified copy. This is the actual nonstrict
forest, occurrence assignment, board policy, simulator and sewing construction. -/
theorem dyadic_fixed_copy_density {d : ℕ} (hd : 2 ≤ d)
    {X : Set (Set (Pt d))} (hX : LangClass X) {g : ℝ → ℝ}
    (hg1 : ∀ x, 1 ≤ x → 1 ≤ g x) {α : Set (Pt d) → ℝ}
    (hα : ∀ K ∈ X, α K ∈ Icc (0 : ℝ) 1)
    (Tf : Set (Pt d) → ℕ → DTree d)
    (hTf : ∀ K ∈ X, ∀ k, 1 ≤ k → DyadicCopyProtected X (hLog g) α K k (Tf K k))
    (lab : ℕ → Set (Pt d)) (acc : ℕ → ℕ)
    (hlab : ∀ j, lab j ∈ X) (hacc : ∀ j, 1 ≤ acc j)
    (Pb : Set (Rect d)) (cst : ℝ) (hs : Sew Pb (hLog g) cst) :
    let c := cfgOf false ⊤ lab acc Tf (fun v => dyadicQuota α v.L v.k) (hLog g) Pb
    ∀ z w, IsFullEnumeration w (lab z) → c.gen.EventuallyValid w (lab z) ∧
      dyadicQuota α (lab z) (acc z) ≤ deltaH (hLog g) (c.gen.outputSet w) (lab z) := by
  intro c z w hw
  have hTF := dyadic_treeFam hX Tf hTf lab acc hlab hacc
  have hc : c.Good := cfgOf_good hTF Pb
  obtain ⟨r, hr, hin, hL, hk⟩ := occ_inv hTF z (ENat.natCast_lt_top z)
  have hqz : c.qd (lastOf (c.occ z)) = dyadicQuota α (lab z) (acc z) := by
    change dyadicQuota α (lastOf (occOf false lab acc Tf z)).L
      (lastOf (occOf false lab acc Tf z)).k = _
    rw [hL, hk]
  have hq : dyadicQuota α (lab z) (acc z) ≤ 1 := by
    apply max_le _ zero_le_one
    have hp : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ acc z := by positivity
    linarith [(hα (lab z) (hlab z)).2]
  have ht := Cfg.gen_works (by omega : 1 ≤ d) hc hs
    (Real.log_pos (by norm_num : (1 : ℝ) < 3)) (hLog_ge hg1)
    (ENat.natCast_lt_top z) hw (by rw [hqz]; exact hq) (last_s_nonneg hTF (ENat.natCast_lt_top z))
  rwa [hqz] at ht

/-- Lemma 7.17: the one generator built from these supplied dyadic trees
satisfies the quota of each specified copy. This is the actual nonstrict
forest, occurrence assignment, board policy, simulator and sewing construction. -/
theorem dyadic_fixed_copy_density_positive {d : ℕ} (hd : 2 ≤ d)
    {X : Set (Set (Pt d))} (hX : LangClass X) {g : ℝ → ℝ}
    (hg0 : ∀ x, 1 ≤ x → 0 < g x) (hgm : MonotoneOn g (Ici 1)) {α : Set (Pt d) → ℝ}
    (hα : ∀ K ∈ X, α K ∈ Icc (0 : ℝ) 1)
    (Tf : Set (Pt d) → ℕ → DTree d)
    (hTf : ∀ K ∈ X, ∀ k, 1 ≤ k → DyadicCopyProtected X (hLog g) α K k (Tf K k))
    (lab : ℕ → Set (Pt d)) (acc : ℕ → ℕ)
    (hlab : ∀ j, lab j ∈ X) (hacc : ∀ j, 1 ≤ acc j)
    (Pb : Set (Rect d)) (cst : ℝ) (hs : Sew Pb (hLog g) cst) :
    let c := cfgOf false ⊤ lab acc Tf (fun v => dyadicQuota α v.L v.k) (hLog g) Pb
    ∀ z w, IsFullEnumeration w (lab z) → c.gen.EventuallyValid w (lab z) ∧
      dyadicQuota α (lab z) (acc z) ≤ deltaH (hLog g) (c.gen.outputSet w) (lab z) := by
  intro c z w hw
  have hTF := dyadic_treeFam hX Tf hTf lab acc hlab hacc
  have hc : c.Good := cfgOf_good hTF Pb
  obtain ⟨r, hr, hin, hL, hk⟩ := occ_inv hTF z (ENat.natCast_lt_top z)
  have hqz : c.qd (lastOf (c.occ z)) = dyadicQuota α (lab z) (acc z) := by
    change dyadicQuota α (lastOf (occOf false lab acc Tf z)).L
      (lastOf (occOf false lab acc Tf z)).k = _
    rw [hL, hk]
  have hq : dyadicQuota α (lab z) (acc z) ≤ 1 := by
    apply max_le _ zero_le_one
    have hp : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ acc z := by positivity
    linarith [(hα (lab z) (hlab z)).2]
  have h0 : 0 < g 1 * Real.log 3 := mul_pos (hg0 1 le_rfl)
    (Real.log_pos (by norm_num))
  have hbound : ∀ n : ℕ, 1 ≤ n → g 1 * Real.log 3 ≤ hLog g n := by
    intro n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog : Real.log 3 ≤ Real.log (2 + (n : ℝ)) :=
      Real.log_le_log (by norm_num) (by linarith)
    exact mul_le_mul (hgm (by simp) hn' hn') hlog (by positivity) (hg0 n hn').le
  have ht := Cfg.gen_works (by omega : 1 ≤ d) hc hs
    h0 hbound
    (ENat.natCast_lt_top z) hw (by rw [hqz]; exact hq) (last_s_nonneg hTF (ENat.natCast_lt_top z))
  rwa [hqz] at ht

end BanachDensityHD.ExactStatements
