import BanachDensity1D.Nov1.Profile.Stages

/-! # The actual countable, distinct, infinite rational-cut family.

The numerical density bounds are proved separately; existence of this family
alone is not the profile-realization theorem.
-/

namespace BanachDensity1D.ProfileAux.Staged
open Set
variable {m : ℕ → ℕ} {hm : ∀ s, 0 < m s}

noncomputable def blocks (α : Cut → ℝ) (f : ℕ → Requirement m hm) (k : ℕ) : List Atom :=
  (f k).stage α k
lemma blocks_nonempty (α : Cut → ℝ) (f : ℕ → Requirement m hm) (k : ℕ) : blocks α f k ≠ [] :=
  (f k).stage_nonempty α k

noncomputable def atoms (α : Cut → ℝ) (f : ℕ → Requirement m hm) : ℕ → Atom :=
  Blocks.flatten (blocks α f) (blocks_nonempty α f)

lemma atoms_at (α : Cut → ℝ) (f : ℕ → Requirement m hm) (k r : ℕ)
    (hr : r < (blocks α f k).length) :
    atoms α f (Blocks.offset (blocks α f) k + r) = (blocks α f k)[r] :=
  Blocks.flatten_at _ _ k r hr

lemma base_mem (α : Cut → ℝ) (R : Requirement m hm) (k : ℕ) (r : Fin (m R.s)) :
    R.baseAtom α r ∈ R.stage α k := by
  apply List.mem_append_left
  apply List.mem_flatten.mpr
  refine ⟨R.baseAtom α r :: List.replicate (R.s + 1) R.localAtom, ?_, by simp⟩
  exact List.mem_ofFn.mpr ⟨r, rfl⟩

/-- Every atom of stage k contributes actual points at or beyond integer k. -/
lemma stage_point (α : Cut → ℝ) (f : ℕ → Requirement m hm) (k : ℕ) {A : Atom}
    (hA : A ∈ blocks α f k) :
    ∃ x : ℤ, (k : ℤ) ≤ x ∧ ∃ n, x ∈ atomPoints (atoms α f) n ∧ atoms α f n = A := by
  obtain ⟨r, hr, hAr⟩ := List.getElem_of_mem hA
  let n := Blocks.offset (blocks α f) k + r
  have hAn : atoms α f n = A := by rw [atoms_at α f k r hr, hAr]
  have hle : k ≤ position (atoms α f) n := by
    have h1 : k ≤ Blocks.offset (blocks α f) k :=
      (Blocks.offset_strictMono _ (blocks_nonempty α f)).le_apply
    have hidx : k ≤ n := by dsimp [n]; omega
    exact hidx.trans (index_le_position (atoms α f) n)
  refine ⟨position (atoms α f) n, by exact_mod_cast hle, n, ?_, hAn⟩
  refine ⟨le_rfl, ?_⟩
  exact_mod_cast position_strictMono (atoms α f) (show n < n + 1 by omega)

lemma language_infinite (α : Cut → ℝ) (f : ℕ → Requirement m hm)
    (hf : ∀ R, ∀ B : ℕ, ∃ k ≥ B, f k = R) (q : Cut) : (language (atoms α f) q).Infinite := by
  intro hfin
  obtain ⟨b, hb⟩ := hfin.bddAbove
  obtain ⟨R, _, hroot⟩ := Requirement.exists_root (m := m) (hm := hm) q 0
  obtain ⟨k, hk, hfk⟩ := hf R (b.toNat + 1)
  let r : Fin (m R.s) := ⟨0, hm R.s⟩
  have hmem : R.baseAtom α r ∈ blocks α f k := by
    rw [blocks, hfk]
    exact base_mem α R k r
  obtain ⟨x, hx, n, hxn, hAn⟩ := stage_point α f k hmem
  have hlabel : (atoms α f n).label < q := by
    rw [hAn]
    change R.baseLabel r < q
    rw [← hroot]
    exact R.baseLabel_below_root r
  have hxL : x ∈ language (atoms α f) q := ⟨n, hxn, hlabel⟩
  have hxb := hb hxL
  have hbNat := Int.self_le_toNat b
  omega

lemma language_proper (α : Cut → ℝ) (f : ℕ → Requirement m hm)
    (hf : ∀ R, ∀ B : ℕ, ∃ k ≥ B, f k = R) {p q : Cut} (hpq : p < q) :
    language (atoms α f) p ⊂ language (atoms α f) q := by
  let i := cutEnumeration.symm p
  obtain ⟨R, hs, hroot⟩ := Requirement.exists_root (m := m) (hm := hm) q i
  obtain ⟨k, _, hfk⟩ := hf R 0
  let r : Fin (m R.s) := ⟨0, hm R.s⟩
  have hmem : R.baseAtom α r ∈ blocks α f k := by
    rw [blocks, hfk]
    exact base_mem α R k r
  obtain ⟨x, _, n, hxn, hAn⟩ := stage_point α f k hmem
  have hlabel : (atoms α f n).label < q := by
    rw [hAn]
    change R.baseLabel r < q
    rw [← hroot]
    exact R.baseLabel_below_root r
  have hnot : ¬ (atoms α f n).label < p := by
    rw [hAn]
    change ¬ R.baseLabel r < p
    have hle : (p : ℚ) ≤ lowerCut R.root (R.s + 1) := by
      have hi : i < R.s + 1 := by omega
      have hip : cutEnumeration i = p := cutEnumeration.apply_symm_apply p
      have hpre := le_lowerCut R.root hi (by rw [hip, hroot]; exact hpq)
      simpa only [hip] using hpre
    exact not_lt_of_ge (hle.trans (R.baseLabel_above_barrier r).le)
  refine ssubset_iff_subset_not_subset.mpr ⟨language_mono _ hpq.le, ?_⟩
  intro hsub
  exact hnot ((atom_language_iff (atoms α f) p hxn).mp (hsub ⟨n, hxn, hlabel⟩))

lemma family_langClass (α : Cut → ℝ) (f : ℕ → Requirement m hm)
    (hf : ∀ R, ∀ B : ℕ, ∃ k ≥ B, f k = R) : LangClass (range (language (atoms α f))) := by
  refine ⟨range_nonempty _, Set.countable_range _, ?_⟩
  rintro L ⟨q, rfl⟩
  exact language_infinite α f hf q

lemma language_injective (α : Cut → ℝ) (f : ℕ → Requirement m hm)
    (hf : ∀ R, ∀ B : ℕ, ∃ k ≥ B, f k = R) : Function.Injective (language (atoms α f)) := by
  intro p q he
  by_contra hpq
  rcases lt_or_gt_of_ne hpq with hlt | hlt
  · exact (language_proper α f hf hlt).ne he
  · exact (language_proper α f hf hlt).ne he.symm

end BanachDensity1D.ProfileAux.Staged
