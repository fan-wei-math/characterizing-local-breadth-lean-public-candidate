import BanachDensity1D.Nov1.Profile.WordCounting

/-! # Exact target population and ambient volume of scheduled witness windows. -/

namespace BanachDensity1D.ProfileAux
open Set

lemma word_mass_le_twice (W : List Atom) : (W.map Atom.size).sum ≤ 2 * W.length := by
  induction W with
  | nil => simp
  | cons A W ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := A.size_bounds
    omega

namespace Requirement
variable {m : ℕ → ℕ} {hm : ∀ s, 0 < m s}

lemma base_mass (α : Cut → ℝ) (R : Requirement m hm)
    (h0 : 0 ≤ α R.root) (h1 : α R.root ≤ 1 / 2) :
    ((List.ofFn (R.baseAtom α)).map Atom.size).sum = points (α R.root) (m R.s) := by
  classical
  have hs (r : Fin (m R.s)) : (R.baseAtom α r).size =
      1 + if isPair (α R.root) r.val then 1 else 0 := by
    by_cases hr : isPair (α R.root) r.val <;> simp [baseAtom, Atom.size, hr]
  rw [List.map_ofFn, List.sum_ofFn]
  simp_rw [Function.comp_apply, hs]
  rw [Finset.sum_add_distrib]
  have hc : (∑ r : Fin (m R.s), if isPair (α R.root) r.val then (1 : ℕ) else 0) =
      pairs (α R.root) (m R.s) := by
    rw [← Finset.sum_range (fun r : ℕ => if isPair (α R.root) r then (1 : ℕ) else 0)]
    simpa [Finset.sum_boole] using pairs_count h0 h1 (m R.s)
  rw [hc]
  simp [points]

lemma witness_mass_upper (α : Cut → ℝ) (R : Requirement m hm) :
    ((R.witness α).map Atom.size).sum ≤ (2 + 2 * (R.s + 1)) * m R.s := by
  have h := word_mass_le_twice (R.witness α)
  rw [witness_length] at h
  nlinarith

end Requirement

namespace Staged
variable {m : ℕ → ℕ} {hm : ∀ s, 0 < m s}

noncomputable def witnessWindow (α : Cut → ℝ) (f : ℕ → Requirement m hm) (k : ℕ) : Set ℤ :=
  Ico (position (atoms α f) (Blocks.offset (blocks α f) k) : ℤ)
    (position (atoms α f) (Blocks.offset (blocks α f) k + ((f k).witness α).length) : ℤ)

lemma witnessWindow_finite (α : Cut → ℝ) (f : ℕ → Requirement m hm) (k : ℕ) :
    (witnessWindow α f k).Finite := finite_Ico _ _

lemma witnessWindow_mass (α : Cut → ℝ) (f : ℕ → Requirement m hm) (k : ℕ)
    (h0 : 0 ≤ α (f k).root) (h1 : α (f k).root ≤ 1 / 2) :
    (language (atoms α f) (f k).root ∩ witnessWindow α f k).ncard =
      points (α (f k).root) (m (f k).s) := by
  classical
  have h := witness_slice_count α f k (language (atoms α f) (f k).root)
    (fun B => B.label < (f k).root) (fun n x hx => atom_language_iff (atoms α f) (f k).root hx)
  change (language (atoms α f) (f k).root ∩ witnessWindow α f k).ncard = _ at h
  rw [h, weighted_filter, (f k).witness_at_root α]
  exact (f k).base_mass α h0 h1

lemma witnessWindow_volume (α : Cut → ℝ) (f : ℕ → Requirement m hm) (k : ℕ) :
    (witnessWindow α f k).ncard ≤ (2 + 2 * ((f k).s + 1)) * m (f k).s := by
  classical
  have h := witness_slice_count α f k univ (fun _ => True) (fun _ _ _ => by simp)
  simp only [univ_inter, ite_true] at h
  exact h.trans_le ((f k).witness_mass_upper α)

lemma witness_relative (α : Cut → ℝ) (f : ℕ → Requirement m hm) (k : ℕ) (q : Cut) :
    IsRelInterval (language (atoms α f) q) (language (atoms α f) q ∩ witnessWindow α f k) := by
  refine ⟨position (atoms α f) (Blocks.offset (blocks α f) k),
    (position (atoms α f) (Blocks.offset (blocks α f) k + ((f k).witness α).length) : ℤ) - 1, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, hlo, hup⟩
    exact ⟨hx, hlo, by omega⟩
  · rintro ⟨hx, hlo, hup⟩
    exact ⟨hx, hlo, by omega⟩

end Staged
end BanachDensity1D.ProfileAux
