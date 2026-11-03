import BanachDensity1D.Nov1.Profile.Stages

/-! # Pair-to-point surplus and nonnegative sufficiently late complete stages. -/

namespace BanachDensity1D.ProfileAux
open Set

noncomputable def atomSurplus (c : ℝ) (q : Cut) (A : Atom) : ℝ :=
  if A.label < q then (if A.pair then 1 else 0) - c * A.size else 0

noncomputable def surplus (c : ℝ) (q : Cut) (W : List Atom) : ℝ :=
  (W.map (atomSurplus c q)).sum

lemma surplus_append (c : ℝ) (q : Cut) (U V : List Atom) :
    surplus c q (U ++ V) = surplus c q U + surplus c q V := by simp [surplus]

lemma surplus_replicate (c : ℝ) (q : Cut) (n : ℕ) (A : Atom) :
    surplus c q (List.replicate n A) = (n : ℝ) * atomSurplus c q A := by
  simp [surplus, nsmul_eq_mul]

lemma pair_surplus_nonneg {c : ℝ} (hc : c ≤ 1 / 2) (q : Cut) (A : Atom) (hA : A.pair = true) :
    0 ≤ atomSurplus c q A := by
  by_cases hq : A.label < q <;> simp [atomSurplus, Atom.size, hA, hq] <;> linarith

lemma atom_surplus_lower {c : ℝ} (h0 : 0 ≤ c) (hc : c ≤ 1 / 2) (q : Cut) (A : Atom) :
    -c ≤ atomSurplus c q A := by
  cases hA : A.pair <;> by_cases hq : A.label < q <;>
    simp [atomSurplus, Atom.size, hA, hq] <;> linarith

namespace Requirement
variable {m : ℕ → ℕ} {hm : ∀ s, 0 < m s}

lemma witness_surplus_lower (α : Cut → ℝ) (R : Requirement m hm) {c : ℝ}
    (h0 : 0 ≤ c) (hc : c ≤ 1 / 2) (q : Cut) :
    -c * m R.s ≤ surplus c q (R.witness α) := by
  have hg (r : Fin (m R.s)) : -c ≤
      surplus c q (R.baseAtom α r :: List.replicate (R.s + 1) R.localAtom) := by
    have hb := atom_surplus_lower h0 hc q (R.baseAtom α r)
    have hp := pair_surplus_nonneg hc q R.localAtom rfl
    simp only [surplus, List.map_cons, List.sum_cons, List.map_replicate, List.sum_replicate,
      nsmul_eq_mul]
    have hprod : 0 ≤ (R.s + 1 : ℝ) * atomSurplus c q R.localAtom := mul_nonneg (by positivity) hp
    push_cast
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun r _ => hg r)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  change -c * m R.s ≤ _
  convert hsum using 1
  · ring
  · simp only [witness, surplus, List.map_flatten, List.sum_flatten, List.map_map, List.map_ofFn,
      List.sum_ofFn, Function.comp_def]

/-- For any previously listed target, stage-ending pairs dominate every possible
singleton deficit once the stage index is sufficiently large. -/
lemma complete_stage_nonneg (α : Cut → ℝ) (R : Requirement m hm) {c : ℝ}
    (h0 : 0 ≤ c) (hc : c ≤ 1 / 2) {i k : ℕ} (hi : i < k + 1)
    (hk : c ≤ (k + 1 : ℝ) * (1 - 2 * c)) :
    0 ≤ surplus c (cutEnumeration i) (R.stage α k) := by
  have hw := R.witness_surplus_lower α h0 hc (cutEnumeration i)
  have he : atomSurplus c (cutEnumeration i) (⟨true, endLabel (k + 1)⟩ : Atom) = 1 - 2 * c := by
    simp [atomSurplus, Atom.size, endLabel_below hi]
    ring
  rw [stage, surplus_append, surplus_replicate, he]
  have hprod := mul_nonneg (Nat.cast_nonneg (α := ℝ) (m R.s)) (sub_nonneg.mpr hk)
  push_cast
  nlinarith

end Requirement
end BanachDensity1D.ProfileAux
