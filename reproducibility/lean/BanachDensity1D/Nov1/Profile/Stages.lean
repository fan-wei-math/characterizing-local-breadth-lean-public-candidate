import BanachDensity1D.Nov1.Profile.Requirements
import BanachDensity1D.Nov1.Profile.Blocks

/-! # Witness words, local padding and stage-ending padding. -/

namespace BanachDensity1D.ProfileAux
open Set

namespace Requirement
variable {m : ℕ → ℕ} {hm : ∀ s, 0 < m s}

open Classical in
noncomputable def baseAtom (α : Cut → ℝ) (R : Requirement m hm) (r : Fin (m R.s)) : Atom :=
  ⟨decide (isPair (α R.root) r.val), R.baseLabel r⟩

noncomputable def localAtom (R : Requirement m hm) : Atom := ⟨true, paddingLabel R.root (R.s + 1)⟩

noncomputable def witness (α : Cut → ℝ) (R : Requirement m hm) : List Atom :=
  (List.ofFn fun r => R.baseAtom α r :: List.replicate (R.s + 1) R.localAtom).flatten

noncomputable def stage (α : Cut → ℝ) (R : Requirement m hm) (k : ℕ) : List Atom :=
  R.witness α ++ List.replicate ((k + 1) * m R.s) (⟨true, endLabel (k + 1)⟩ : Atom)

lemma witness_length (α : Cut → ℝ) (R : Requirement m hm) :
    (R.witness α).length = m R.s * (R.s + 2) := by
  simp [witness, List.length_flatten, List.map_ofFn, Function.comp_def]

lemma stage_nonempty (α : Cut → ℝ) (R : Requirement m hm) (k : ℕ) : R.stage α k ≠ [] := by
  have hpos := hm R.s
  have hpadpos : 0 < (k + 1) * m R.s := Nat.mul_pos (by omega) hpos
  change R.witness α ++ List.replicate ((k + 1) * m R.s) (⟨true, endLabel (k + 1)⟩ : Atom) ≠ []
  intro he
  have hnil := (List.append_eq_nil_iff.mp he).2
  have := congrArg List.length hnil
  simp only [List.length_replicate, List.length_nil] at this
  omega

/-- Base atoms all lie below the target cutoff and local padding all lies above it. -/
lemma witness_at_root (α : Cut → ℝ) (R : Requirement m hm) :
    (R.witness α).filter (fun A => decide (A.label < R.root)) =
      List.ofFn (R.baseAtom α) := by
  classical
  let p : Atom → Bool := fun A => decide (A.label < R.root)
  have hbase (r : Fin (m R.s)) : p (R.baseAtom α r) = true := by
    simpa [p, baseAtom] using R.baseLabel_below_root r
  have hpad : p R.localAtom = false := by
    have hp := padding_above R.root (R.s + 1)
    simp only [p, localAtom]
    exact decide_eq_false (not_lt_of_ge hp.le)
  have hf (r : Fin (m R.s)) :
      (R.baseAtom α r :: List.replicate (R.s + 1) R.localAtom).filter p = [R.baseAtom α r] := by
    simp [hbase r, hpad]
  have he : (List.ofFn (fun r => R.baseAtom α r :: List.replicate (R.s + 1) R.localAtom)).map
      (List.filter p) = List.ofFn (fun r => [R.baseAtom α r]) := by
    rw [List.map_ofFn]
    congr 1
    funext r
    exact hf r
  change ((List.ofFn _).flatten).filter p = _
  rw [List.filter_flatten, he]
  have hflat (l : List Atom) : (l.map fun A => [A]).flatten = l := by
    induction l with
    | nil => rfl
    | cons A l ih => simpa using congrArg (List.cons A) ih
  simpa only [List.map_ofFn, Function.comp_def] using hflat (List.ofFn (R.baseAtom α))

lemma base_invisible (α : Cut → ℝ) (R : Requirement m hm) {i : ℕ}
    (hi : i < R.s + 1) (hiq : cutEnumeration i < R.root) (r : Fin (m R.s)) :
    ¬ (R.baseAtom α r).label < cutEnumeration i := by
  change ¬ (R.baseLabel r : ℚ) < (cutEnumeration i : ℚ)
  have hb := R.baseLabel_above_barrier r
  have hle := le_lowerCut R.root hi hiq
  exact not_lt_of_ge (le_trans hle hb.le)

lemma padding_invisible (R : Requirement m hm) {i : ℕ} (hiq : cutEnumeration i ≤ R.root) :
    ¬ R.localAtom.label < cutEnumeration i := by
  change ¬ paddingLabel R.root (R.s + 1) < cutEnumeration i
  exact not_lt_of_ge (le_trans hiq (padding_above _ _).le)

lemma base_protected (α : Cut → ℝ) (R : Requirement m hm) {q : Cut} (hq : R.root ≤ q)
    (r : Fin (m R.s)) : (R.baseAtom α r).label < q :=
  lt_of_lt_of_le (R.baseLabel_below_root r) hq

lemma padding_protected (R : Requirement m hm) {i : ℕ}
    (hi : i < R.s + 1) (hiq : R.root < cutEnumeration i) :
    R.localAtom.label < cutEnumeration i := padding_below _ hi hiq

end Requirement
end BanachDensity1D.ProfileAux
