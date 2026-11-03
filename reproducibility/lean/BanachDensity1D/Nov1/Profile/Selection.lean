import BanachDensity1D.Nov1.Profile.Stages

/-! # Filtering a witness word to one refinement layer. -/

namespace BanachDensity1D.ProfileAux
open Set

lemma filter_ofFn_singleton {T : Type*} {n : ℕ} (f : Fin n → T)
    (P : T → Prop) [DecidablePred P] (t : Fin n) (hP : ∀ r, P (f r) ↔ r = t) :
    (List.ofFn f).filter (fun x => decide (P x)) = [f t] := by
  classical
  have he : List.ofFn f = (List.finRange n).map f := by
    rw [← List.ofFn_id, List.map_ofFn]
    rfl
  rw [he, List.filter_map]
  have hp : (fun r => decide (P (f r))) = fun r => decide (r = t) := by
    funext r
    simp only [hP r]
  change ((List.finRange n).filter (fun r => decide (P (f r)))).map f = _
  rw [hp, List.filter_eq, List.count_eq_one_of_mem (List.nodup_finRange n) (by simp)]
  simp

lemma filter_padded (W : List Atom) (A : Atom) (n : ℕ) (P : Atom → Prop) [DecidablePred P]
    (hA : ¬ P A) :
    ((W.map (fun B => B :: List.replicate n A)).flatten).filter (fun B => decide (P B)) =
      W.filter (fun B => decide (P B)) := by
  induction W with
  | nil => simp
  | cons B W ih =>
    by_cases hb : P B <;> simp [List.filter_cons, List.filter_append, List.filter_replicate, hb, hA, ih]

namespace Requirement
variable {m : ℕ → ℕ} {hm : ∀ s, 0 < m s}

lemma witness_filter_of_padding_excluded (α : Cut → ℝ) (R : Requirement m hm)
    (P : Atom → Prop) [DecidablePred P] (hp : ¬ P R.localAtom) :
    (R.witness α).filter (fun B => decide (P B)) =
      (List.ofFn (R.baseAtom α)).filter (fun B => decide (P B)) := by
  have he : R.witness α = ((List.ofFn (R.baseAtom α)).map
      (fun B => B :: List.replicate (R.s + 1) R.localAtom)).flatten := by
    rw [List.map_ofFn]
    rfl
  rw [he]
  exact filter_padded _ _ _ P hp

/-- Membership in the next-cut difference, with the final layer treated uniformly. -/
def layerPredicate (R : Requirement m hm) (t : Fin (m R.s)) (B : Atom) : Prop :=
  B.label < R.cuts t ∧ ∀ u : Fin (m R.s), u.val = t.val + 1 → ¬ B.label < R.cuts u

lemma base_layer_iff (α : Cut → ℝ) (R : Requirement m hm) (r t : Fin (m R.s)) :
    R.layerPredicate t (R.baseAtom α r) ↔ r = t := by
  constructor
  · rintro ⟨hmem, hnext⟩
    have htr : t ≤ r := (R.baseLabel_in_layer r t).mp hmem
    by_contra hne
    have hlt : t < r := lt_of_le_of_ne htr (Ne.symm hne)
    let u : Fin (m R.s) := ⟨t.val + 1, by omega⟩
    have hu : u ≤ r := by change t.val + 1 ≤ r.val; omega
    exact hnext u rfl ((R.baseLabel_in_layer r u).mpr hu)
  · intro he
    subst r
    refine ⟨(R.baseLabel_in_layer t t).mpr le_rfl, ?_⟩
    intro u hu hmem
    have hut := (R.baseLabel_in_layer t u).mp hmem
    change u.val ≤ t.val at hut
    omega

open Classical in
lemma witness_layer_filter (α : Cut → ℝ) (R : Requirement m hm) (t : Fin (m R.s)) :
    (R.witness α).filter (fun B => decide (R.layerPredicate t B)) = [R.baseAtom α t] := by
  classical
  rw [witness_filter_of_padding_excluded α R (R.layerPredicate t) ?_]
  · exact filter_ofFn_singleton _ _ t (fun r => R.base_layer_iff α r t)
  · rintro ⟨hp, _⟩
    have hcut := R.cuts_le_root t
    have hpad := padding_above R.root (R.s + 1)
    exact not_lt_of_ge (hcut.trans hpad.le) hp

end Requirement
end BanachDensity1D.ProfileAux
