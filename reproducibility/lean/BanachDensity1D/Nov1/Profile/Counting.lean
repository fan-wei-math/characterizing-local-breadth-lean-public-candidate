import BanachDensity1D.Nov1.Profile.Atoms

/-! # Exact integer counts over a finite interval of whole atoms. -/

namespace BanachDensity1D.ProfileAux
open Set

open Classical in
/-- A membership property constant on each atom can be counted by its atom sizes. -/
lemma atom_slice_count (A : ℕ → Atom) (E : Set ℤ) (P : Atom → Prop) [DecidablePred P]
    (hE : ∀ n x, x ∈ atomPoints A n → (x ∈ E ↔ P (A n)))
    {a b : ℕ} (hab : a ≤ b) :
    (E ∩ Ico (position A a : ℤ) (position A b : ℤ)).ncard =
      ∑ n ∈ Finset.Ico a b, if P (A n) then (A n).size else 0 := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | @succ b hab ih =>
    have hpos : (position A a : ℤ) ≤ position A b := by
      exact_mod_cast (position_strictMono A).monotone hab
    have hstep : (position A b : ℤ) ≤ position A (b + 1) := by
      exact_mod_cast (position_strictMono A).monotone (Nat.le_succ b)
    have hspl : E ∩ Ico (position A a : ℤ) (position A (b + 1) : ℤ) =
        (E ∩ Ico (position A a : ℤ) (position A b : ℤ)) ∪ (E ∩ atomPoints A b) := by
      ext x
      constructor
      · rintro ⟨hx, hlo, hup⟩
        by_cases hb : x < (position A b : ℤ)
        · exact Or.inl ⟨hx, hlo, hb⟩
        · exact Or.inr ⟨hx, le_of_not_gt hb, hup⟩
      · rintro (⟨hx, hlo, hup⟩ | ⟨hx, hlo, hup⟩)
        · exact ⟨hx, hlo, lt_of_lt_of_le hup hstep⟩
        · exact ⟨hx, hpos.trans hlo, hup⟩
    have hd : Disjoint (E ∩ Ico (position A a : ℤ) (position A b : ℤ)) (E ∩ atomPoints A b) := by
      apply disjoint_left.mpr
      rintro x ⟨_, _, hx⟩ ⟨_, hx', _⟩
      omega
    have hf1 : (E ∩ Ico (position A a : ℤ) (position A b : ℤ)).Finite :=
      (finite_Ico _ _).subset inter_subset_right
    have hf2 : (E ∩ atomPoints A b).Finite := (finite_Ico _ _).subset inter_subset_right
    have hcount : (E ∩ atomPoints A b).ncard = if P (A b) then (A b).size else 0 := by
      by_cases hb : P (A b)
      · have he : E ∩ atomPoints A b = atomPoints A b := by
          apply inter_eq_right.mpr
          intro x hx
          exact (hE b x hx).mpr hb
        rw [he, atomPoints_card, ite_eq_left hb]
      · have he : E ∩ atomPoints A b = ∅ := by
          apply eq_empty_of_forall_notMem
          rintro x ⟨hxE, hx⟩
          exact hb ((hE b x hx).mp hxE)
        rw [he, ncard_empty, ite_eq_right hb]
    rw [hspl, ncard_union_eq hd hf1 hf2, ih, hcount, Finset.sum_Ico_succ_top hab]

open Classical in
/-- Relative-interval target counts are the sizes of precisely the selected atoms. -/
lemma language_slice_count (A : ℕ → Atom) (q : Cut) {a b : ℕ} (hab : a ≤ b) :
    (language A q ∩ Ico (position A a : ℤ) (position A b : ℤ)).ncard =
      ∑ n ∈ Finset.Ico a b, if (A n).label < q then (A n).size else 0 :=
  atom_slice_count A (language A q) (fun B => B.label < q)
    (fun n x hx => atom_language_iff A q hx) hab

end BanachDensity1D.ProfileAux
