import BanachDensity1D.Nov1.Profile.Counting
import BanachDensity1D.Nov1.Profile.Construction

/-! # From witness atom words to actual population and ambient-volume counts. -/

namespace BanachDensity1D.ProfileAux
open Set

lemma weighted_filter (P : Atom → Prop) [DecidablePred P] (W : List Atom) :
    (W.map (fun A => if P A then A.size else 0)).sum =
      ((W.filter (fun A => decide (P A))).map Atom.size).sum := by
  induction W with
  | nil => rfl
  | cons A W ih =>
    by_cases h : P A <;> simp [h, ih]

open Classical in
lemma word_slice_count (A : ℕ → Atom) (E : Set ℤ) (P : Atom → Prop) [DecidablePred P]
    (hE : ∀ n x, x ∈ atomPoints A n → (x ∈ E ↔ P (A n)))
    (W : List Atom) (a : ℕ) (hW : ∀ r, ∀ hr : r < W.length, A (a + r) = W[r]) :
    (E ∩ Ico (position A a : ℤ) (position A (a + W.length) : ℤ)).ncard =
      (W.map (fun B => if P B then B.size else 0)).sum := by
  rw [atom_slice_count A E P hE (show a ≤ a + W.length by omega),
    Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, Finset.sum_range]
  calc
    (∑ i : Fin W.length, if P (A (a + i)) then (A (a + i)).size else 0) =
        ∑ i : Fin W.length, if P W[i.val] then W[i.val].size else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hW i.val i.isLt]
    _ = _ := Fin.sum_univ_fun_getElem W (fun B => if P B then B.size else 0)

namespace Staged
variable {m : ℕ → ℕ} {hm : ∀ s, 0 < m s}

lemma witness_atoms_at (α : Cut → ℝ) (f : ℕ → Requirement m hm) (k r : ℕ)
    (hr : r < ((f k).witness α).length) :
    atoms α f (Blocks.offset (blocks α f) k + r) = ((f k).witness α)[r] := by
  have hr' : r < (blocks α f k).length := by
    change r < ((f k).witness α ++ _).length
    simp only [List.length_append]
    omega
  rw [atoms_at α f k r hr']
  exact List.getElem_append_left hr

open Classical in
lemma witness_slice_count (α : Cut → ℝ) (f : ℕ → Requirement m hm) (k : ℕ)
    (E : Set ℤ) (P : Atom → Prop) [DecidablePred P]
    (hE : ∀ n x, x ∈ atomPoints (atoms α f) n → (x ∈ E ↔ P (atoms α f n))) :
    (E ∩ Ico (position (atoms α f) (Blocks.offset (blocks α f) k) : ℤ)
      (position (atoms α f) (Blocks.offset (blocks α f) k + ((f k).witness α).length) : ℤ)).ncard =
      (((f k).witness α).map (fun B => if P B then B.size else 0)).sum :=
  word_slice_count _ E P hE _ _ (witness_atoms_at α f k)

end Staged
end BanachDensity1D.ProfileAux
