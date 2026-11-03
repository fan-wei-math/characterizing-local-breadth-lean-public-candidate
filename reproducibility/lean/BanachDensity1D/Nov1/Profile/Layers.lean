import BanachDensity1D.Nov1.Profile.Selection

/-! # The existing list layers indexed by the corresponding refinement cuts. -/

namespace BanachDensity1D.ProfileAux
open Set

noncomputable def layerAt {n : ℕ} (F : Fin n → Set ℤ) (r : Fin n) : Set ℤ :=
  if h : r.val + 1 < n then F r \ F ⟨r.val + 1, h⟩ else F r

lemma layers_cons_nonempty (L : Set ℤ) (H : List (Set ℤ)) (hne : H ≠ []) :
    layers (L :: H) = (L \ start H) :: layers H := by
  cases H with
  | nil => contradiction
  | cons M H => rfl

lemma layers_ofFn {n : ℕ} (F : Fin n → Set ℤ) :
    layers (List.ofFn F) = List.ofFn (layerAt F) := by
  induction n with
  | zero => simp [layers]
  | succ n ih =>
    cases n with
    | zero => simp [layers, List.ofFn_succ, layerAt]
    | succ n =>
      let tail : Fin (n + 1) → Set ℤ := fun r => F r.succ
      have he : List.ofFn F = F 0 :: List.ofFn tail := List.ofFn_succ
      have hne : List.ofFn tail ≠ [] := by simp
      rw [he, layers_cons_nonempty _ _ hne, ih]
      conv_rhs => rw [List.ofFn_succ]
      congr 1
      · simp [start, List.ofFn_succ, tail, layerAt]
      · congr 1
        funext r
        simp only [layerAt, tail, Fin.val_succ, Nat.add_lt_add_iff_right]
        split_ifs <;> rfl

namespace Requirement
variable {m : ℕ → ℕ} {hm : ∀ s, 0 < m s}

lemma layerPredicate_iff (R : Requirement m hm) (t : Fin (m R.s)) (B : Atom) :
    R.layerPredicate t B ↔
      if h : t.val + 1 < m R.s then
        B.label < R.cuts t ∧ ¬ B.label < R.cuts ⟨t.val + 1, h⟩
      else B.label < R.cuts t := by
  unfold layerPredicate
  split_ifs with h
  · constructor
    · rintro ⟨hp, hn⟩
      exact ⟨hp, hn ⟨t.val + 1, h⟩ rfl⟩
    · rintro ⟨hp, hn⟩
      refine ⟨hp, ?_⟩
      intro u hu
      have he : u = ⟨t.val + 1, h⟩ := Fin.ext hu
      simpa only [he] using hn
  · constructor
    · exact And.left
    · intro hp
      refine ⟨hp, ?_⟩
      intro u hu
      have := u.isLt
      omega

lemma atom_layer_membership (R : Requirement m hm) (A : ℕ → Atom)
    (t : Fin (m R.s)) {n : ℕ} {x : ℤ} (hx : x ∈ atomPoints A n) :
    x ∈ layerAt (fun r => language A (R.cuts r)) t ↔ R.layerPredicate t (A n) := by
  rw [R.layerPredicate_iff]
  unfold layerAt
  split_ifs with h
  · simp only [mem_sdiff, atom_language_iff A _ hx]
  · exact atom_language_iff A _ hx

end Requirement
end BanachDensity1D.ProfileAux
