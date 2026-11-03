import BanachDensity1D.Nov1.Profile.WordCounting

/-! # The exact periodic base/local-padding layout of a witness word. -/

namespace BanachDensity1D.ProfileAux.Requirement
open Set
variable {m : ℕ → ℕ} {hm : ∀ s, 0 < m s}

noncomputable def witnessAtom (α : Cut → ℝ) (R : Requirement m hm)
    (i : Fin (m R.s * (R.s + 2))) : Atom :=
  if i.val % (R.s + 2) = 0 then
    R.baseAtom α ⟨i.val / (R.s + 2), (Nat.div_lt_iff_lt_mul (by omega)).mpr i.isLt⟩
  else R.localAtom

lemma witness_as_ofFn (α : Cut → ℝ) (R : Requirement m hm) :
    R.witness α = List.ofFn (R.witnessAtom α) := by
  unfold witness
  rw [List.ofFn_mul]
  congr 1
  congr 1
  funext r
  rw [List.ofFn_succ]
  congr 1
  · have hd := Nat.mul_div_left r.val (show 0 < R.s + 2 by omega)
    simp [witnessAtom, hd]
  · have ht : (fun j : Fin (R.s + 1) => R.witnessAtom α
        ⟨r.val * (R.s + 2) + j.succ.val, by
          have hj : j.succ.val < R.s + 2 := by change j.val + 1 < R.s + 2; omega
          calc
            _ < r.val * (R.s + 2) + (R.s + 2) := Nat.add_lt_add_left hj _
            _ = (r.val + 1) * (R.s + 2) := by ring
            _ ≤ m R.s * (R.s + 2) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt r.isLt)⟩) = fun _ => R.localAtom := by
      funext j
      have hmod : (r.val * (R.s + 2) + (j.val + 1)) % (R.s + 2) = j.val + 1 := by
        rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      simp only [witnessAtom, Fin.val_mk, Fin.val_succ, hmod, ite_eq_right (by omega : j.val + 1 ≠ 0)]
    rw [ht, List.ofFn_const]

lemma witness_get (α : Cut → ℝ) (R : Requirement m hm) (r : ℕ)
    (hr : r < (R.witness α).length) :
    (R.witness α)[r] = R.witnessAtom α ⟨r, by rw [witness_length] at hr; exact hr⟩ := by
  simp only [witness_as_ofFn, List.getElem_ofFn]

end BanachDensity1D.ProfileAux.Requirement
