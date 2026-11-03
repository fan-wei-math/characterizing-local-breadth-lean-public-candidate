import BanachDensity1D.Nov1.Profile.Layout
import BanachDensity1D.Nov1.Profile.Surplus
import BanachDensity1D.Nov1.Profile.PaddedSums
import BanachDensity1D.Nov1.Profile.MechanicalSurplus

/-! # Arbitrary partial witness intervals: small parameters, equality, protection and invisibility. -/

namespace BanachDensity1D.ProfileAux.Requirement
open Set Finset
variable {m : ℕ → ℕ} {hm : ∀ s, 0 < m s}

noncomputable def baseContribution (α : Cut → ℝ) (R : Requirement m hm) (c : ℝ) (q : Cut) (r : ℕ) : ℝ :=
  if hr : r < m R.s then atomSurplus c q (R.baseAtom α ⟨r, hr⟩) else 0

noncomputable def witnessValue (α : Cut → ℝ) (R : Requirement m hm) (c : ℝ) (q : Cut) : ℕ → ℝ :=
  paddedValue (R.s + 2) (R.baseContribution α c q) (atomSurplus c q R.localAtom)

lemma witness_surplus_value (α : Cut → ℝ) (R : Requirement m hm) (c : ℝ) (q : Cut)
    {r : ℕ} (hr : r < (R.witness α).length) :
    atomSurplus c q (R.witness α)[r] = R.witnessValue α c q r := by
  have hquot : r / (R.s + 2) < m R.s := by
    apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
    simpa only [witness_length] using hr
  rw [witness_get]
  unfold witnessValue paddedValue
  by_cases hmod : r % (R.s + 2) = 0
  · simp only [witnessAtom, Fin.val_mk, ite_eq_left hmod, baseContribution, dite_eq_left hquot]
  · simp only [witnessAtom, Fin.val_mk, ite_eq_right hmod]

lemma baseContribution_lower (α : Cut → ℝ) (R : Requirement m hm) {c : ℝ}
    (h0 : 0 ≤ c) (hc : c ≤ 1 / 2) (q : Cut) (r : ℕ) :
    -c ≤ R.baseContribution α c q r := by
  unfold baseContribution
  split_ifs with hr
  · exact atom_surplus_lower h0 hc q _
  · linarith

lemma local_padding_surplus_nonneg (R : Requirement m hm) {c : ℝ} (hc : c ≤ 1 / 2) (q : Cut) :
    0 ≤ atomSurplus c q R.localAtom := pair_surplus_nonneg hc q _ rfl

lemma witness_small_lower (α : Cut → ℝ) (R : Requirement m hm) {c : ℝ}
    (h0 : 0 ≤ c) (hc : c ≤ 1 / 2) (q : Cut) {a b : ℕ} (hb : b ≤ (R.witness α).length) :
    -c * m R.s ≤ intervalSum (R.witnessValue α c q) a b := by
  have hG : 0 < R.s + 2 := by omega
  have hbound := padded_lower_count hG (R.baseContribution α c q)
    (R.local_padding_surplus_nonneg hc q) (R.baseContribution_lower α h0 hc q) a b
  have hceil : b ⌈/⌉ (R.s + 2) ≤ m R.s := by
    apply (ceilDiv_le_iff_le_mul hG).mpr
    simpa only [witness_length, Nat.mul_comm] using hb
  have hN : b ⌈/⌉ (R.s + 2) - a ⌈/⌉ (R.s + 2) ≤ m R.s := by omega
  have hNreal : ((b ⌈/⌉ (R.s + 2) - a ⌈/⌉ (R.s + 2) : ℕ) : ℝ) ≤ m R.s := by exact_mod_cast hN
  have hmul := mul_le_mul_of_nonneg_left hNreal h0
  exact (by nlinarith : -c * (m R.s : ℝ) ≤ -c * ((b ⌈/⌉ (R.s + 2) - a ⌈/⌉ (R.s + 2) : ℕ) : ℝ)).trans hbound

lemma base_surplus_included (α : Cut → ℝ) (R : Requirement m hm) (c : ℝ) (q : Cut)
    (r : Fin (m R.s)) (hr : R.baseLabel r < q) :
    atomSurplus c q (R.baseAtom α r) = mechanicalSurplus (α R.root) c r.val := by
  classical
  by_cases hp : isPair (α R.root) r.val <;>
    simp [atomSurplus, baseAtom, Atom.size, mechanicalSurplus, hr, hp] <;> ring

lemma root_value (α : Cut → ℝ) (R : Requirement m hm) (c : ℝ)
    {r : ℕ} (hr : r < (R.witness α).length) :
    R.witnessValue α c R.root r =
      if r % (R.s + 2) = 0 then mechanicalSurplus (α R.root) c (r / (R.s + 2)) else 0 := by
  have hquot : r / (R.s + 2) < m R.s := by
    apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
    simpa only [witness_length] using hr
  have hpad : atomSurplus c R.root R.localAtom = 0 := by
    have hp := not_lt_of_ge (padding_above R.root (R.s + 1)).le
    simp [atomSurplus, localAtom, hp]
  unfold witnessValue paddedValue
  rw [hpad]
  split_ifs with hmod
  · unfold baseContribution
    rw [dite_eq_left hquot]
    exact R.base_surplus_included α c R.root _ (R.baseLabel_below_root _)
  · rfl

lemma witness_root_lower (α : Cut → ℝ) (R : Requirement m hm) {c : ℝ}
    (hα0 : 0 ≤ α R.root) (hα1 : α R.root ≤ 1 / 2) (hc : c ≤ α R.root)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ (R.witness α).length) :
    -1 < intervalSum (R.witnessValue α c R.root) a b := by
  have he : intervalSum (R.witnessValue α c R.root) a b =
      intervalSum (fun n => if n % (R.s + 2) = 0 then mechanicalSurplus (α R.root) c (n / (R.s + 2)) else 0) a b := by
    apply sum_congr rfl
    intro r hr
    exact R.root_value α c (lt_of_lt_of_le (mem_Ico.mp hr).2 hb)
  rw [he]
  exact mechanical_stride_lower hα0 hα1 hc (by omega) hab

lemma witness_invisible (α : Cut → ℝ) (R : Requirement m hm) (c : ℝ) {i : ℕ}
    (hi : i < R.s + 1) (hiq : cutEnumeration i < R.root) :
    R.witnessValue α c (cutEnumeration i) = fun _ => 0 := by
  have hbase : R.baseContribution α c (cutEnumeration i) = fun _ => 0 := by
    funext r
    unfold baseContribution
    split_ifs with hr
    · exact ite_eq_right (R.base_invisible α hi hiq ⟨r, hr⟩)
    · rfl
  have hpad : atomSurplus c (cutEnumeration i) R.localAtom = 0 :=
    ite_eq_right (R.padding_invisible hiq.le)
  funext n
  unfold witnessValue paddedValue
  rw [hbase, hpad]
  split_ifs <;> rfl

lemma witness_protected_lower (α : Cut → ℝ) (R : Requirement m hm) {c : ℝ}
    (h0 : 0 ≤ c) (hc : c ≤ 1 / 2) {i : ℕ}
    (hi : i < R.s + 1) (hiq : R.root < cutEnumeration i)
    (hpad : c ≤ (R.s + 1 : ℝ) * (1 - 2 * c)) {a b : ℕ} (hab : a ≤ b) :
    -c ≤ intervalSum (R.witnessValue α c (cutEnumeration i)) a b := by
  have hp : atomSurplus c (cutEnumeration i) R.localAtom = 1 - 2 * c := by
    rw [atomSurplus, ite_eq_left (R.padding_protected hi hiq)]
    change 1 - c * 2 = 1 - 2 * c
    ring
  unfold witnessValue
  rw [hp]
  apply padded_uniform_lower (by omega) _ h0 (by linarith) (R.baseContribution_lower α h0 hc _)
    (a := a) (b := b) ?_ hab
  simpa only [show R.s + 2 - 1 = R.s + 1 by omega, Nat.cast_add, Nat.cast_one] using hpad

end BanachDensity1D.ProfileAux.Requirement
