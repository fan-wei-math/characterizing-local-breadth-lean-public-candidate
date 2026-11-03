import BanachDensity1D.Nov1.Profile.UniformWitness
import BanachDensity1D.Nov1.Profile.Construction
import BanachDensity1D.Nov1.Profile.LateBlocks

/-! # Uniform surplus on every atom interval in the actual infinite staged construction. -/

namespace BanachDensity1D.ProfileAux
open Set Finset

lemma sum_word_values {T : Type*} (W : List T) (F : T → ℝ) (a : ℕ) (g : ℕ → ℝ)
    (hg : ∀ r, ∀ hr : r < W.length, g (a + r) = F W[r]) :
    intervalSum g a (a + W.length) = (W.map F).sum := by
  rw [intervalSum, sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, sum_range]
  calc
    _ = ∑ r : Fin W.length, F W[r.val] := by
      apply sum_congr rfl
      intro r hr
      exact hg r.val r.isLt
    _ = _ := Fin.sum_univ_fun_getElem W F

namespace Requirement
variable {m : ℕ → ℕ} {hm : ∀ s, 0 < m s}

lemma stage_suffix_pair (α : Cut → ℝ) (R : Requirement m hm) (k r : ℕ)
    (hlo : (R.witness α).length ≤ r) (hr : r < (R.stage α k).length) :
    ((R.stage α k)[r]).pair = true := by
  unfold stage at hr ⊢
  simp only [List.getElem_append_right hlo, List.getElem_replicate]


lemma stage_interval_lower (α : Cut → ℝ) (R : Requirement m hm) {c C : ℝ}
    (hc : c ≤ 1 / 2) (hC : 0 ≤ C) (q : Cut)
    (hw : ∀ a b : ℕ, a ≤ b → b ≤ (R.witness α).length →
      -C ≤ intervalSum (R.witnessValue α c q) a b)
    (k : ℕ) (g : ℕ → ℝ)
    (hg : ∀ r, ∀ hr : r < (R.stage α k).length, g r = atomSurplus c q (R.stage α k)[r])
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ (R.stage α k).length) :
    -C ≤ intervalSum g a b := by
  have hwl : (R.witness α).length ≤ (R.stage α k).length := by simp [stage]
  have hpref {a b : ℕ} (hab : a ≤ b) (hb : b ≤ (R.witness α).length) :
      -C ≤ intervalSum g a b := by
    have he : intervalSum g a b = intervalSum (R.witnessValue α c q) a b := by
      apply sum_congr rfl
      intro r hr
      have hrw : r < (R.witness α).length := lt_of_lt_of_le (mem_Ico.mp hr).2 hb
      rw [hg r (hrw.trans_le hwl)]
      simp only [stage, List.getElem_append_left hrw]
      exact R.witness_surplus_value α c q hrw
    rw [he]
    exact hw a b hab hb
  have htail {a b : ℕ} (ha : (R.witness α).length ≤ a) (hb : b ≤ (R.stage α k).length) :
      0 ≤ intervalSum g a b := by
    apply sum_nonneg
    intro r hr
    have hrl : (R.witness α).length ≤ r := ha.trans (mem_Ico.mp hr).1
    have hru : r < (R.stage α k).length := lt_of_lt_of_le (mem_Ico.mp hr).2 hb
    rw [hg r hru]
    exact pair_surplus_nonneg hc q _ (R.stage_suffix_pair α k r hrl hru)
  by_cases hbw : b ≤ (R.witness α).length
  · exact hpref hab hbw
  · by_cases haw : (R.witness α).length ≤ a
    · exact (by linarith : -C ≤ 0).trans (htail haw hb)
    · have hleft := hpref (a := a) (b := (R.witness α).length) (by omega) le_rfl
      have hright := htail (a := (R.witness α).length) (b := b) le_rfl hb
      have he := intervalSum_split g (show a ≤ (R.witness α).length by omega)
        (show (R.witness α).length ≤ b by omega)
      linarith

end Requirement

namespace Staged
variable {m : ℕ → ℕ} {hm : ∀ s, 0 < m s}

/-- Every atom interval has bounded negative c-surplus. The bound includes the
finite initial prefix and is independent of interval length and history depth. -/
theorem global_atom_surplus (α : Cut → ℝ) (hα : ∀ q, 0 ≤ α q ∧ α q ≤ 1 / 2)
    (f : ℕ → Requirement m hm) (i : ℕ) {c : ℝ}
    (h0 : 0 ≤ c) (hc : c < α (cutEnumeration i)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ a b : ℕ, a ≤ b →
      -D ≤ intervalSum (fun n => atomSurplus c (cutEnumeration i) (atoms α f n)) a b := by
  have hc1 : c < 1 / 2 := hc.trans_le (hα (cutEnumeration i)).2
  obtain ⟨C, hC, hW⟩ := uniform_witness_lower hm α hα i h0 hc
  let o := Blocks.offset (blocks α f)
  let g : ℕ → ℝ := fun n => atomSurplus c (cutEnumeration i) (atoms α f n)
  have ho : StrictMono o := Blocks.offset_strictMono _ (blocks_nonempty α f)
  have hz : o 0 = 0 := Blocks.offset_zero _
  have hlocal : ∀ k a b, o k ≤ a → a ≤ b → b ≤ o (k + 1) → -C ≤ intervalSum g a b := by
    intro k a b ha hab hb
    let a' := a - o k
    let b' := b - o k
    have hb' : b' ≤ ((f k).stage α k).length := by
      have he := Blocks.offset_succ (blocks α f) k
      change o (k + 1) = o k + ((f k).stage α k).length at he
      dsimp [b']
      omega
    have hab' : a' ≤ b' := Nat.sub_le_sub_right hab _
    have h := (f k).stage_interval_lower α hc1.le hC (cutEnumeration i)
      (hW (f k)) k (fun r => g (o k + r))
      (fun r hr => congrArg (atomSurplus c (cutEnumeration i)) (atoms_at α f k r hr)) hab' hb'
    have he : intervalSum (fun r => g (o k + r)) a' b' = intervalSum g a b := by
      unfold intervalSum
      have hs := sum_Ico_add g a' b' (o k)
      simpa only [a', b', Nat.sub_add_cancel ha, Nat.sub_add_cancel (ha.trans hab)] using hs
    rwa [he] at h
  have hp : 0 < 1 - 2 * c := by linarith
  obtain ⟨N, hN⟩ := exists_nat_ge (c / (1 - 2 * c))
  let K := max i N
  have hwhole : ∀ k ≥ K, 0 ≤ intervalSum g (o k) (o (k + 1)) := by
    intro k hk
    have hi : i < k + 1 := by have := le_max_left i N; dsimp [K] at hk; omega
    have hNk : N ≤ k + 1 := by have := le_max_right i N; dsimp [K] at hk; omega
    have hpad : c ≤ (k + 1 : ℝ) * (1 - 2 * c) := by
      apply (div_le_iff₀ hp).mp
      exact hN.trans (by exact_mod_cast hNk)
    have he : intervalSum g (o k) (o (k + 1)) = surplus c (cutEnumeration i) ((f k).stage α k) := by
      have hlen := Blocks.offset_succ (blocks α f) k
      change o (k + 1) = o k + ((f k).stage α k).length at hlen
      rw [hlen]
      exact sum_word_values _ (atomSurplus c (cutEnumeration i)) _ g
        (fun r hr => congrArg (atomSurplus c (cutEnumeration i)) (atoms_at α f k r hr))
    rw [he]
    exact (f k).complete_stage_nonneg α h0 hc1.le hi hpad
  exact eventual_block_surplus g ho hz hC hlocal K hwhole

end Staged
end BanachDensity1D.ProfileAux
