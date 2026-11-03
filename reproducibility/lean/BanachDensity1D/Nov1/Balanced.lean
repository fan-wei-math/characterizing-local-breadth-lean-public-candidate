import BanachDensity1D.PriorZeroValue

/-! # Balanced mechanical cores for the Nov. 1 realization constructions.

All definitions and proofs here are new; the verified library is unchanged.
Natural floor agrees with integer floor on the nonnegative arguments used here.
-/

namespace BanachDensity1D.FullRangeAux
open Set Filter

/-- The balanced core in nonnegative integer coordinates. -/
def coreNat (ρ : ℝ) : Set ℕ :=
  {j | ⌊((j + 1 : ℕ) : ℝ) * ρ⌋₊ = ⌊(j : ℝ) * ρ⌋₊ + 1}

/-- The same core embedded in Z. -/
def core (ρ : ℝ) : Set ℤ := {x | 0 ≤ x ∧ x.toNat ∈ coreNat ρ}

lemma floor_step {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (j : ℕ) :
    ⌊((j + 1 : ℕ) : ℝ) * ρ⌋₊ = ⌊(j : ℝ) * ρ⌋₊ ∨
    ⌊((j + 1 : ℕ) : ℝ) * ρ⌋₊ = ⌊(j : ℝ) * ρ⌋₊ + 1 := by
  have hlo : ⌊(j : ℝ) * ρ⌋₊ ≤ ⌊((j + 1 : ℕ) : ℝ) * ρ⌋₊ :=
    Nat.floor_mono (by push_cast; nlinarith)
  have hup : ⌊((j + 1 : ℕ) : ℝ) * ρ⌋₊ ≤ ⌊(j : ℝ) * ρ⌋₊ + 1 := by
    calc
      _ ≤ ⌊(j : ℝ) * ρ + 1⌋₊ := Nat.floor_mono (by push_cast; nlinarith)
      _ = _ := Nat.floor_add_one (by positivity)
  omega

open Classical in
lemma prefix_count {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (N : ℕ) :
    ((Finset.range N).filter (fun j => j ∈ coreNat ρ)).card = ⌊(N : ℝ) * ρ⌋₊ := by
  classical
  induction N with
  | zero => simp
  | succ N ih =>
    have hnot : N ∉ (Finset.range N).filter (fun j => j ∈ coreNat ρ) := by simp
    have hs := floor_step hρ0 hρ1 N
    by_cases h : N ∈ coreNat ρ
    · have he : ⌊((N + 1 : ℕ) : ℝ) * ρ⌋₊ = ⌊(N : ℝ) * ρ⌋₊ + 1 := h
      simpa [Finset.range_add_one, Finset.filter_insert, h, hnot, ih] using he.symm
    · have he : ⌊((N + 1 : ℕ) : ℝ) * ρ⌋₊ = ⌊(N : ℝ) * ρ⌋₊ := by
        change ¬ _ = _ at h
        omega
      simpa [Finset.range_add_one, Finset.filter_insert, h, ih] using he.symm

open Classical in
lemma interval_count {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {a b : ℕ} (hab : a ≤ b) :
    (((Finset.Ico a b).filter (fun j => j ∈ coreNat ρ)).card : ℝ) =
      (⌊(b : ℝ) * ρ⌋₊ : ℝ) - ⌊(a : ℝ) * ρ⌋₊ := by
  classical
  have hs := Finset.sum_range_add_sum_Ico (fun j => if j ∈ coreNat ρ then (1 : ℝ) else 0) hab
  simp only [Finset.sum_boole] at hs
  rw [prefix_count hρ0 hρ1 a, prefix_count hρ0 hρ1 b] at hs
  linarith

open Classical in
/-- The strict interval discrepancy bound from the manuscript, including empty intervals. -/
theorem interval_discrepancy {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {a b : ℕ}
    (hab : a ≤ b) :
    |(((Finset.Ico a b).filter (fun j => j ∈ coreNat ρ)).card : ℝ) -
      ρ * ((b : ℝ) - a)| < 1 := by
  rw [interval_count hρ0 hρ1 hab, abs_lt]
  have ha0 : 0 ≤ (a : ℝ) * ρ := by positivity
  have hb0 : 0 ≤ (b : ℝ) * ρ := by positivity
  have ha := Nat.floor_le ha0
  have ha' := Nat.lt_floor_add_one ((a : ℝ) * ρ)
  have hb := Nat.floor_le hb0
  have hb' := Nat.lt_floor_add_one ((b : ℝ) * ρ)
  constructor <;> nlinarith

lemma complement_infinite {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    (coreNat ρ)ᶜ.Infinite := by
  classical
  intro hf
  obtain ⟨B, hB⟩ := hf.bddAbove
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / (1 - ρ))
  have hpos : 0 < 1 - ρ := by linarith
  have hM' : 1 < (M : ℝ) * (1 - ρ) := (div_lt_iff₀ hpos).mp hM
  have hall : (Finset.Ico (B + 1) (B + 1 + M)).filter (fun j => j ∈ coreNat ρ) =
      Finset.Ico (B + 1) (B + 1 + M) := by
    apply Finset.filter_eq_self.mpr
    intro j hj
    have hlo := (Finset.mem_Ico.mp hj).1
    by_contra hn
    have := hB hn
    omega
  have hd := interval_discrepancy hρ0 hρ1.le (Nat.le_add_right (B + 1) M)
  rw [hall, Nat.card_Ico] at hd
  simp only [Nat.add_sub_cancel_left] at hd
  rw [abs_lt] at hd
  push_cast at hd
  nlinarith [hd.2]

/-- Increasing enumeration of the complement of the common core. -/
noncomputable def phi (ρ : ℝ) : ℕ → ℕ := Nat.nth (fun j => j ∉ coreNat ρ)

lemma phi_strictMono {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) : StrictMono (phi ρ) :=
  Nat.nth_strictMono (complement_infinite hρ0 hρ1)

lemma phi_not_mem {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (j : ℕ) :
    phi ρ j ∉ coreNat ρ := Nat.nth_mem_of_infinite (complement_infinite hρ0 hρ1) j

lemma phi_range {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    range (phi ρ) = (coreNat ρ)ᶜ := Nat.range_nth_of_infinite (complement_infinite hρ0 hρ1)

end BanachDensity1D.FullRangeAux
