import BanachDensity1D.Nov1.Balanced

/-! # Mechanical singleton/pair words for prescribed profile values.

This is only the finite-word portion of `prop:profile-realization` in the
read-only Nov. 1 manuscript. It does not assert existence of the staged family.
-/

namespace BanachDensity1D.ProfileAux
open Set Filter
open FullRangeAux

/-- Pair frequency needed for point density alpha: a pair uses one extra point. -/
noncomputable def theta (α : ℝ) : ℝ := α / (1 - α)

lemma theta_mem {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2) :
    0 ≤ theta α ∧ theta α ≤ 1 := by
  have hd : 0 < 1 - α := by linarith
  constructor
  · exact div_nonneg h0 hd.le
  · apply (div_le_one hd).mpr
    linarith

/-- The r-th atom is a pair exactly at a mechanical floor increment. -/
def isPair (α : ℝ) (r : ℕ) : Prop := r ∈ coreNat (theta α)

/-- Number of pairs in m atoms, as prescribed by the manuscript. -/
noncomputable def pairs (α : ℝ) (m : ℕ) : ℕ := ⌊(m : ℝ) * theta α⌋₊

/-- Each atom contributes one point and each pair contributes one extra point. -/
noncomputable def points (α : ℝ) (m : ℕ) : ℕ := m + pairs α m

open Classical in
lemma pairs_count {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2) (m : ℕ) :
    ((Finset.range m).filter (isPair α)).card = pairs α m :=
  prefix_count (theta_mem h0 h1).1 (theta_mem h0 h1).2 m

lemma pairs_le {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2) (m : ℕ) :
    pairs α m ≤ m := by
  have hθ := theta_mem h0 h1
  have hle : (m : ℝ) * theta α ≤ m := by nlinarith
  exact (Nat.floor_le (mul_nonneg (Nat.cast_nonneg m) hθ.1)).trans hle |> fun h => by exact_mod_cast h

lemma points_bounds {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2) (m : ℕ) :
    m ≤ points α m ∧ points α m ≤ 2 * m := by
  dsimp [points]
  have := pairs_le h0 h1 m
  omega

lemma whole_surplus_nonpos {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2) (m : ℕ) :
    (pairs α m : ℝ) - α * points α m ≤ 0 := by
  have hθ := (theta_mem h0 h1).1
  have hfloor := Nat.floor_le (mul_nonneg (Nat.cast_nonneg m) hθ)
  have hd : 0 < 1 - α := by linarith
  have he : (1 - α) * theta α = α := by dsimp [theta]; field_simp
  have hm : (1 - α) * (pairs α m : ℝ) ≤ α * m := by
    dsimp [pairs]
    nlinarith
  dsimp [points]
  push_cast
  linarith

lemma whole_ratio_le {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2)
    {m : ℕ} (hm : 0 < m) : (pairs α m : ℝ) / points α m ≤ α := by
  have hp : (0 : ℝ) < points α m := by exact_mod_cast lt_of_lt_of_le hm (points_bounds h0 h1 m).1
  apply (div_le_iff₀ hp).mpr
  linarith [whole_surplus_nonpos h0 h1 m]

open Classical in
/-- Every consecutive atom subword has alpha-surplus greater than -1. -/
lemma local_surplus {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2)
    {a b : ℕ} (hab : a ≤ b) :
    let p := ((Finset.Ico a b).filter (isPair α)).card
    (p : ℝ) - α * ((b : ℝ) - a + p) > -1 := by
  dsimp
  have hθ := theta_mem h0 h1
  have hdis := (abs_lt.mp (interval_discrepancy hθ.1 hθ.2 hab)).1
  change -1 < (((Finset.Ico a b).filter (isPair α)).card : ℝ) -
    theta α * ((b : ℝ) - a) at hdis
  have hd : 0 < 1 - α := by linarith
  have he : (1 - α) * theta α = α := by dsimp [theta]; field_simp
  have hmul := (mul_lt_mul_of_pos_left hdis hd)
  nlinarith

lemma zero_pairs (m : ℕ) : pairs 0 m = 0 := by simp [pairs, theta]
lemma half_pairs (m : ℕ) : pairs (1 / 2) m = m := by
  have he : theta (1 / 2) = 1 := by norm_num [theta]
  unfold pairs
  rw [he]
  simp

end BanachDensity1D.ProfileAux
