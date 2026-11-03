import BanachDensityHD.ExactStatements.ProfileInternal

namespace Nov2Triangular
open Set
open BanachDensity1D.ProfileAux

-- Block k is E(0),...,E(k): exactly the printed triangular dovetail.
def tri : ℕ → ℕ
  | 0 => 0
  | k + 1 => tri k + (k + 1)

theorem two_tri (k : ℕ) : 2 * tri k = k * (k + 1) := by
  induction k with
  | zero => simp [tri]
  | succ k ih => simp only [tri]; nlinarith

theorem tri_formula (k : ℕ) : tri k = k * (k + 1) / 2 := by
  have h := two_tri k
  omega

def block {T : Type*} (E : ℕ → T) (k : ℕ) : List T :=
  (List.range (k + 1)).map E

theorem block_length {T : Type*} (E : ℕ → T) (k : ℕ) :
    (block E k).length = k + 1 := by simp [block]

theorem block_nonempty {T : Type*} (E : ℕ → T) (k : ℕ) : block E k ≠ [] := by
  intro h
  have hc := congrArg List.length h
  simp [block] at hc

noncomputable def schedule {T : Type*} (E : ℕ → T) : ℕ → T :=
  Blocks.flatten (block E) (block_nonempty E)

theorem offset_tri {T : Type*} (E : ℕ → T) (k : ℕ) :
    Blocks.offset (block E) k = tri k := by
  induction k with
  | zero => simp [Blocks.offset_zero, tri]
  | succ k ih => rw [Blocks.offset_succ, ih, block_length, tri]

theorem schedule_at {T : Type*} (E : ℕ → T) (k j : ℕ) (hj : j ≤ k) :
    schedule E (tri k + j) = E j := by
  have hr : j < (block E k).length := by rw [block_length]; omega
  unfold schedule
  rw [← offset_tri E k, Blocks.flatten_at (block E) (block_nonempty E) k j hr]
  simp [block]

theorem recurrent {T : Type*} (E : ℕ → T) (hE : Function.Surjective E) :
    ∀ R, ∀ B : ℕ, ∃ k ≥ B, schedule E k = R := by
  intro R B
  obtain ⟨j, rfl⟩ := hE R
  let r := max j B
  have hrj : j ≤ r := le_max_left _ _
  have hrB : B ≤ r := le_max_right _ _
  have htri : r ≤ tri r := by
    rw [← offset_tri E r]
    exact (Blocks.offset_strictMono (block E) (block_nonempty E)).le_apply
  exact ⟨tri r + j, by omega, schedule_at E r j hrj⟩

-- Positive manuscript indices: R_i occurs in row r at T_(r-1)+i.
theorem positive_occurrence {T : Type*} (E : ℕ → T) {i r : ℕ}
    (hi : 1 ≤ i) (hir : i ≤ r) :
    schedule E (tri (r - 1) + (i - 1)) = E (i - 1) := by
  exact schedule_at E (r - 1) (i - 1) (by omega)

-- Numerical statement for the actual triangular staged family, preserving
-- the existing stage model, midpoint labels, scales, and theorem chain.
theorem triangular_staged_bK_exact {m : ℕ → ℕ} {hm : ∀ s, 0 < m s}
    (α : Cut → ℝ) (hα : ∀ q, 0 ≤ α q ∧ α q ≤ 1 / 2)
    (E : ℕ → Requirement m hm) (hE : Function.Surjective E)
    (h : ℕ → ℝ) (hh : PositiveThreshold h)
    (hscale : ∀ s : ℕ, (s + 1 : ℝ) ≤ (m s : ℝ) / h ((2 + 2 * (s + 1)) * m s))
    (q : Cut) :
    BanachDensity1D.bK (range (language (Staged.atoms α (schedule E))))
      (language (Staged.atoms α (schedule E)) q) = α q := by
  exact BanachDensityHD.ExactStatements.staged_bK_exact α hα
    (schedule E) (recurrent E hE) h hh hscale q

#print axioms Nov2Triangular.recurrent
#print axioms Nov2Triangular.triangular_staged_bK_exact
end Nov2Triangular
