import BanachDensity1D.Nov1.Profile.Atoms

/-! # Flattening finite nonempty stages without gaps or reordering. -/

namespace BanachDensity1D.ProfileAux
open Set

namespace Blocks
variable {T : Type*}

def offset (B : ℕ → List T) (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, (B i).length

lemma offset_zero (B : ℕ → List T) : offset B 0 = 0 := by simp [offset]
lemma offset_succ (B : ℕ → List T) (k : ℕ) :
    offset B (k + 1) = offset B k + (B k).length := by simp [offset, Finset.sum_range_succ]

lemma offset_strictMono (B : ℕ → List T) (hB : ∀ k, B k ≠ []) : StrictMono (offset B) := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [offset_succ]
  have := List.length_pos_iff.mpr (hB k)
  omega

lemma exists_block (B : ℕ → List T) (hB : ∀ k, B k ≠ []) (n : ℕ) :
    ∃ k, n < offset B (k + 1) := by
  refine ⟨n, ?_⟩
  have : n + 1 ≤ offset B (n + 1) := (offset_strictMono B hB).le_apply
  omega

noncomputable def owner (B : ℕ → List T) (hB : ∀ k, B k ≠ []) (n : ℕ) : ℕ :=
  Nat.find (exists_block B hB n)

lemma owner_bounds (B : ℕ → List T) (hB : ∀ k, B k ≠ []) (n : ℕ) :
    offset B (owner B hB n) ≤ n ∧ n < offset B (owner B hB n + 1) := by
  have hup := Nat.find_spec (exists_block B hB n)
  refine ⟨?_, hup⟩
  by_cases hz : owner B hB n = 0
  · simp [hz, offset_zero]
  · have hlo := Nat.find_min (exists_block B hB n) (show owner B hB n - 1 < owner B hB n by omega)
    have he : owner B hB n - 1 + 1 = owner B hB n := by omega
    rw [he] at hlo
    omega

noncomputable def flatten (B : ℕ → List T) (hB : ∀ k, B k ≠ []) (n : ℕ) : T :=
  (B (owner B hB n))[n - offset B (owner B hB n)]'(by
    have hb := owner_bounds B hB n
    rw [offset_succ] at hb
    omega)

lemma owner_of_block (B : ℕ → List T) (hB : ∀ k, B k ≠ []) (k r : ℕ)
    (hr : r < (B k).length) : owner B hB (offset B k + r) = k := by
  have hb := owner_bounds B hB (offset B k + r)
  have hk : offset B k ≤ offset B k + r ∧ offset B k + r < offset B (k + 1) := by
    rw [offset_succ]
    omega
  have hmono := offset_strictMono B hB
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlo | hhi
  · have hm := hmono.monotone (show owner B hB (offset B k + r) + 1 ≤ k by omega)
    omega
  · have hm := hmono.monotone (show k + 1 ≤ owner B hB (offset B k + r) by omega)
    omega

lemma flatten_at (B : ℕ → List T) (hB : ∀ k, B k ≠ []) (k r : ℕ)
    (hr : r < (B k).length) : flatten B hB (offset B k + r) = (B k)[r] := by
  unfold flatten
  simp only [owner_of_block B hB k r hr, Nat.add_sub_cancel_left]

end Blocks
end BanachDensity1D.ProfileAux
