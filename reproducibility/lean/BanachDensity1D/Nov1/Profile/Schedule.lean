import BanachDensity1D.Nov1.Profile.Scales

/-! # A repeated countable schedule, used by the profile witness stages. -/

namespace BanachDensity1D.ProfileAux
open Set

/-- Any countable nonempty requirements can be scheduled beyond every stage. -/
theorem repeated_schedule (T : Type*) [Countable T] [Nonempty T] :
    ∃ f : ℕ → T, ∀ t : T, ∀ B : ℕ, ∃ k ≥ B, f k = t := by
  classical
  letI : Encodable T := Encodable.ofCountable T
  let t0 : T := Classical.choice (inferInstance : Nonempty T)
  let f : ℕ → T := fun k => (Encodable.decode (α := T) (Nat.unpair k).1).getD t0
  refine ⟨f, ?_⟩
  intro t B
  refine ⟨Nat.pair (Encodable.encode t) B, Nat.right_le_pair _ _, ?_⟩
  simp [f, Nat.unpair_pair, Encodable.encodek]

/-- Choose successively larger scales, rather than assuming the choices are monotone. -/
theorem increasing_scales {h : ℕ → ℝ} (hh : PositiveThreshold h) :
    ∃ m : ℕ → ℕ, StrictMono m ∧ (∀ s, s + 1 ≤ m s) ∧
      ∀ s : ℕ, (s + 1 : ℝ) ≤ (m s : ℝ) / h ((2 + 2 * (s + 1)) * m s) := by
  classical
  choose next hn hnratio using fun s L =>
    scale_exists hh (2 + 2 * (s + 1)) L (s + 1) (by omega)
  let m : ℕ → ℕ := fun s => Nat.rec (next 0 1) (fun i prev => next (i + 1) (prev + 1)) s
  have hm0 : m 0 = next 0 1 := rfl
  have hmsucc : ∀ s, m (s + 1) = next (s + 1) (m s + 1) := fun _ => rfl
  have hstrict : StrictMono m := by
    apply strictMono_nat_of_lt_succ
    intro s
    rw [hmsucc]
    have := hn (s + 1) (m s + 1)
    omega
  refine ⟨m, hstrict, ?_, ?_⟩
  · intro s
    have hstart : 1 ≤ m 0 := by rw [hm0]; exact le_trans (le_max_left _ _) (hn 0 1)
    have hle : s + m 0 ≤ m s := by simpa only [Nat.add_zero] using hstrict.add_le_nat s 0
    omega
  · intro s
    cases s with
    | zero => simpa only [hm0, Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add] using hnratio 0 1
    | succ s => simpa only [hmsucc, Nat.cast_add, Nat.cast_one] using hnratio (s + 1) (m s + 1)

end BanachDensity1D.ProfileAux
