import BanachDensityHD.ExactStatements.CopyForest
import Mathlib.Data.Nat.Nth

namespace BanachDensityHD.ExactStatements
open Set
open scoped Classical

/-- Every countable nonempty family has a bijective enumeration of all its
positive accuracy copies, with increasing accuracy order for each language. -/
theorem exists_copy_enumeration {d : ℕ} {X : Set (Set (Pt d))} (hX : LangClass X) :
    ∃ (lab : ℕ → Set (Pt d)) (acc : ℕ → ℕ),
      (∀ j, lab j ∈ X) ∧ (∀ j, 1 ≤ acc j) ∧
      (∀ i j, lab i = lab j → acc i = acc j → i = j) ∧
      (∀ L ∈ X, ∀ k, 1 ≤ k → ∃ i, lab i = L ∧ acc i = k) ∧
      (∀ i j, lab i = lab j → acc i < acc j → i < j) := by
  have : Countable X := hX.countable.to_subtype
  obtain ⟨idx, hidx⟩ := exists_injective_nat X
  let p : ℕ → Prop := fun k => ∃ L : X, ∃ m, 1 ≤ m ∧ Nat.pair (idx L) m = k
  obtain ⟨L0, hL0⟩ := hX.nonempty
  have hinf : (Set.ofPred p).Infinite := by
    have hi : Function.Injective (fun m : ℕ => Nat.pair (idx ⟨L0, hL0⟩) (m + 1)) := by
      intro a b h
      have := (Nat.pair_eq_pair.1 h).2
      omega
    exact Set.infinite_of_injective_forall_mem hi
      (fun m => ⟨⟨L0, hL0⟩, m + 1, by omega, rfl⟩)
  have hmem : ∀ v, p (Nat.nth p v) := Nat.nth_mem_of_infinite hinf
  let Lv : ℕ → X := fun v => (hmem v).choose
  let cv : ℕ → ℕ := fun v => (hmem v).choose_spec.choose
  have hcv : ∀ v, 1 ≤ cv v ∧ Nat.pair (idx (Lv v)) (cv v) = Nat.nth p v :=
    fun v => (hmem v).choose_spec.choose_spec
  have hsm := Nat.nth_strictMono hinf
  refine ⟨fun v => (Lv v).1, cv, fun v => (Lv v).2, fun v => (hcv v).1, ?_, ?_, ?_⟩
  · intro i j hL hc
    have he : Lv i = Lv j := Subtype.ext hL
    apply Nat.nth_injective hinf
    rw [← (hcv i).2, ← (hcv j).2, he, hc]
  · intro L hL k hk
    have hpk : p (Nat.pair (idx ⟨L, hL⟩) k) := ⟨⟨L, hL⟩, k, hk, rfl⟩
    refine ⟨Nat.count p (Nat.pair (idx ⟨L, hL⟩) k), ?_⟩
    have h := (hcv (Nat.count p (Nat.pair (idx ⟨L, hL⟩) k))).2
    rw [Nat.nth_count hpk] at h
    obtain ⟨h1, h2⟩ := Nat.pair_eq_pair.1 h
    exact ⟨congrArg Subtype.val (hidx h1), h2⟩
  · intro i j hL hc
    have he : Lv i = Lv j := Subtype.ext hL
    apply hsm.lt_iff_lt.1
    rw [← (hcv i).2, ← (hcv j).2, he]
    exact Nat.pair_lt_pair_right _ hc

end BanachDensityHD.ExactStatements
