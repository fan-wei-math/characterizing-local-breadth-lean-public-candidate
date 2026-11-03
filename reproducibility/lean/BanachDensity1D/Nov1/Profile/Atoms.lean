import BanachDensity1D.Nov1.Profile.Words

/-! # Consecutive labelled singleton/pair atoms and rational-cut languages. -/

namespace BanachDensity1D.ProfileAux
open Set

/-- Rational labels lie in the manuscript's open unit interval. -/
abbrev Cut := {q : ℚ // 0 < q ∧ q < 1}

instance : Infinite Cut := Set.Ioo.infinite (show (0 : ℚ) < 1 by norm_num)

/-- Fix a bijective enumeration, so arbitrary alpha_i can be assigned without duplication. -/
noncomputable def cutEnumeration : ℕ ≃ Cut := Classical.choice inferInstance

/-- A singleton or a pair, with a common label for every point of the atom. -/
structure Atom where
  pair : Bool
  label : Cut

namespace Atom

def size (A : Atom) : ℕ := if A.pair then 2 else 1
lemma size_bounds (A : Atom) : 1 ≤ A.size ∧ A.size ≤ 2 := by
  unfold size
  split <;> omega

end Atom

/-- Left endpoints of successive atoms, starting at zero. -/
def position (A : ℕ → Atom) (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, (A i).size

lemma position_zero (A : ℕ → Atom) : position A 0 = 0 := by simp [position]
lemma position_succ (A : ℕ → Atom) (n : ℕ) :
    position A (n + 1) = position A n + (A n).size := by
  simp [position, Finset.sum_range_succ]

lemma position_strictMono (A : ℕ → Atom) : StrictMono (position A) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [position_succ]
  have := (A n).size_bounds
  omega

lemma index_le_position (A : ℕ → Atom) (n : ℕ) : n ≤ position A n :=
  (position_strictMono A).le_apply

/-- Actual integer points in one atom. -/
def atomPoints (A : ℕ → Atom) (n : ℕ) : Set ℤ :=
  Ico (position A n : ℤ) (position A (n + 1) : ℤ)

lemma atomPoints_nonempty (A : ℕ → Atom) (n : ℕ) : (atomPoints A n).Nonempty := by
  refine ⟨position A n, le_rfl, ?_⟩
  exact_mod_cast position_strictMono A (show n < n + 1 by omega)

lemma atomPoints_card (A : ℕ → Atom) (n : ℕ) : (atomPoints A n).ncard = (A n).size := by
  rw [atomPoints, Set.ncard_Ico, Int.card_Ico, position_succ]
  omega

lemma atomPoints_disjoint (A : ℕ → Atom) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (atomPoints A i) (atomPoints A j) := by
  apply disjoint_left.mpr
  rintro x ⟨hlo, hup⟩ ⟨hlo', hup'⟩
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · have hp : (position A (i + 1) : ℤ) ≤ position A j := by
      exact_mod_cast (position_strictMono A).monotone (show i + 1 ≤ j by omega)
    omega
  · have hp : (position A (j + 1) : ℤ) ≤ position A i := by
      exact_mod_cast (position_strictMono A).monotone (show j + 1 ≤ i by omega)
    omega

/-- Every nonnegative integer belongs to exactly one atom. -/
lemma atom_partition (A : ℕ → Atom) {x : ℤ} (hx : 0 ≤ x) :
    ∃! n : ℕ, x ∈ atomPoints A n := by
  have hex : ∃ n, x.toNat < position A (n + 1) := by
    refine ⟨x.toNat, ?_⟩
    have := index_le_position A (x.toNat + 1)
    omega
  let n := Nat.find hex
  have hup : x.toNat < position A (n + 1) := Nat.find_spec hex
  have hlo : position A n ≤ x.toNat := by
    by_cases hn : n = 0
    · simp [hn, position_zero]
    · have hprev := Nat.find_min hex (show n - 1 < n by omega)
      have he : n - 1 + 1 = n := by omega
      rw [he] at hprev
      omega
  refine ⟨n, ⟨by omega, by omega⟩, ?_⟩
  intro j hj
  by_contra hne
  have hd := atomPoints_disjoint A hne
  exact disjoint_left.mp hd hj ⟨by omega, by omega⟩

/-- The rational-cut language, using whole atoms with labels strictly below q. -/
def language (A : ℕ → Atom) (q : Cut) : Set ℤ :=
  {x | ∃ n, x ∈ atomPoints A n ∧ (A n).label < q}

lemma atom_language_iff (A : ℕ → Atom) (q : Cut) {n : ℕ} {x : ℤ}
    (hx : x ∈ atomPoints A n) : x ∈ language A q ↔ (A n).label < q := by
  constructor
  · rintro ⟨j, hj, hlabel⟩
    have hjeq : j = n := by
      by_contra hne
      exact disjoint_left.mp (atomPoints_disjoint A hne) hj hx
    simpa [hjeq] using hlabel
  · intro hlabel
    exact ⟨n, hx, hlabel⟩

lemma language_mono (A : ℕ → Atom) {p q : Cut} (hpq : p ≤ q) : language A p ⊆ language A q := by
  rintro x ⟨n, hx, hlabel⟩
  exact ⟨n, hx, lt_of_lt_of_le hlabel hpq⟩

lemma languages_do_not_split (A : ℕ → Atom) (q : Cut) (n : ℕ) :
    atomPoints A n ⊆ language A q ∨ Disjoint (atomPoints A n) (language A q) := by
  by_cases hlabel : (A n).label < q
  · exact Or.inl (fun x hx => (atom_language_iff A q hx).mpr hlabel)
  · exact Or.inr (disjoint_left.mpr (fun x hx hmem => hlabel ((atom_language_iff A q hx).mp hmem)))

end BanachDensity1D.ProfileAux
