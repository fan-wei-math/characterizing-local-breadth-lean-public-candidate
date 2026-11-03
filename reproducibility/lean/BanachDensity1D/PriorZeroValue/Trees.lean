import BanachDensity1D.PriorZeroValue.Construction

/-! # Admissible finite-height towers for the previous construction. -/

namespace BanachDensity1D.PriorZero.Construction
open Set Filter
variable (C : BanachDensity1D.PriorZero.Construction)

lemma language_nonneg (ell a : ℕ) (hs : List ℕ) : C.language ell a hs ⊆ K0 := by
  have hex : ∀ b, C.exceptions b hs ⊆ K0 := by
    induction hs with
    | nil => simp [exceptions]
    | cons h hs ih =>
      intro b x hx
      rcases hx with hx | hx
      · obtain ⟨i, hi, hlo, hup⟩ := hx
        have : (0 : ℤ) ≤ C.endpoint i := by positivity
        exact le_trans this (by omega)
      · exact ih (b + 1) hx
  intro x hx
  rcases hx with (hx | hx) | hx
  · exact hx.1
  · obtain ⟨i, hlo, hup⟩ := hx
    exact le_trans (by positivity : (0 : ℤ) ≤ C.endpoint i) hlo
  · exact hex a hx

lemma child_subset (ell a k : ℕ) (hs : List ℕ) :
    C.language ell a (k :: hs) ⊆ C.language ell (a + 1) hs := by
  intro x hx
  rcases hx with (hx | hx) | (hx | hx)
  · exact Or.inl (Or.inl hx)
  · obtain ⟨i, hlo, hup⟩ := hx
    exact Or.inl (Or.inr ⟨i, hlo, by push_cast; omega⟩)
  · obtain ⟨i, hi, hlo, hup⟩ := hx
    exact Or.inl (Or.inr ⟨i, by omega, hup⟩)
  · exact Or.inr hx

lemma child_mono (ell a : ℕ) (hs : List ℕ) {k m : ℕ} (hkm : k ≤ m) :
    C.language ell a (k :: hs) ⊆ C.language ell a (m :: hs) := by
  intro x hx
  rcases hx with hx | (hx | hx)
  · exact Or.inl hx
  · obtain ⟨i, hi, hlo, hup⟩ := hx
    exact Or.inr (Or.inl ⟨i, lt_of_lt_of_le hi hkm, hlo, hup⟩)
  · exact Or.inr (Or.inr hx)

lemma child_covers (ell a : ℕ) (hs : List ℕ) {x : ℤ}
    (hx : x ∈ C.language ell (a + 1) hs) :
    ∃ k, x ∈ C.language ell a (k :: hs) := by
  rcases hx with (hx | hx) | hx
  · exact ⟨0, Or.inl (Or.inl hx)⟩
  · obtain ⟨i, hlo, hup⟩ := hx
    by_cases he : x = C.endpoint i
    · refine ⟨0, Or.inl (Or.inr ⟨i, hlo, ?_⟩)⟩
      rw [he]; omega
    · exact ⟨i + 1, Or.inr (Or.inl ⟨i, by omega, by omega, hup⟩)⟩
  · exact ⟨0, Or.inr (Or.inr hx)⟩

lemma child_finite_cover (ell a b : ℕ) (hs : List ℕ) {F : Set ℤ}
    (hF : F.Finite) (hsub : F ⊆ C.language ell (a + 1) hs) :
    ∃ k, b ≤ k ∧ F ⊆ C.language ell a (k :: hs) := by
  induction F, hF using Set.Finite.induction_on with
  | empty => exact ⟨b, le_rfl, empty_subset _⟩
  | @insert x F hnot hfin ih =>
    obtain ⟨k, hbk, hk⟩ := ih (fun y hy => hsub (Or.inr hy))
    obtain ⟨m, hm⟩ := C.child_covers ell a hs (hsub (Or.inl rfl))
    refine ⟨max k m, le_trans hbk (le_max_left _ _), ?_⟩
    rintro y (rfl | hy)
    · exact C.child_mono ell a hs (le_max_right k m) hm
    · exact C.child_mono ell a hs (le_max_left k m) (hk hy)

lemma child_proper (ell a k : ℕ) (hs : List ℕ) :
    C.language ell a (k :: hs) ⊂ C.language ell (a + 1) hs := by
  obtain ⟨B, hB⟩ := C.isolated_eventually (a + 1 + hs.length)
  let r := B + ell + bound hs + k + 1
  have hiso := hB r (by dsimp [r]; omega)
  have hp := C.language_trace hiso (le_refl (a + 1 + hs.length))
    (show ell ≤ r by dsimp [r]; omega) (show bound hs < r by dsimp [r]; omega)
  have hc := C.language_trace hiso (show a + (k :: hs).length ≤ a + 1 + hs.length by simp; omega)
    (show ell ≤ r by dsimp [r]; omega)
    (show bound (k :: hs) < r by simp only [bound]; dsimp [r]; omega)
  refine ssubset_iff_subset_ne.mpr ⟨C.child_subset ell a k hs, ?_⟩
  intro heq
  rw [heq, hp] at hc
  have hx : (C.endpoint r : ℤ) + ((a + 1 : ℕ) : ℤ) ∈
      Icc (C.endpoint r : ℤ) ((C.endpoint r : ℤ) + ((a + 1 : ℕ) : ℤ)) := by
    constructor <;> omega
  rw [hc] at hx
  have := hx.2
  push_cast at this
  omega

lemma root_proper (ell n : ℕ) : C.language ell n [] ⊂ K0 := by
  obtain ⟨B, hB⟩ := C.isolated_eventually (n + 1)
  let r := B + ell + 1
  have ht := C.language_trace (hB r (by dsimp [r]; omega))
    (show n + [].length ≤ n + 1 by simp)
    (show ell ≤ r by dsimp [r]; omega) (show bound [] < r by simp [bound, r])
  refine ssubset_iff_subset_ne.mpr ⟨C.language_nonneg ell n [], ?_⟩
  intro heq
  rw [heq] at ht
  have hx : (C.endpoint r : ℤ) + ((n + 1 : ℕ) : ℤ) ∈
      K0 ∩ Icc (C.endpoint r : ℤ) ((C.endpoint r : ℤ) + ((n + 1 : ℕ) : ℤ)) := by
    dsimp [K0]
    constructor
    · change 0 ≤ (C.endpoint r : ℤ) + ((n + 1 : ℕ) : ℤ)
      positivity
    · constructor <;> omega
  rw [ht] at hx
  have := hx.2
  push_cast at this
  omega

lemma root_finite_cover (n : ℕ) {F : Set ℤ} (hF : F.Finite) (hsub : F ⊆ K0) :
    ∃ ell, F ⊆ C.language ell n [] := by
  obtain ⟨b, hb⟩ := hF.bddAbove
  refine ⟨b.toNat + 1, ?_⟩
  intro x hx
  refine Or.inl (Or.inl ⟨hsub hx, ?_⟩)
  have := hb hx
  have : b ≤ (b.toNat : ℤ) := Int.self_le_toNat b
  push_cast
  omega

lemma mem_le_bound {hs : List ℕ} {j : ℕ} (hj : j ∈ hs) : j ≤ bound hs := by
  induction hs with
  | nil => simp at hj
  | cons h hs ih =>
    rcases List.mem_cons.mp hj with rfl | hj
    · exact le_max_left _ _
    · exact le_trans (ih hj) (le_max_right _ _)

lemma ordered_prepend {hs : List ℕ} (hhs : Ordered hs) {k : ℕ} (hk : bound hs ≤ k) :
    Ordered (k :: hs) := by
  exact List.pairwise_cons.mpr ⟨fun j hj => (mem_le_bound hj).trans hk, hhs⟩

/-- Exactly the finite-height tower prescribed by current Appendix B.1. The
max reindexes all sufficiently large legal child-prefix indices. -/
def tower (ell : ℕ) : ℕ → List ℕ → LTree
  | 0, hs => .leaf (C.language ell 0 hs)
  | a + 1, hs => .node (C.language ell (a + 1) hs)
      (fun k => tower ell a (max k (bound hs) :: hs))

@[simp] lemma tower_label (ell a : ℕ) (hs : List ℕ) :
    (C.tower ell a hs).label = C.language ell a hs := by
  cases a <;> rfl

lemma tower_admissible (ell a : ℕ) {hs : List ℕ} (hhs : Ordered hs) :
    (C.tower ell a hs).Admissible C.X0 := by
  induction a generalizing hs with
  | zero => trivial
  | succ a ih =>
    refine ⟨?_, ?_⟩
    · intro k
      simp only [tower_label]
      have ho := ordered_prepend hhs (le_max_right k (bound hs))
      exact ⟨C.language_mem ell a ho, C.child_proper ell a _ hs, ih ho⟩
    · intro F hF hsub
      obtain ⟨k, hk, hcover⟩ := C.child_finite_cover ell a (bound hs) hs hF hsub
      refine ⟨k, ?_⟩
      simpa only [tower_label, max_eq_left hk] using hcover

/-- The obstruction tree T_n: root N, followed by the height-n towers. -/
def obstruction (n : ℕ) : LTree := .node K0 (fun ell => C.tower ell n [])

lemma obstruction_admissible (n : ℕ) : def_aot C.X0 K0 (C.obstruction n) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro ell
    simp only [tower_label]
    exact ⟨C.language_mem ell n (by simp [Ordered]), C.root_proper ell n,
      C.tower_admissible ell n (by simp [Ordered])⟩
  · intro F hF hsub
    simpa only [tower_label] using C.root_finite_cover n hF hsub

end BanachDensity1D.PriorZero.Construction
