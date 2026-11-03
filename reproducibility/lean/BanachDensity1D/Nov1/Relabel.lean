import BanachDensity1D.Nov1.Balanced

/-! # Common-core relabelling of the existing B.1 obstruction trees. -/

namespace BanachDensity1D.FullRangeAux
open Set Filter

/-- Extend the increasing complement enumeration to all integers by fixing negatives. -/
noncomputable def embed (ρ : ℝ) (x : ℤ) : ℤ :=
  if 0 ≤ x then (phi ρ x.toNat : ℤ) else x

lemma embed_nat (ρ : ℝ) (j : ℕ) : embed ρ (j : ℤ) = (phi ρ j : ℤ) := by
  simp [embed]

lemma embed_strictMono {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) : StrictMono (embed ρ) := by
  intro x y hxy
  by_cases hx : 0 ≤ x <;> by_cases hy : 0 ≤ y
  · rw [embed, ite_eq_left hx, embed, ite_eq_left hy]
    have hnat : x.toNat < y.toNat := by omega
    exact_mod_cast phi_strictMono hρ0 hρ1 hnat
  · omega
  · rw [embed, ite_eq_right hx, embed, ite_eq_left hy]
    have : (0 : ℤ) ≤ phi ρ y.toNat := by positivity
    omega
  · simp only [embed, ite_eq_right hx, ite_eq_right hy]
    exact hxy

lemma embed_not_core {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (x : ℤ) :
    embed ρ x ∉ core ρ := by
  by_cases hx : 0 ≤ x
  · simpa [core, embed, hx] using phi_not_mem hρ0 hρ1 x.toNat
  · simp [embed, hx, core]

lemma embed_nonneg (ρ : ℝ) {x : ℤ} (hx : 0 ≤ x) : 0 ≤ embed ρ x := by
  rw [embed, ite_eq_left hx]
  positivity

/-- The current manuscript's language transformation. -/
noncomputable def lift (ρ : ℝ) (L : Set ℤ) : Set ℤ := core ρ ∪ embed ρ '' L

lemma core_subset_lift (ρ : ℝ) (L : Set ℤ) : core ρ ⊆ lift ρ L := subset_union_left

lemma lift_subset_iff {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {L M : Set ℤ} :
    lift ρ L ⊆ lift ρ M ↔ L ⊆ M := by
  constructor
  · intro h x hx
    rcases h (Or.inr ⟨x, hx, rfl⟩) with hcore | ⟨y, hy, hxy⟩
    · exact False.elim (embed_not_core hρ0 hρ1 x hcore)
    · have := (embed_strictMono hρ0 hρ1).injective hxy
      simpa [this] using hy
  · intro h x hx
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact Or.inl hx
    · exact Or.inr ⟨y, h hy, rfl⟩

lemma lift_proper {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {L M : Set ℤ}
    (h : L ⊂ M) : lift ρ L ⊂ lift ρ M := by
  exact ssubset_iff_subset_not_subset.mpr
    ⟨(lift_subset_iff hρ0 hρ1).mpr h.1,
      fun hm => h.not_subset ((lift_subset_iff hρ0 hρ1).mp hm)⟩

lemma lift_K0 {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    lift ρ PriorZero.Construction.K0 = PriorZero.Construction.K0 := by
  ext x
  constructor
  · rintro (hc | ⟨y, hy, rfl⟩)
    · exact hc.1
    · exact embed_nonneg ρ hy
  · intro hx
    by_cases hc : x ∈ core ρ
    · exact Or.inl hc
    · have hxn : x.toNat ∉ coreNat ρ := fun h => hc ⟨hx, h⟩
      have hmem : x.toNat ∈ range (phi ρ) := by
        rw [phi_range hρ0 hρ1]
        exact hxn
      obtain ⟨j, hj⟩ := hmem
      refine Or.inr ⟨j, by change (0 : ℤ) ≤ j; positivity, ?_⟩
      rw [embed_nat, hj, Int.toNat_of_nonneg hx]

lemma lift_nonneg (ρ : ℝ) {L : Set ℤ} (hL : L ⊆ PriorZero.Construction.K0) :
    lift ρ L ⊆ PriorZero.Construction.K0 := by
  rintro x (hx | ⟨y, hy, rfl⟩)
  · exact hx.1
  · exact embed_nonneg ρ (hL hy)

lemma lift_finite_cover {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    {L : Set ℤ} {child : ℕ → Set ℤ}
    (hcover : ∀ Q : Set ℤ, Q.Finite → Q ⊆ L → ∃ i, Q ⊆ child i)
    {F : Set ℤ} (hF : F.Finite) (hsub : F ⊆ lift ρ L) :
    ∃ i, F ⊆ lift ρ (child i) := by
  let Q := embed ρ ⁻¹' (F \ core ρ)
  have hfin : Q.Finite := (hF.subset sdiff_subset).preimage
    (embed_strictMono hρ0 hρ1).injective.injOn
  have hQL : Q ⊆ L := by
    intro x hx
    rcases hsub hx.1 with hcore | ⟨y, hy, heq⟩
    · exact False.elim (hx.2 hcore)
    · have := (embed_strictMono hρ0 hρ1).injective heq
      simpa [this] using hy
  obtain ⟨i, hi⟩ := hcover Q hfin hQL
  refine ⟨i, ?_⟩
  intro x hx
  by_cases hc : x ∈ core ρ
  · exact Or.inl hc
  · obtain ⟨y, hy, rfl⟩ := (hsub hx).resolve_left hc
    exact Or.inr ⟨y, hi ⟨hx, hc⟩, rfl⟩

/-- Relabelling leaves the existing inductive tree shape unchanged. -/
def mapTree (f : Set ℤ → Set ℤ) : LTree → LTree
  | .leaf L => .leaf (f L)
  | .node L child => .node (f L) (fun i => mapTree f (child i))

@[simp] lemma mapTree_label (f : Set ℤ → Set ℤ) (T : LTree) :
    (mapTree f T).label = f T.label := by cases T <;> rfl

lemma mapTree_paths (f : Set ℤ → Set ℤ) (T : LTree) (P : List (Set ℤ)) :
    P ∈ (mapTree f T).paths ↔ ∃ H ∈ T.paths, P = H.map f := by
  induction T generalizing P with
  | leaf L => simp [mapTree, LTree.paths]
  | node L child ih =>
    constructor
    · rintro ⟨i, Q, hQ, rfl⟩
      obtain ⟨H, hH, rfl⟩ := (ih i Q).mp hQ
      exact ⟨L :: H, ⟨i, H, hH, rfl⟩, rfl⟩
    · rintro ⟨H, ⟨i, Q, hQ, rfl⟩, rfl⟩
      exact ⟨i, Q.map f, (ih i _).mpr ⟨Q, hQ, rfl⟩, rfl⟩

lemma mapTree_admissible {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (X : Set (Set ℤ)) (T : LTree) (hT : T.Admissible X) :
    (mapTree (lift ρ) T).Admissible (lift ρ '' X) := by
  induction T with
  | leaf L => trivial
  | node L child ih =>
    refine ⟨?_, ?_⟩
    · intro i
      obtain ⟨hm, hp, ha⟩ := hT.1 i
      simp only [mapTree_label]
      exact ⟨⟨(child i).label, hm, rfl⟩, lift_proper hρ0 hρ1 hp, ih i ha⟩
    · intro F hF hsub
      obtain ⟨i, hi⟩ := lift_finite_cover hρ0 hρ1 hT.2 hF hsub
      exact ⟨i, by simpa only [mapTree_label] using hi⟩

/-- Precisely the common-core image of the completed B.1 family. -/
noncomputable def family (C : PriorZero.Construction) (ρ : ℝ) : Set (Set ℤ) :=
  lift ρ '' C.X0

lemma family_langClass (C : PriorZero.Construction) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    LangClass (family C ρ) := by
  refine ⟨C.langClass.nonempty.image (lift ρ), C.langClass.countable.image (lift ρ), ?_⟩
  rintro M ⟨L, hL, rfl⟩
  exact ((C.langClass.infinite L hL).image (embed_strictMono hρ0 hρ1).injective.injOn).mono
    subset_union_right

lemma family_K0 (C : PriorZero.Construction) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    PriorZero.Construction.K0 ∈ family C ρ := by
  refine ⟨_, C.K0_mem, ?_⟩
  exact lift_K0 hρ0 hρ1

lemma lifted_obstruction (C : PriorZero.Construction) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (n : ℕ) :
    def_aot (family C ρ) PriorZero.Construction.K0
      (mapTree (lift ρ) (C.obstruction n)) := by
  refine ⟨?_, mapTree_admissible hρ0 hρ1 _ _ (C.obstruction_admissible n).2⟩
  rw [mapTree_label, (C.obstruction_admissible n).1, lift_K0 hρ0 hρ1]

end BanachDensity1D.FullRangeAux
