import BanachDensityHD.Characterization

/-!
# Nov. 1 protected-tree proof correspondence

Additive interfaces for Definitions 2.3, 5.3, 7.5–7.6 and Theorem 7.7 /
Corollaries 7.8–7.9. See TREE-CORRESPONDENCE-STRENGTHENING.md for the authority
and the distinction between occurrence identity and existence equivalence.
-/
namespace BanachDensityHD.TreeCorrespondence
open Set Topology
open scoped Classical

section Topology
variable {α : Type} {X : Set (Set α)}

/-- The manuscript's iterative basic set, specified by its least-closure property.
The finite test is a function of the whole history, not of its last language. -/
def PaperBasic (H : History X) (F : History X → Set α) (V : Set (History X)) : Prop :=
  FiniteTests F ∧ H ∈ V ∧
  (∀ Γ ∈ V, ∀ Δ M, History.IsSnoc Γ Δ M → F Γ ⊆ M → Δ ∈ V) ∧
  ∀ W : Set (History X), H ∈ W →
    (∀ Γ ∈ W, ∀ Δ M, History.IsSnoc Γ Δ M → F Γ ⊆ M → Δ ∈ W) → V ⊆ W

/-- Least iterative closure is exactly the existing inductive basic set. -/
theorem paperBasic_iff (H : History X) (F : History X → Set α) (V : Set (History X)) :
    PaperBasic H F V ↔ FiniteTests F ∧ V = {Γ | InBasic H F Γ} := by
  constructor
  · rintro ⟨hf, hr, hs, hm⟩
    refine ⟨hf, Set.Subset.antisymm (hm _ InBasic.base ?_) ?_⟩
    · intro Γ hΓ Δ M hsn hF; exact InBasic.step hΓ hsn hF
    · intro Γ hΓ
      induction hΓ with
      | base => exact hr
      | step _ hsn hF ih => exact hs _ ih _ _ hsn hF
  · rintro ⟨hf, rfl⟩
    refine ⟨hf, InBasic.base, ?_, ?_⟩
    · intro Γ hΓ Δ M hsn hF; exact InBasic.step hΓ hsn hF
    · intro W hr hs Γ hΓ
      induction hΓ with
      | base => exact hr
      | step _ hsn hF ih => exact hs _ ih _ _ hsn hF

/-- Every root component is open: restricting to H_K introduces no extra
ambient openness requirement. -/
theorem rootComponent_isOpen (K : Set α) : IsOpen (historiesFrom X K) := by
  rw [HistoriesAux.isOpen_iff]
  intro H hH
  refine ⟨∅, Set.finite_empty, Set.empty_subset _, ?_⟩
  rintro Γ M ⟨_, _, he⟩ _
  show Γ.val.headD ∅ = K
  rw [he]
  obtain ⟨L, t, ht⟩ := List.exists_cons_of_ne_nil H.property.1
  change H.val.headD ∅ = K at hH
  simpa [ht] using hH

/-- Relative openness in the manuscript's H_K is equivalent to the ambient
openness used in IsQGoodDecoration, for sets already contained in H_K. -/
theorem relative_open_iff {K : Set α} {U : Set (History X)}
    (hU : U ⊆ historiesFrom X K) :
    IsOpen (Subtype.val ⁻¹' U : Set (historiesFrom X K)) ↔ IsOpen U := by
  constructor
  · intro ho
    have he : (Subtype.val '' (Subtype.val ⁻¹' U : Set (historiesFrom X K))) = U := by
      ext H; simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact hx
      · intro hx; exact ⟨⟨H, hU hx⟩, hx, rfl⟩
    rw [← he]
    exact (rootComponent_isOpen K).isOpenMap_subtype_val _ ho
  · intro ho; exact ho.preimage continuous_subtype_val
end Topology

/-! ## Arbitrarily countable branching obstruction trees

An inductive (well-founded) occurrence tree with an arbitrary countable,
nonempty child type at each internal vertex. Finite branching is included;
no finite-height bound or finite-branching compactness is assumed.
-/
inductive PaperObstruction (α : Type) : Type 1
  | leaf (label : Set α)
  | node (label : Set α) (ι : Type) [Countable ι] [Nonempty ι]
      (child : ι → PaperObstruction α)

namespace PaperObstruction
variable {α : Type}
def label : PaperObstruction α → Set α
  | .leaf L => L
  | @node _ L _ _ _ _ => L

def admissible (X : Set (Set α)) : PaperObstruction α → Prop
  | .leaf _ => True
  | @node _ L _ _ _ c =>
    (∀ i, (c i).label ∈ X ∧ (c i).label ⊂ L ∧ admissible X (c i)) ∧
    ∀ F : Set α, F.Finite → F ⊆ L → ∃ i, F ⊆ (c i).label

def paths : PaperObstruction α → Set (List (Set α))
  | .leaf L => {[L]}
  | @node _ L _ _ _ c => {P | ∃ i, ∃ Q ∈ paths (c i), P = L :: Q}

noncomputable def encode : PaperObstruction α → LTree α
  | .leaf L => .leaf L
  | @node _ L ι instC instN c =>
      letI := instC
      letI := instN
      .node L (fun n => encode (c ((exists_surjective_nat ι).choose n)))

@[simp] theorem encode_label (T : PaperObstruction α) : T.encode.label = T.label := by
  cases T <;> rfl

/-- Enumeration repeats children when necessary, but loses no terminal language path. -/
theorem encode_paths (T : PaperObstruction α) : T.encode.paths = T.paths := by
  induction T with
  | leaf L => rfl
  | @node L ι _ _ c ih =>
    ext P
    simp only [encode, LTree.paths, paths, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, Q, hQ, he⟩
      exact ⟨_, Q, (ih _ ▸ hQ), he⟩
    · rintro ⟨i, Q, hQ, he⟩
      obtain ⟨n, hn⟩ := (exists_surjective_nat ι).choose_spec i
      refine ⟨n, Q, ?_, he⟩
      rw [hn, ih]; exact hQ

/-- Admissibility is preserved and reflected, including universal finite evidence. -/
theorem encode_admissible (X : Set (Set α)) (T : PaperObstruction α) :
    T.encode.Admissible X ↔ T.admissible X := by
  induction T with
  | leaf L => rfl
  | @node L ι _ _ c ih =>
    simp only [encode, LTree.Admissible, admissible, encode_label]
    constructor
    · rintro ⟨hc, hf⟩
      refine ⟨?_, ?_⟩
      · intro i
        obtain ⟨n, hn⟩ := (exists_surjective_nat ι).choose_spec i
        have hi := hc n
        rw [hn] at hi
        exact ⟨hi.1, hi.2.1, (ih i).1 hi.2.2⟩
      · intro F hF hFL
        obtain ⟨n, hn⟩ := hf F hF hFL
        exact ⟨_, hn⟩
    · rintro ⟨hc, hf⟩
      refine ⟨fun n => ⟨(hc _).1, (hc _).2.1, (ih _).2 (hc _).2.2⟩, ?_⟩
      intro F hF hFL
      obtain ⟨i, hi⟩ := hf F hF hFL
      obtain ⟨n, hn⟩ := (exists_surjective_nat ι).choose_spec i
      exact ⟨n, hn ▸ hi⟩

def decode : LTree α → PaperObstruction α
  | .leaf L => .leaf L
  | .node L c => .node L ℕ (fun n => decode (c n))

@[simp] theorem decode_label (T : LTree α) : (decode T).label = T.label := by
  cases T <;> rfl
@[simp] theorem decode_paths (T : LTree α) : (decode T).paths = T.paths := by
  induction T with
  | leaf L => rfl
  | node L c ih => ext P; simp only [decode, paths, LTree.paths, ih]
@[simp] theorem decode_admissible (X : Set (Set α)) (T : LTree α) :
    (decode T).admissible X ↔ T.Admissible X := by
  induction T with
  | leaf L => rfl
  | node L c ih => simp only [decode, admissible, LTree.Admissible, decode_label, ih]

/-- Immediate descendant relation; inductive trees may have unbounded finite
branch lengths but cannot have an infinite descending branch. -/
inductive Child : PaperObstruction α → PaperObstruction α → Prop
  | atChild {L : Set α} {ι : Type} [Countable ι] [Nonempty ι]
      (c : ι → PaperObstruction α) (i : ι) : Child (c i) (.node L ι c)

theorem wellFounded_child : WellFounded (Child (α := α)) := by
  constructor
  intro T
  induction T with
  | leaf L =>
    constructor
    intro S hs
    cases hs
  | @node L ι _ _ c ih =>
    constructor
    intro S hs
    cases hs with
    | atChild _ i => exact ih i

/-- Countability is a union of countably many countable sets, not an assumption
of finite branching. -/
theorem paths_countable (T : PaperObstruction α) : T.paths.Countable := by
  induction T with
  | leaf L => exact Set.countable_singleton _
  | @node L ι instC _ c ih =>
    letI := instC
    have he : (.node L ι c : PaperObstruction α).paths =
        ⋃ i, List.cons L '' (c i).paths := by
      ext P
      simp only [paths, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image]
      constructor
      · rintro ⟨i, Q, hQ, he⟩; exact ⟨i, Q, hQ, he.symm⟩
      · rintro ⟨i, Q, hQ, he⟩; exact ⟨i, Q, hQ, he.symm⟩
    rw [he]
    exact Set.countable_iUnion fun i => (ih i).image _
end PaperObstruction

/-- Quantification over arbitrary countable branching is equivalent to that over
LTree, for every property of terminal language histories. This is not an
isomorphism of occurrences; duplicate enumerated children are harmless. -/
theorem all_obstructions_iff {α : Type} (X : Set (Set α)) (K : Set α)
    (Good : List (Set α) → Prop) :
    (∀ T : PaperObstruction α, T.label = K → T.admissible X → ∃ P ∈ T.paths, Good P) ↔
    (∀ T : LTree α, def_aot X K T → ∃ P ∈ T.paths, Good P) := by
  constructor
  · intro ht T hT
    simpa using ht (PaperObstruction.decode T) (by simpa using hT.1) (by simpa using hT.2)
  · intro ht T he ha
    have hT : def_aot X K T.encode := ⟨by simpa using he, (T.encode_admissible X).2 ha⟩
    simpa only [T.encode_paths] using ht T.encode hT


/-- Lemma 5.6 for arbitrary countable branching, including exact common-root
concatenation. This exposes the closure step used in the written Corollary 7.8. -/
theorem paper_obstruction_closure {α : Type} [Countable α] {X : Set (Set α)}
    (D : Set (History X)) (H : History X) :
    H ∈ closure D ↔ ∃ T : PaperObstruction α,
      T.label = H.last ∧ T.admissible X ∧
      ∀ P ∈ T.paths, ∃ G ∈ D, G.val = H.val ++ P.tail := by
  rw [HistoriesAux.lem_obstruction_closure_gen]
  constructor
  · rintro ⟨T, he, hp⟩
    exact ⟨PaperObstruction.decode T, by simpa using he.1,
      by simpa using he.2, by simpa using hp⟩
  · rintro ⟨T, he, ha, hp⟩
    exact ⟨T.encode, ⟨by simpa using he, (T.encode_admissible X).2 ha⟩,
      by simpa only [T.encode_paths] using hp⟩

end BanachDensityHD.TreeCorrespondence
