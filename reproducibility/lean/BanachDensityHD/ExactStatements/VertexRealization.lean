import BanachDensityHD.TreeCorrespondence.VertexObstruction

/-! Occurrence-preserving countable vertex realization of the obstruction interface.
The vertex is its full dependent address. Distinct equal-labelled children stay distinct.
-/
namespace BanachDensityHD.TreeCorrespondence
open Set
open scoped Classical
namespace PaperObstruction

def Address {α : Type} : PaperObstruction α → Type
  | .leaf _ => PUnit
  | @node _ _ ι _ _ c => Option (Σ i : ι, Address (c i))

namespace Address
variable {α : Type}

def root : (T : PaperObstruction α) → Address T
  | .leaf _ => PUnit.unit
  | @node _ L ι hc hn c => none

def down {L : Set α} {ι : Type} [Countable ι] [Nonempty ι]
    (c : ι → PaperObstruction α) (i : ι) (v : Address (c i)) :
    Address (.node L ι c) := some ⟨i, v⟩

def tree : {T : PaperObstruction α} → Address T → PaperObstruction α
  | .leaf L, _ => .leaf L
  | @node _ L ι hc hn c, none => @node _ L ι hc hn c
  | @node _ _ ι hc hn c, some ⟨i, v⟩ => tree v

@[simp] theorem tree_root (T : PaperObstruction α) : (root T).tree = T := by
  cases T <;> rfl
@[simp] theorem tree_down {L : Set α} {ι : Type} [Countable ι] [Nonempty ι]
    (c : ι → PaperObstruction α) (i : ι) (v : Address (c i)) :
    (down (L := L) c i v).tree = v.tree := rfl

inductive Edge : {T : PaperObstruction α} → Address T → Address T → Prop
  | first {L : Set α} {ι : Type} [Countable ι] [Nonempty ι]
      (c : ι → PaperObstruction α) (i : ι) :
      Edge (down c i (root (c i))) (root (.node L ι c))
  | lift {L : Set α} {ι : Type} [Countable ι] [Nonempty ι]
      (c : ι → PaperObstruction α) (i : ι) {w v : Address (c i)}
      (h : Edge w v) : Edge (down (L := L) c i w) (down c i v)

theorem edge_tree {T : PaperObstruction α} {w v : Address T} (h : Edge w v) :
    Child w.tree v.tree := by
  induction h with
  | first c i => simpa using Child.atChild c i
  | lift _ _ _ ih => exact ih

theorem wellFounded (T : PaperObstruction α) : WellFounded (@Edge α T) :=
  (PaperObstruction.wellFounded_child.onFun (f := tree)).mono fun _ _ h => edge_tree h

instance countable (T : PaperObstruction α) : Countable (Address T) := by
  induction T with
  | leaf L => exact inferInstanceAs (Countable PUnit)
  | @node L ι hc hn c ih =>
    letI := hc
    letI : ∀ i, Countable (Address (c i)) := ih
    exact inferInstanceAs (Countable (Option (Σ i, Address (c i))))

def vertexTree (T : PaperObstruction α) : VertexObstruction (Address T) α where
  root := root T
  label v := v.tree.label
  child := Edge
  wellFounded := wellFounded T

lemma terminal_down {L : Set α} {ι : Type} [Countable ι] [Nonempty ι]
    (c : ι → PaperObstruction α) (i : ι) (v : Address (c i)) (P : List (Set α)) :
    (vertexTree (.node L ι c)).Terminal (down c i v) P ↔
      (vertexTree (c i)).Terminal v P := by
  constructor
  · intro h
    generalize he : down (L := L) c i v = u at h
    induction h generalizing v with
    | leaf u hl =>
      subst u
      apply VertexObstruction.Terminal.leaf
      intro w hw
      exact hl (down c i w) (.lift c i hw)
    | @step u w P hw ht ih =>
      subst u
      cases hw with
      | lift _ _ he =>
        exact VertexObstruction.Terminal.step he (ih _ rfl)
  · intro h
    induction h with
    | leaf v hl =>
      apply VertexObstruction.Terminal.leaf
      intro w hw
      cases hw with
      | lift _ _ he => exact hl _ he
    | step he _ ih => exact VertexObstruction.Terminal.step (.lift c i he) ih

/-- Exact terminal language paths; no quotient of original occurrences is used. -/
theorem terminal_root (T : PaperObstruction α) (P : List (Set α)) :
    (vertexTree T).Terminal (root T) P ↔ P ∈ T.paths := by
  induction T generalizing P with
  | leaf L =>
    constructor
    · intro h; cases h with
      | leaf => simp [vertexTree, PaperObstruction.label, PaperObstruction.paths]
      | step he _ => cases he
    · intro h
      change P = [L] at h
      subst P
      apply VertexObstruction.Terminal.leaf (T := vertexTree (.leaf L))
      intro w h; change Edge w (root (.leaf L)) at h; cases h
  | @node L ι hc hn c ih =>
    constructor
    · intro h; cases h with
      | leaf _ hl =>
        let i : ι := Classical.choice hn
        exact False.elim (hl _ (.first c i))
      | step he ht =>
        cases he with
        | first _ i => exact ⟨i, _, (ih i _).1 ((terminal_down c i _ _).1 ht), by simp [vertexTree, PaperObstruction.label, PaperObstruction.paths]⟩
    · rintro ⟨i, Q, hQ, rfl⟩
      simpa [vertexTree, PaperObstruction.label] using
        (VertexObstruction.Terminal.step (T := vertexTree (.node L ι c)) (Edge.first c i)
          ((terminal_down c i _ _).2 ((ih i _).2 hQ)))

lemma subtree_admissible {T : PaperObstruction α} {X : Set (Set α)}
    (hr : T.label ∈ X) (ha : T.admissible X) (v : Address T) :
    v.tree.label ∈ X ∧ v.tree.admissible X := by
  induction T with
  | leaf L => exact ⟨hr, ha⟩
  | @node L ι hc hn c ih =>
    cases v with
    | none => exact ⟨hr, ha⟩
    | some w =>
      rcases w with ⟨i, v⟩
      exact ih i (ha.1 i).1 (ha.1 i).2.2 v

lemma finite_child {T : PaperObstruction α} {X : Set (Set α)}
    (hr : T.label ∈ X) (ha : T.admissible X) (v : Address T)
    (hv : ∃ w, Edge w v) (F : Set α) (hF : F.Finite) (hFL : F ⊆ v.tree.label) :
    ∃ w, Edge w v ∧ F ⊆ w.tree.label := by
  induction T with
  | leaf L => obtain ⟨w, hw⟩ := hv; cases hw
  | @node L ι hc hn c ih =>
    cases v with
    | none =>
      obtain ⟨i, hi⟩ := ha.2 F hF hFL
      exact ⟨down c i (root _), Edge.first c i, by simpa using hi⟩
    | some w =>
      rcases w with ⟨i, v⟩
      have hv' : ∃ w, Edge w v := by
        obtain ⟨w, hw⟩ := hv
        cases hw with
        | lift _ _ he => exact ⟨_, he⟩
      obtain ⟨w, hw, hFw⟩ := ih i (ha.1 i).1 (ha.1 i).2.2 v hv' hFL
      exact ⟨down c i w, Edge.lift c i hw, hFw⟩

lemma child_strict {S R : PaperObstruction α} {X : Set (Set α)}
    (ha : S.admissible X) (he : Child R S) : R.label ⊂ S.label := by
  cases he with
  | atChild c i => exact (ha.1 i).2.1

/-- All admissibility clauses hold at all actual address vertices. -/
theorem admissible {T : PaperObstruction α} {X : Set (Set α)}
    (hr : T.label ∈ X) (ha : T.admissible X) : (vertexTree T).Admissible X := by
  refine ⟨fun v => (subtree_admissible hr ha v).1, ?_, ?_⟩
  · intro v w he
    exact child_strict (subtree_admissible hr ha v).2 (edge_tree he)
  · intro v hv F hF hFL
    exact finite_child hr ha v hv F hF hFL

end Address
end PaperObstruction
end BanachDensityHD.TreeCorrespondence
