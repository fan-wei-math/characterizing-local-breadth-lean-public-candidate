import BanachDensityHD.TreeCorrespondence.Basic

/-! # Unfolding arbitrary countable well-founded vertex trees.

This interface does not start by assuming an inductive tree. Well-foundedness
is equivalent (classically) to the manuscript's no-infinite-branch condition.
-/
namespace BanachDensityHD.TreeCorrespondence
open Set
open scoped Classical

/-- Parent/child presentation of a countable well-founded rooted tree.
Unique parents are unnecessary for the bridge: unfolding a DAG also works. -/
structure VertexObstruction (V α : Type) where
  root : V
  label : V → Set α
  child : V → V → Prop
  wellFounded : WellFounded child

namespace VertexObstruction
variable {V α : Type} [Countable V] (T : VertexObstruction V α)

/-- Actual finite root-to-leaf language histories, retaining vertex witnesses. -/
inductive Terminal : V → List (Set α) → Prop
  | leaf (v : V) (hleaf : ∀ w, ¬ T.child w v) : Terminal v [T.label v]
  | step {v w : V} {P : List (Set α)} (edge : T.child w v)
      (tail : Terminal w P) : Terminal v (T.label v :: P)

/-- The manuscript's finite-evidence and strict-refinement conditions at vertices. -/
def Admissible (X : Set (Set α)) : Prop :=
  (∀ v, T.label v ∈ X) ∧
  (∀ v w, T.child w v → T.label w ⊂ T.label v) ∧
  (∀ v, (∃ w, T.child w v) → ∀ F : Set α, F.Finite → F ⊆ T.label v →
    ∃ w, T.child w v ∧ F ⊆ T.label w)

noncomputable def unfold : V → PaperObstruction α :=
  T.wellFounded.fix fun v rec =>
    if hv : ∃ w, T.child w v then
      letI : Nonempty {w // T.child w v} := ⟨⟨hv.choose, hv.choose_spec⟩⟩
      .node (T.label v) {w // T.child w v} (fun w => rec w.val w.property)
    else .leaf (T.label v)

theorem unfold_eq (v : V) :
    T.unfold v = if hv : ∃ w, T.child w v then
      letI : Nonempty {w // T.child w v} := ⟨⟨hv.choose, hv.choose_spec⟩⟩
      PaperObstruction.node (T.label v) {w // T.child w v} (fun w => T.unfold w.val)
    else .leaf (T.label v) := by
  conv_lhs => unfold unfold; rw [WellFounded.fix_eq]
  rfl

@[simp] theorem unfold_label (v : V) : (T.unfold v).label = T.label v := by
  rw [T.unfold_eq]
  split_ifs <;> rfl

/-- Every terminal path is preserved and reflected. The transformation covers
arbitrary countable vertex trees, not only trees supplied in inductive form. -/
theorem unfold_paths (v : V) (P : List (Set α)) :
    P ∈ (T.unfold v).paths ↔ T.Terminal v P := by
  induction v using T.wellFounded.induction generalizing P with
  | h v ih =>
    rw [T.unfold_eq]
    split_ifs with hv
    · change (∃ w : {w // T.child w v}, ∃ Q ∈ (T.unfold w.val).paths,
        P = T.label v :: Q) ↔ _
      constructor
      · rintro ⟨w, Q, hQ, rfl⟩
        exact Terminal.step w.property ((ih w.val w.property Q).1 hQ)
      · intro hp
        cases hp with
        | leaf _ hl => exact False.elim (hl hv.choose hv.choose_spec)
        | step he ht => exact ⟨⟨_, he⟩, _, (ih _ he _).2 ht, rfl⟩
    · change P = [T.label v] ↔ _
      constructor
      · rintro rfl; exact Terminal.leaf v (fun w hw => hv ⟨w, hw⟩)
      · intro hp
        cases hp with
        | leaf => rfl
        | step he _ => exact False.elim (hv ⟨_, he⟩)

theorem unfold_admissible {X : Set (Set α)} (ha : T.Admissible X) (v : V) :
    (T.unfold v).admissible X := by
  induction v using T.wellFounded.induction with
  | h v ih =>
    rw [T.unfold_eq]
    split_ifs with hv
    · change (∀ w : {w // T.child w v}, _ ∧ _ ∧ _) ∧ _
      refine ⟨fun w => ⟨by simpa using ha.1 w.val,
        by simpa using ha.2.1 v w.val w.property, ih _ w.property⟩, ?_⟩
      intro F hF hFL
      obtain ⟨w, hw, hFw⟩ := ha.2.2 v hv F hF hFL
      exact ⟨⟨w, hw⟩, by simpa using hFw⟩
    · trivial

/-- Arbitrary countable well-founded vertex trees inherit every terminal-path
conclusion established for the paper inductive interface. -/
theorem transfer_terminal {X : Set (Set α)} {Good : List (Set α) → Prop}
    (ha : T.Admissible X)
    (hgood : ∀ S : PaperObstruction α, S.label = T.label T.root →
      S.admissible X → ∃ P ∈ S.paths, Good P) :
    ∃ P, T.Terminal T.root P ∧ Good P := by
  obtain ⟨P, hp, hg⟩ := hgood (T.unfold T.root) (T.unfold_label T.root)
    (T.unfold_admissible ha T.root)
  exact ⟨P, (T.unfold_paths T.root P).1 hp, hg⟩
/-- The manuscript's prohibition of infinite paths is exactly well-foundedness
of the child relation, under ordinary classical dependent choice. -/
theorem wellFounded_iff_no_infinite (r : V → V → Prop) :
    WellFounded r ↔ ¬ ∃ f : ℕ → V, ∀ n, r (f (n + 1)) (f n) := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  exact ⟨fun he ⟨f, hf⟩ => he.false ⟨f, hf⟩,
    fun hn => ⟨fun f => hn ⟨f.val, f.property⟩⟩⟩
end VertexObstruction
end BanachDensityHD.TreeCorrespondence
