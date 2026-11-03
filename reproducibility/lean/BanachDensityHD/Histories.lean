import BanachDensityHD.Common

/-!
# Histories, the finite-evidence history topology, admissible obstruction trees

Kleinberg–Wei, *Characterizing Local Breadth in Language Generation*.
Historical source numbering is retained; current mappings are in the release registry.

-/

namespace BanachDensityHD

open Set Filter
open scoped Classical

/-! ## Histories, the finite-evidence history topology, obstruction trees
(ported from `BanachDensity1D.Chains` / `BanachDensity1D.HistoryTopology`, `Set ℤ` ↦ `Set α`) -/

section Histories
variable {α : Type*}

/-- A chain of languages of `X`: a nonempty strictly descending list (1D `IsChain`). -/
def IsChain (X : Set (Set α)) (H : List (Set α)) : Prop :=
  H ≠ [] ∧ (∀ L ∈ H, L ∈ X) ∧ H.IsChain (fun L M => M ⊂ L)

/-- The space `𝓗` of finite strictly descending chains (1D `History`). -/
def History (X : Set (Set α)) := {H : List (Set α) // IsChain X H}

/-- `end(H)` (1D `chainEnd`). -/
def History.last {X : Set (Set α)} (H : History X) : Set α := H.1.getLastD ∅

/-- `Γ = H⌢M` (1D `History.IsSnoc`). -/
def History.IsSnoc {X : Set (Set α)} (H Γ : History X) (M : Set α) : Prop :=
  M ∈ X ∧ M ⊂ H.last ∧ Γ.1 = H.1 ++ [M]

/-- Basic neighbourhoods, Definition 6.3 (1D `InBasic`). -/
inductive InBasic {X : Set (Set α)} (H : History X) (F : History X → Set α) : History X → Prop
  | base : InBasic H F H
  | step {Γ Γ' : History X} {M : Set α} :
      InBasic H F Γ → History.IsSnoc Γ Γ' M → F Γ ⊆ M → InBasic H F Γ'

/-- Admissible finite tests (1D `FiniteTests`). -/
def FiniteTests {X : Set (Set α)} (F : History X → Set α) : Prop :=
  ∀ Γ, (F Γ).Finite ∧ F Γ ⊆ Γ.last

/-- **Definition 6.3** (`opensets`), ported. -/
def opensets (X : Set (Set α)) : Set (Set (History X)) :=
  {U | ∃ H : History X, ∃ F : History X → Set α, FiniteTests F ∧ U = {Γ | InBasic H F Γ}}

/-- The finite-evidence history topology (1D `historyTopology`). -/
instance historyTopology (X : Set (Set α)) : TopologicalSpace (History X) :=
  TopologicalSpace.generateFrom (opensets X)

/-- `𝓗_K`: histories beginning at `K`. -/
def historiesFrom (X : Set (Set α)) (K : Set α) : Set (History X) := {H | H.1.headD ∅ = K}

/-- The one-language history `(K)`. -/
def History.single {X : Set (Set α)} (K : Set α) (hK : K ∈ X) : History X :=
  ⟨[K], by simp [IsChain, hK]⟩

/-- Well-founded language-labelled trees (1D `LTree`). -/
inductive LTree (α : Type*)
  | leaf (L : Set α)
  | node (L : Set α) (child : ℕ → LTree α)

/-- Root label. -/
def LTree.label : LTree α → Set α
  | leaf L => L
  | node L _ => L

/-- Conditions 2–3 of Definition 3.3 (1D `LTree.Admissible`). -/
def LTree.Admissible (X : Set (Set α)) : LTree α → Prop
  | leaf _ => True
  | node L c =>
      (∀ i, (c i).label ∈ X ∧ (c i).label ⊂ L ∧ LTree.Admissible X (c i)) ∧
      ∀ F : Set α, F.Finite → F ⊆ L → ∃ i, F ⊆ (c i).label

/-- Root-to-leaf paths (1D `LTree.paths`). -/
def LTree.paths : LTree α → Set (List (Set α))
  | leaf L => {[L]}
  | node L c => {P | ∃ i, ∃ Q ∈ LTree.paths (c i), P = L :: Q}

/-- **Definition 3.3** (`def:aot`), ported. -/
def def_aot (X : Set (Set α)) (K : Set α) (T : LTree α) : Prop :=
  T.label = K ∧ T.Admissible X

end Histories

/-- The entries of a nonempty list as a function on `Fin (length - 1 + 1)`. -/
def listFn {β : Type*} (l : List β) (hl : l ≠ []) : Fin (l.length - 1 + 1) → β :=
  fun i => l.get ⟨i.val, by have := List.length_pos_iff.mpr hl; omega⟩


section HistoriesGeneralized
open Topology

/-! ## Section A: Lemmas 6.4 and 6.6 for histories over an arbitrary type -/

namespace HistoriesAux

variable {α : Type*} {X : Set (Set α)}

/-- `H⌢M` as a history, for `M ∈ X` with `M ⊊ end(H)`. -/
def snoc (H : History X) (M : Set α) (hM : M ∈ X) (hlt : M ⊂ H.last) : History X :=
  ⟨H.1 ++ [M], by
    obtain ⟨hne, hX, hc⟩ := H.2
    refine ⟨by simp, ?_, ?_⟩
    · intro L hL
      rcases List.mem_append.1 hL with h | h
      · exact hX L h
      · rw [List.mem_singleton.1 h]; exact hM
    · refine hc.append (List.isChain_singleton M) ?_
      intro x hx y hy
      have hx' : x = H.last := by
        unfold History.last
        rw [List.getLastD_eq_getLast?, hx]; rfl
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hx' hy
      exact hlt⟩

theorem snoc_isSnoc (H : History X) (M : Set α) (hM : M ∈ X) (hlt : M ⊂ H.last) :
    History.IsSnoc H (snoc H M hM hlt) M := ⟨hM, hlt, rfl⟩

/-- The end of `H⌢M` is `M`. -/
theorem IsSnoc.last_eq {H Γ : History X} {M : Set α} (h : History.IsSnoc H Γ M) :
    Γ.last = M := by
  unfold History.last
  rw [h.2.2]; simp

/-- A root-to-leaf path starts with the root label. -/
theorem paths_head {T : LTree α} {P : List (Set α)} (hP : P ∈ T.paths) :
    ∃ Q, P = T.label :: Q := by
  cases T with
  | leaf L => exact ⟨[], hP⟩
  | node L c =>
    obtain ⟨i, Q, -, rfl⟩ := hP
    exact ⟨Q, rfl⟩

/-- Appending the tail of a path starting at `M` to `H⌢M` is appending the path to `H`. -/
theorem append_snoc (H : History X) (M : Set α) (hM : M ∈ X) (hlt : M ⊂ H.last)
    (L : Set α) (Q : List (Set α)) (hQ : ∃ Q', Q = M :: Q') :
    (snoc H M hM hlt).1 ++ Q.tail = H.1 ++ (L :: Q).tail := by
  obtain ⟨Q', rfl⟩ := hQ
  simp [snoc]

/-- Basic neighbourhoods are transitive. -/
theorem inBasic_trans {H Γ : History X} {F G : History X → Set α}
    (hΓ : InBasic H F Γ) (hFG : ∀ Δ, F Δ ⊆ G Δ) {Δ : History X} (hΔ : InBasic Γ G Δ) :
    InBasic H F Δ := by
  induction hΔ with
  | base => exact hΓ
  | step _ hs hM ih => exact InBasic.step ih hs ((hFG _).trans hM)

/-- The basic open sets form a basis of the history topology (first part of Lemma 6.4). -/
theorem isBasis : TopologicalSpace.IsTopologicalBasis (opensets X) := by
  refine ⟨?_, ?_, rfl⟩
  · rintro _ ⟨H₁, F₁, hF₁, rfl⟩ _ ⟨H₂, F₂, hF₂, rfl⟩ Γ ⟨h₁, h₂⟩
    refine ⟨{Δ | InBasic Γ (fun Δ => F₁ Δ ∪ F₂ Δ) Δ},
      ⟨Γ, _, fun Δ => ⟨(hF₁ Δ).1.union (hF₂ Δ).1, union_subset (hF₁ Δ).2 (hF₂ Δ).2⟩, rfl⟩,
      InBasic.base, fun Δ hΔ => ⟨?_, ?_⟩⟩
    · exact inBasic_trans h₁ (fun _ => subset_union_left) hΔ
    · exact inBasic_trans h₂ (fun _ => subset_union_right) hΔ
  · refine eq_univ_of_forall fun H => ?_
    exact ⟨_, ⟨H, fun _ => ∅, fun _ => ⟨finite_empty, empty_subset _⟩, rfl⟩, InBasic.base⟩

/-- The finite-test characterization of open sets (second part of Lemma 6.4). -/
theorem isOpen_iff (U : Set (History X)) : IsOpen U ↔
    ∀ H ∈ U, ∃ F : Set α, F.Finite ∧ F ⊆ H.last ∧
      ∀ Γ : History X, ∀ M, History.IsSnoc H Γ M → F ⊆ M → Γ ∈ U := by
  constructor
  · intro hU H hH
    obtain ⟨t, ⟨H₀, F₀, hF₀, rfl⟩, hHt, htU⟩ := isBasis.exists_subset_of_mem_open hH hU
    exact ⟨F₀ H, (hF₀ H).1, (hF₀ H).2, fun Γ M hs hM => htU (InBasic.step hHt hs hM)⟩
  · intro h
    let F : History X → Set α := fun H => if hH : H ∈ U then (h H hH).choose else ∅
    have hF : FiniteTests F := by
      intro H
      by_cases hH : H ∈ U
      · simp only [F, hH, ↓reduceDIte]
        exact ⟨(h H hH).choose_spec.1, (h H hH).choose_spec.2.1⟩
      · simp only [F, hH, ↓reduceDIte]
        exact ⟨finite_empty, empty_subset _⟩
    have key : ∀ H ∈ U, ∀ Γ, InBasic H F Γ → Γ ∈ U := by
      intro H hH Γ hΓ
      induction hΓ with
      | base => exact hH
      | @step Γ Γ' M _ hs hM ih =>
        have hM' : (h Γ ih).choose ⊆ M := by simpa only [F, ih, ↓reduceDIte] using hM
        exact (h Γ ih).choose_spec.2.2 Γ' M hs hM'
    refine isOpen_iff_forall_mem_open.2 fun H hH => ⟨{Γ | InBasic H F Γ}, key H hH, ?_,
      InBasic.base⟩
    exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨H, F, hF, rfl⟩

/-- **Lemma 6.4** (`lem:history-topology`), generalized from `ℤ` to an arbitrary type `α` (in
particular `α = ℤ^d`): the basic open sets form a basis of the history topology, and `U` is open iff
every `H ∈ U` has a finite `F_H ⊆ end(H)` such that every `M ∈ X` with `F_H ⊆ M ⊊ end(H)` gives
`H⌢M ∈ U`. Port of `BanachDensity1D.lem_history_topology`. -/
theorem lem_history_topology_gen (X : Set (Set α)) :
    TopologicalSpace.IsTopologicalBasis (opensets X) ∧
    ∀ U : Set (History X), IsOpen U ↔
      ∀ H ∈ U, ∃ F : Set α, F.Finite ∧ F ⊆ H.last ∧
        ∀ Γ : History X, ∀ M, History.IsSnoc H Γ M → F ⊆ M → Γ ∈ U :=
  ⟨isBasis, isOpen_iff⟩

/-- Following an admissible obstruction tree rooted at `end(H)` whose appended paths lie in `D`
puts `H` in the closure of `D` (first half of Lemma 6.6). -/
theorem mem_closure_of_tree {D : Set (History X)} (T : LTree α) :
    ∀ H : History X, def_aot X H.last T →
      (∀ P ∈ T.paths, ∃ G ∈ D, G.1 = H.1 ++ P.tail) → H ∈ closure D := by
  induction T with
  | leaf L =>
    intro H hT hP
    obtain ⟨G, hG, hGe⟩ := hP [L] rfl
    have : G = H := Subtype.ext (by simpa using hGe)
    exact subset_closure (this ▸ hG)
  | node L c ih =>
    intro H hT hP
    obtain ⟨hTL, hadm, hcov⟩ := hT
    change L = H.last at hTL
    subst hTL
    rw [mem_closure_iff]
    intro U hU hHU
    obtain ⟨F, hF, hFL, hsn⟩ := (isOpen_iff U).1 hU H hHU
    obtain ⟨i, hi⟩ := hcov F hF hFL
    obtain ⟨hiX, hilt, hiadm⟩ := hadm i
    have hHi : snoc H _ hiX hilt ∈ closure D := by
      refine ih i _ ⟨(IsSnoc.last_eq (snoc_isSnoc H _ hiX hilt)).symm, hiadm⟩ fun Q hQ => ?_
      obtain ⟨G, hG, hGe⟩ := hP (H.last :: Q) ⟨i, Q, hQ, rfl⟩
      exact ⟨G, hG, hGe.trans (append_snoc H _ hiX hilt _ Q (paths_head hQ)).symm⟩
    exact mem_closure_iff.1 hHi U hU (hsn _ _ (snoc_isSnoc H _ hiX hilt) hi)

/-- The histories admitting an admissible obstruction tree whose appended paths lie in `D` form a
closed set (second half of Lemma 6.6). Countability of `α` makes the finite subsets of `end(H)`
countable, so they can index the children of one tree vertex. -/
theorem isClosed_treeSet [Countable α] (D : Set (History X)) :
    IsClosed {H : History X | ∃ T : LTree α, def_aot X H.last T ∧
      ∀ P ∈ T.paths, ∃ G ∈ D, G.1 = H.1 ++ P.tail} := by
  rw [← isOpen_compl_iff, isOpen_iff]
  intro H hH
  by_contra hne
  push Not at hne
  apply hH
  have hS : {F : Set α | F.Finite ∧ F ⊆ H.last}.Countable :=
    Set.countable_ofPred_finite_subset (Set.to_countable _)
  obtain ⟨e, he⟩ := hS.exists_eq_range ⟨∅, finite_empty, empty_subset _⟩
  have he' : ∀ i, (e i).Finite ∧ e i ⊆ H.last := fun i => by
    have : e i ∈ range e := mem_range_self i
    rw [← he] at this
    exact this
  choose Γ M hs hFM hW using fun i => hne (e i) (he' i).1 (he' i).2
  simp only [mem_compl_iff, not_not] at hW
  choose T hT hTP using hW
  refine ⟨LTree.node H.last T, ⟨rfl, ?_, ?_⟩, ?_⟩
  · intro i
    have hl : (T i).label = M i := (hT i).1.trans (IsSnoc.last_eq (hs i))
    rw [hl]
    exact ⟨(hs i).1, (hs i).2.1, (hT i).2⟩
  · intro F hF hFL
    have : F ∈ range e := by rw [← he]; exact ⟨hF, hFL⟩
    obtain ⟨i, rfl⟩ := this
    exact ⟨i, (hFM i).trans (((hT i).1.trans (IsSnoc.last_eq (hs i))).symm ▸ subset_rfl)⟩
  · rintro P ⟨i, Q, hQ, rfl⟩
    obtain ⟨G, hG, hGe⟩ := hTP i Q hQ
    refine ⟨G, hG, hGe.trans ?_⟩
    obtain ⟨Q', rfl⟩ := paths_head hQ
    have hl : (T i).label = M i := (hT i).1.trans (IsSnoc.last_eq (hs i))
    rw [hl, (hs i).2.2]
    simp

/-- **Lemma 6.6** (`lem:obstruction-closure`), generalized from `ℤ` to a countable type `α` (in
particular `α = ℤ^d`): `H` is in the closure of `D` iff some admissible obstruction tree rooted at
`end(H)` has every root-to-leaf path `P`, appended to `H` (as `H ++ P.tail`, the common language
`end(H)` written once), producing a history in `D`. The paper's restriction to `D ⊆ 𝓗_A`, `H ∈ 𝓗_A`
is not needed. Port of `BanachDensity1D.lem_obstruction_closure`. -/
theorem lem_obstruction_closure_gen [Countable α] (D : Set (History X)) (H : History X) :
    H ∈ closure D ↔ ∃ T : LTree α, def_aot X H.last T ∧
      ∀ P ∈ T.paths, ∃ G ∈ D, G.1 = H.1 ++ P.tail := by
  constructor
  · intro hcl
    refine closure_minimal (fun G hG => ?_) (isClosed_treeSet D) hcl
    refine ⟨LTree.leaf G.last, ⟨rfl, trivial⟩, fun P hP => ⟨G, hG, ?_⟩⟩
    rw [show P = [G.last] from hP]
    simp
  · rintro ⟨T, hT, hP⟩
    exact mem_closure_of_tree T H hT hP

end HistoriesAux

end HistoriesGeneralized

end BanachDensityHD
