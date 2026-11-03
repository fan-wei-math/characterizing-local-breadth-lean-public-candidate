import BanachDensityHD.TreeCorrespondence.Decoration
import BanachDensityHD.TreeCorrespondence.Occurrence
import BanachDensityHD.TreeCorrespondence.VertexObstruction
import BanachDensityHD.TreeCorrespondence.Pruning
import BanachDensityHD.TreeCorrespondence.OccurrencePruning

/-! # Kernel witnesses for the Nov. 1 proof route. -/
namespace BanachDensityHD.TreeCorrespondence
open Set Topology CharAux
open scoped Classical

variable {d : ℕ} {X : Set (Set (Pt d))} {h : ℕ → ℝ}
  {q : Set (Pt d) → ℝ} {K : Set (Pt d)}

/-- The boundary-safe extension in Corollary 7.8, exposed separately. Values on
U and its prefix cutoffs are preserved exactly, not merely replaced by a
different good assignment. Outside radii dominate inside-prefix absolute radii
and increase with history length. -/
theorem global_extension (hK : K ∈ X) {U : Set (History X)}
    {s a : List (Set (Pt d)) → ℝ} (hU : IsQGoodDecoration X h q K hK U s a) :
    ∃ s' a' : List (Set (Pt d)) → ℝ,
      (∀ H, IsChain X H → H.headD ∅ = K → 1 ≤ s' H ∧ 0 ≤ a' H) ∧
      (∀ H M, IsChain X (H ++ [M]) → H ≠ [] → H.headD ∅ = K → a' H < a' (H ++ [M])) ∧
      (∀ H ∈ U, s' H.val = s H.val ∧ a' H.val = a H.val) ∧
      (∀ H ∈ U, DecoratedGood h q s' a' H.val H.property.1) := by
  obtain ⟨hUK, hUo, hUs, hUpre, hUsa, hUa, hUg⟩ := hU
  let f : List (Set (Pt d)) → ℝ := fun l => if InU X U l then |a l| else 0
  have hf0 : ∀ l, 0 ≤ f l := fun l => by simp only [f]; split_ifs <;> positivity
  let A : List (Set (Pt d)) → ℝ := fun l =>
    (∑ n ∈ Finset.range (l.length + 1), f (l.take n)) + l.length
  let s' : List (Set (Pt d)) → ℝ := fun l => if InU X U l then s l else 1
  let a' : List (Set (Pt d)) → ℝ := fun l => if InU X U l then a l else A l
  have hA0 : ∀ l, 0 ≤ A l := fun l => by
    have := Finset.sum_nonneg fun n (_ : n ∈ Finset.range (l.length + 1)) => hf0 (l.take n)
    simp only [A]; positivity
  have hAsnoc : ∀ H M, A H + 1 ≤ A (H ++ [M]) ∧ f H + 1 ≤ A (H ++ [M]) := by
    intro H M
    have hsum : ∑ n ∈ Finset.range ((H ++ [M]).length + 1), f ((H ++ [M]).take n) =
        (∑ n ∈ Finset.range (H.length + 1), f (H.take n)) + f (H ++ [M]) := by
      rw [show (H ++ [M]).length + 1 = H.length + 1 + 1 by simp, Finset.sum_range_succ]
      congr 1
      · refine Finset.sum_congr rfl fun n hn => ?_
        rw [List.take_append_of_le_length (by simp at hn; omega)]
      · rw [List.take_of_length_le (by simp)]
    have hle : f H ≤ ∑ n ∈ Finset.range (H.length + 1), f (H.take n) := by
      have := Finset.single_le_sum (fun n (_ : n ∈ Finset.range (H.length + 1)) => hf0 (H.take n))
        (Finset.self_mem_range_succ H.length)
      rwa [List.take_of_length_le le_rfl] at this
    have e : A (H ++ [M]) = (∑ n ∈ Finset.range (H.length + 1), f (H.take n)) +
        f (H ++ [M]) + H.length + 1 := by
      simp only [A]; rw [hsum]; simp only [List.length_append, List.length_singleton]; push_cast
      ring
    have eA : A H = (∑ n ∈ Finset.range (H.length + 1), f (H.take n)) + H.length := rfl
    have := hf0 (H ++ [M])
    have : (0 : ℝ) ≤ H.length := Nat.cast_nonneg _
    rw [e, eA]
    constructor <;> linarith
  have hInU_take : ∀ l, InU X U l → ∀ n, 1 ≤ n → InU X U (l.take n) := fun l hl n hn =>
    ⟨isChain_take hl.1 hn, hUpre _ hl.2 n hn (isChain_take hl.1 hn)⟩
  refine ⟨s', a', ?_, ?_, ?_, ?_⟩
  · intro H _ _
    simp only [s', a']
    split_ifs with hH
    · exact hUsa _ hH.2
    · exact ⟨le_rfl, hA0 H⟩
  · intro H M hc hne hhead
    have hHc : IsChain X H := by
      have := isChain_take hc (n := H.length) (by have := List.length_pos_iff.mpr hne; omega)
      rwa [List.take_append_of_le_length le_rfl, List.take_of_length_le le_rfl] at this
    by_cases hHM : InU X U (H ++ [M])
    · have hH : InU X U H := by
        have := hInU_take _ hHM H.length (by have := List.length_pos_iff.mpr hne; omega)
        rwa [List.take_append_of_le_length le_rfl, List.take_of_length_le le_rfl] at this
      simp only [a', if_pos hH, if_pos hHM]
      have hlt : M ⊂ H.getLastD ∅ := by
        have hi := isChain_getElem hc (H.length - 1)
          (by simp; have := List.length_pos_iff.mpr hne; omega)
        have hlen := List.length_pos_iff.mpr hne
        rw [List.getElem_append_right (by omega), List.getElem_append_left (by omega)] at hi
        rw [getLastD_eq_getLast _ _ hne, List.getLast_eq_getElem]
        simpa [show H.length - 1 + 1 - H.length = 0 by omega] using hi
      exact hUa ⟨H, hHc⟩ hH.2 ⟨H ++ [M], hc⟩ hHM.2 M
        ⟨hc.2.1 M (by simp), hlt, rfl⟩
    · simp only [a', if_neg hHM]
      by_cases hH : InU X U H
      · simp only [if_pos hH]
        have := (hAsnoc H M).2
        simp only [f, if_pos hH] at this
        linarith [le_abs_self (a H)]
      · simp only [if_neg hH]
        linarith [(hAsnoc H M).1]
  · intro H hH
    have hi : InU X U H.val := ⟨H.property, hH⟩
    simp only [s', a', if_pos hi, and_self]
  · intro H hH
    have hi : InU X U H.val := ⟨H.property, hH⟩
    have hap : a' H.val = a H.val := by simp only [a', if_pos hi]
    have hsp : (fun i : Fin (H.val.length - 1 + 1) => s' (H.val.take (i.val + 1))) =
        (fun i => s (H.val.take (i.val + 1))) := by
      funext i
      simp only [s', if_pos (hInU_take H.val hi (i.val + 1) (by omega))]
    unfold DecoratedGood
    rw [hap, hsp]
    exact hUg H hH

/-- Basis shrinking used in the written reverse proof of Theorem 7.7. All
finite tests are indexed by histories. The restricted decoration keeps the
original s and a on every retained prefix. -/
theorem shrink_to_basic (hK : K ∈ X) {U : Set (History X)}
    {s a : List (Set (Pt d)) → ℝ} (hU : IsQGoodDecoration X h q K hK U s a) :
    ∃ F : History X → Set (Pt d),
      PaperBasic (History.single K hK) F {Γ | InBasic (History.single K hK) F Γ} ∧
      {Γ | InBasic (History.single K hK) F Γ} ⊆ U ∧
      IsQGoodDecoration X h q K hK {Γ | InBasic (History.single K hK) F Γ} s a := by
  have hopen := (HistoriesAux.isOpen_iff U).1 hU.2.1
  choose Fs hfin hsub he using hopen
  let F : History X → Set (Pt d) := fun H => if hH : H ∈ U then Fs H hH else ∅
  have hF : FiniteTests F := by
    intro H
    dsimp [F]
    split_ifs with hh
    · exact ⟨hfin H hh, hsub H hh⟩
    · exact ⟨Set.finite_empty, Set.empty_subset _⟩
  have hSU : {Γ | InBasic (History.single K hK) F Γ} ⊆ U := by
    apply basic_sub F ?_ hU.2.2.1
    intro H hH Γ M hs hM
    exact he H hH Γ M hs (by simpa only [F, dite_eq_left hH] using hM)
  refine ⟨F, (paperBasic_iff _ _ _).2 ⟨hF, rfl⟩, hSU, ?_⟩
  refine ⟨fun Γ hΓ => basic_head hK F Γ hΓ, ?_, InBasic.base,
    basic_prefix hK F, ?_, ?_, ?_⟩
  · exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨_, F, hF, rfl⟩
  · intro H hH; exact hU.2.2.2.2.1 H (hSU hH)
  · intro H hH Γ hΓ M hs; exact hU.2.2.2.2.2.1 H (hSU hH) Γ (hSU hΓ) M hs
  · intro H hH; exact hU.2.2.2.2.2.2 H (hSU hH)

/-- Selection is coherent at every prefix. This is the actual pruning lemma,
not independent choices of an occurrence for each endpoint language. -/
theorem pruning_prefixes (T : DTree d) {H : List (Set (Pt d))}
    (hH : SelGood T H) (n : ℕ) (hn : 1 ≤ n) :
    SelGood T (H.take n) ∧ sel T (H.take n) = (sel T H).take n :=
  selGood_take T hH hn

/-- A retained one-step history uses one actual child of its selected parent. -/
theorem pruning_child (T : DTree d) {H : List (Set (Pt d))} {M : Set (Pt d)}
    (hHM : SelGood T (H ++ [M])) :
    (H = [] ∨ SelGood T H) ∧ ∃ w, w.L = M ∧ sel T (H ++ [M]) = sel T H ++ [w] :=
  selGood_snoc T hHM

/-- Theorem 7.7 on occurrence trees and partial manuscript decorations.
The reverse direction explicitly passes through the basic neighborhood from
the written proof. No growth lower bound is needed for this qualitative step. -/
theorem paper_topological_characterization (hX : X.Countable) (hK : K ∈ X) :
    (∃ (ι : Type) (T : OccurrenceTree ι d), T.Protected X h q K) ↔
      Nonempty (PaperDecoration X h q K hK) := by
  constructor
  · rintro ⟨ι, T, ht⟩
    obtain ⟨S, hS, _, _, _, _, _, _, _⟩ := T.prune_original ht
    obtain ⟨U, s, a, hU⟩ := deco_of_tree hK (S.encode_protected hS)
    exact ⟨PaperDecoration.ofLean hU⟩
  · rintro ⟨D⟩
    obtain ⟨F, _, _, hV⟩ := shrink_to_basic hK D.toLean
    obtain ⟨T, hT⟩ := tree_of_deco hX hK hV
    exact ⟨Deco d, OccurrenceTree.ofDTree T, OccurrenceTree.ofDTree_protected hT⟩

/-- Corollary 7.8 with all countable well-founded branching types, in the
manuscript quantifier order: one assignment, then every obstruction tree. -/
theorem paper_obstruction_characterization (hX : X.Countable) (hK : K ∈ X) :
    (∃ (ι : Type) (T : OccurrenceTree ι d), T.Protected X h q K) ↔
      ∃ s a : List (Set (Pt d)) → ℝ,
        (∀ H, IsChain X H → H.headD ∅ = K → 1 ≤ s H ∧ 0 ≤ a H) ∧
        (∀ H M, IsChain X (H ++ [M]) → H ≠ [] → H.headD ∅ = K → a H < a (H ++ [M])) ∧
        ∀ T : PaperObstruction (Pt d), T.label = K → T.admissible X →
          ∃ P ∈ T.paths, ∃ hP : P ≠ [], DecoratedGood h q s a P hP := by
  rw [paperProtectedTree_iff]
  constructor
  · rintro ⟨T, hT⟩
    obtain ⟨s, a, hb, hi, hp⟩ := assignment_of_tree hK hT
    exact ⟨s, a, hb, hi, (all_obstructions_iff X K _).2 hp⟩
  · rintro ⟨s, a, hb, hi, hp⟩
    exact tree_of_assignment hX hK s a hb hi ((all_obstructions_iff X K _).1 hp)

/-- The assignment obtained above works for every countable vertex presentation,
with actual root-to-leaf paths, not just for inductively supplied trees. -/
theorem all_vertex_obstructions (hX : X.Countable) (hK : K ∈ X)
    (hT : ∃ (ι : Type) (T : OccurrenceTree ι d), T.Protected X h q K) :
    ∃ s a : List (Set (Pt d)) → ℝ,
      (∀ H, IsChain X H → H.headD ∅ = K → 1 ≤ s H ∧ 0 ≤ a H) ∧
      (∀ H M, IsChain X (H ++ [M]) → H ≠ [] → H.headD ∅ = K → a H < a (H ++ [M])) ∧
      ∀ (V : Type) [Countable V] (T : VertexObstruction V (Pt d)),
        T.label T.root = K → T.Admissible X →
          ∃ P, T.Terminal T.root P ∧ ∃ hP : P ≠ [], DecoratedGood h q s a P hP := by
  obtain ⟨s, a, hb, hi, ht⟩ := (paper_obstruction_characterization hX hK).1 hT
  refine ⟨s, a, hb, hi, ?_⟩
  intro V _ T he ha
  exact T.transfer_terminal ha (fun S hs hsa => ht S (hs.trans he) hsa)

end BanachDensityHD.TreeCorrespondence
