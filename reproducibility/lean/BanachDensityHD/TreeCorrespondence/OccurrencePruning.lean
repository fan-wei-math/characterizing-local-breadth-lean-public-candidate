import BanachDensityHD.TreeCorrespondence.Occurrence

/-! # Pruning original occurrence addresses before decorated-path merging. -/
namespace BanachDensityHD.TreeCorrespondence
open Set
open scoped Classical
namespace OccurrenceTree
variable {ι : Type*} {d : ℕ} (T : OccurrenceTree ι d)

/-- Choose a child of this ACTUAL occurrence, not of an encoded decorated path. -/
noncomputable def chosenChild (p : List ι) (M : Set (Pt d)) : ι :=
  if hc : ∃ i, p ++ [i] ∈ T.paths ∧ T.language (p ++ [i]) = M then hc.choose else T.root

/-- Every edge of an original address uses the chosen child at its original
parent occurrence. The choice still depends on the entire address. -/
def Retained (p : List ι) : Prop :=
  ∀ i (hi : i + 1 < p.length),
    p[i + 1] = T.chosenChild (p.take (i + 1)) (T.language (p.take (i + 1 + 1)))

lemma retained_prefix {p : List ι} (hp : T.Retained p) (n : ℕ) : T.Retained (p.take n) := by
  intro i hi
  have hi0 : i + 1 < p.length := by simp only [List.length_take] at hi; omega
  have hn : i + 1 + 1 ≤ n := by simp only [List.length_take] at hi; omega
  simpa only [List.getElem_take, List.take_take, Nat.min_eq_left (by omega : i + 1 ≤ n),
    Nat.min_eq_left hn] using hp i hi0

lemma retained_child {p : List ι} (hp : T.Retained p) (hne : p ≠ [])
    {i : ι} (hi : i = T.chosenChild p (T.language (p ++ [i]))) : T.Retained (p ++ [i]) := by
  intro j hj
  have hlen : 0 < p.length := List.length_pos_iff.mpr hne
  by_cases hlt : j + 1 < p.length
  · rw [List.getElem_append_left hlt,
      List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega)]
    exact hp j hlt
  · have he : j + 1 = p.length := by simp only [List.length_append, List.length_singleton] at hj; omega
    simpa only [he, List.getElem_append_right (by omega : p.length ≤ p.length),
      Nat.sub_self, List.getElem_cons_zero, List.take_append_of_le_length le_rfl,
      List.take_of_length_le le_rfl, List.take_of_length_le (by simp : (p ++ [i]).length ≤ p.length + 1)]
      using hi

lemma retained_last {p : List ι} {v : ι} (hp : T.Retained (p ++ [v])) (hne : p ≠ []) :
    v = T.chosenChild p (T.language (p ++ [v])) := by
  have hlen := List.length_pos_iff.mpr hne
  have hh := hp (p.length - 1) (by simp only [List.length_append, List.length_singleton]; omega)
  have he : p.length - 1 + 1 = p.length := by omega
  simpa only [he, List.getElem_append_right (le_refl p.length), Nat.sub_self,
    List.getElem_cons_zero, List.take_append_of_le_length le_rfl,
    List.take_of_length_le le_rfl, List.take_of_length_le (by simp : (p ++ [v]).length ≤ p.length + 1)]
    using hh

/-- The paper's pruning, literally on original addresses. All occurrence data,
root, and retained paths are unchanged. At each retained parent there is at
most one child with any given language. No encoded-tree quotient is used. -/
theorem prune_original {X : Set (Set (Pt d))} {h : ℕ → ℝ}
    {q : Set (Pt d) → ℝ} {K : Set (Pt d)} (ht : T.Protected X h q K) :
    ∃ S : OccurrenceTree ι d, S.Protected X h q K ∧ S.root = T.root ∧
      S.paths ⊆ T.paths ∧ S.language = T.language ∧ S.protectedSet = T.protectedSet ∧
      S.cutoff = T.cutoff ∧ S.radius = T.radius ∧
      ∀ p i j, p ++ [i] ∈ S.paths → p ++ [j] ∈ S.paths →
        T.language (p ++ [i]) = T.language (p ++ [j]) → i = j := by
  let S : OccurrenceTree ι d := { T with
    paths := {p | p ∈ T.paths ∧ T.Retained p}
    root_mem := ⟨T.root_mem, by intro i hi; simp only [List.length_singleton] at hi; omega⟩
    head := fun p hp => T.head p hp.1
    prefix_closed := fun p hp n hn => ⟨T.prefix_closed p hp.1 n hn, T.retained_prefix hp.2 n⟩
    countable := T.countable.mono (fun _ hp => hp.1) }
  have hS : S.Protected X h q K := by
    refine ⟨ht.1, ?_, ?_, ?_, ?_⟩
    · intro p hp; exact ht.2.1 p hp.1
    · intro p hp i hi; exact ht.2.2.1 p hp.1 i hi.1
    · intro p hp M hM hPM hML
      have hc := ht.2.2.2.1 p hp.1 M hM hPM hML
      have he : T.chosenChild p M = hc.choose := by
        unfold chosenChild
        rw [dite_eq_left hc]
      have hchild : p ++ [T.chosenChild p M] ∈ T.paths := he.symm ▸ hc.choose_spec.1
      have hlang : T.language (p ++ [T.chosenChild p M]) = M := he.symm ▸ hc.choose_spec.2
      refine ⟨T.chosenChild p M, ⟨hchild, ?_⟩, hlang⟩
      exact T.retained_child hp.2 (T.nonempty hp.1) (by rw [hlang])
    · intro p hp; exact ht.2.2.2.2 p hp.1
  refine ⟨S, hS, rfl, fun _ hp => hp.1, rfl, rfl, rfl, rfl, ?_⟩
  intro p i j hi hj he
  by_cases hp : p = []
  · subst p
    have hei : i = T.root := by simpa using T.head _ hi.1
    have hej : j = T.root := by simpa using T.head _ hj.1
    exact hei.trans hej.symm
  · have hpi := T.retained_last hi.2 hp
    have hpj := T.retained_last hj.2 hp
    exact hpi.trans ((congrArg (T.chosenChild p) he).trans hpj.symm)
/-- Language histories retain all prefixes of the original occurrence address. -/
noncomputable def languageHistory (p : List ι) : List (Set (Pt d)) :=
  (CharAux.pathG T.data p).map Deco.L

/-- After original-address pruning, a whole language history determines its
unique original occurrence. Thus its cutoff/radius are genuinely well-defined
before any decorated-path encoding or merging. -/
theorem languageHistory_injective
    (hd : ∀ p i j, p ++ [i] ∈ T.paths → p ++ [j] ∈ T.paths →
      T.language (p ++ [i]) = T.language (p ++ [j]) → i = j)
    {p r : List ι} (hp : p ∈ T.paths) (hr : r ∈ T.paths)
    (he : T.languageHistory p = T.languageHistory r) : p = r := by
  have hlen : p.length = r.length := by
    have hh := congrArg List.length he
    simpa only [languageHistory, List.length_map, CharAux.pathG_length] using hh
  have hpre : ∀ n, n ≤ p.length → p.take n = r.take n := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      have hnp : n < p.length := by omega
      have hnr : n < r.length := by omega
      have hpt : p.take (n + 1) = p.take n ++ [p[n]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hnp]; rfl
      have hrt : r.take (n + 1) = r.take n ++ [r[n]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hnr]; rfl
      have hlab := List.getElem_of_eq he (by
        simp only [languageHistory, List.length_map, CharAux.pathG_length]; exact hnp)
      simp only [languageHistory, List.getElem_map, CharAux.pathG_getElem, data, Deco.L] at hlab
      have hpc : p.take n ++ [p[n]] ∈ T.paths := hpt ▸ T.prefix_closed p hp _ (by omega)
      have hrc : p.take n ++ [r[n]] ∈ T.paths := by
        rw [hprev, ← hrt]; exact T.prefix_closed r hr _ (by omega)
      have hlabel : T.language (p.take n ++ [p[n]]) = T.language (p.take n ++ [r[n]]) := by
        rw [← hpt, hprev, ← hrt]; exact hlab
      have hei := hd _ _ _ hpc hrc hlabel
      rw [hpt, hrt, hprev, hei]
  have hh := hpre p.length le_rfl
  simpa only [List.take_of_length_le le_rfl, List.take_of_length_le (by omega : r.length ≤ p.length)] using hh
end OccurrenceTree
end BanachDensityHD.TreeCorrespondence
