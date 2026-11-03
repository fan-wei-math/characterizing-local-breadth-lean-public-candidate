import BanachDensity1D.Basic

/-!
# Section 3: chains, pairing scores, admissible obstruction trees, `b_n(K)`

Kleinberg–Wei, Part *Dimension one*, Section 3.1–3.2.

* A *chain* (finite refinement history) `H = (A = L₀ ⊋ L₁ ⊋ ⋯ ⊋ L_d)` of languages in `X` is a
  nonempty list, strictly decreasing for `⊂` (`IsChain`). Its first entry is its starting
  language and its last entry its end.
* Its *layers* are `L_d, L_{d-1} \ L_d, …, L₀ \ L₁` (`layers`).
* A *relative interval* of `A` is a set of consecutive points of `A`, i.e. `A ∩ [a, b]`.
* `p(H,J)` is the raw pairing score (Definition 3.1, equation (6)) and `c_n(H)` the pairing score (8).
  In (8) the paper writes "`J` a relative interval of `K`" for a chain starting at a language
  `A`; we read `K` as the chain's starting language (every use has `H` starting at `K`, or, in
  Section 6.3, at the language `A` of the safety requirement).
* Admissible obstruction trees (Definition 3.3) are represented as well-founded trees whose
  vertices carry a language and whose children are indexed by `ℕ` (`LTree`). A term of an
  inductive type has no infinite path, which is condition 4; countably many children are listed
  by a function on `ℕ` (repetitions allowed).
-/

namespace BanachDensity1D

open Set Filter

/-- A chain of languages of `X`: a nonempty list `L₀ ⊋ L₁ ⊋ ⋯ ⊋ L_d` of members of `X`. -/
def IsChain (X : Set (Set ℤ)) (H : List (Set ℤ)) : Prop :=
  H ≠ [] ∧ (∀ L ∈ H, L ∈ X) ∧ H.IsChain (fun L M => M ⊂ L)

/-- The starting language `L₀` of a chain (`∅` for the empty list, which is not a chain). -/
def start (H : List (Set ℤ)) : Set ℤ := H.headD ∅

/-- The end `end(H) = L_d` of a chain (`∅` for the empty list, which is not a chain). -/
def chainEnd (H : List (Set ℤ)) : Set ℤ := H.getLastD ∅

/-- The layers `L₀ \ L₁, L₁ \ L₂, …, L_{d-1} \ L_d, L_d` of a chain. -/
def layers : List (Set ℤ) → List (Set ℤ)
  | [] => []
  | [L] => [L]
  | L :: M :: t => (L \ M) :: layers (M :: t)

/-- A relative interval of `A`: a set of consecutive points of `A`, i.e. `A ∩ [a, b]`. -/
def IsRelInterval (A J : Set ℤ) : Prop := ∃ a b : ℤ, J = A ∩ Icc a b

/-- **Definition 3.1** (`def:raw-pairing-score`), equation (6): the raw pairing score
`p(H,J) = (1/|J|) ∑_{layers E of H} ⌊|E ∩ J| / 2⌋`. -/
noncomputable def def_raw_pairing_score (H : List (Set ℤ)) (J : Set ℤ) : ℝ :=
  (1 / (J.ncard : ℝ)) * ((layers H).map fun E => (((E ∩ J).ncard / 2 : ℕ) : ℝ)).sum

/-- The relative intervals `J` of the starting language of `H` with `|J| ≥ n` and
`J ∩ [-R, R] = ∅`, over which the infimum in (8) is taken. -/
def farIntervals (H : List (Set ℤ)) (n R : ℕ) : Set (Set ℤ) :=
  {J | IsRelInterval (start H) J ∧ n ≤ J.ncard ∧ Disjoint J (Icc (-(R : ℤ)) R)}

/-- The pairing score, equation (8) (`eq:cn`):
`c_n(H) = lim_{R → ∞} inf {p(H,J) : J a relative interval, |J| ≥ n, J ∩ [-R,R] = ∅}`. -/
noncomputable def cn (H : List (Set ℤ)) (n : ℕ) : ℝ :=
  limUnder atTop fun R : ℕ => ⨅ J : farIntervals H n R, def_raw_pairing_score H J

namespace ChainsAux

open Topology

/-- The layer sum `∑_{E a layer of H} ⌊|E ∩ J| / 2⌋`, the numerator of the raw pairing score
`def_raw_pairing_score H J`. -/
noncomputable def layerSum (H : List (Set ℤ)) (J : Set ℤ) : ℕ :=
  ((layers H).map fun E => (E ∩ J).ncard / 2).sum

/-- The raw pairing score is the layer sum divided by `|J|`. -/
lemma score_eq (H : List (Set ℤ)) (J : Set ℤ) :
    def_raw_pairing_score H J = (1 / (J.ncard : ℝ)) * (layerSum H J : ℝ) := by
  simp only [def_raw_pairing_score, layerSum, Nat.cast_list_sum, List.map_map]
  rfl

/-- Raw pairing scores are nonnegative. -/
theorem raw_score_nonneg (H : List (Set ℤ)) (J : Set ℤ) : 0 ≤ def_raw_pairing_score H J := by
  unfold def_raw_pairing_score
  apply mul_nonneg (by positivity)
  apply List.sum_nonneg
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨E, -, rfl⟩ := hx
  positivity

/-- For an infinite starting language, the index family of the infimum in (8) is nonempty. -/
theorem farIntervals_nonempty {H : List (Set ℤ)} (hA : (start H).Infinite) (n R : ℕ) :
    (farIntervals H n R).Nonempty := by
  set A := start H
  have hsplit : A \ Icc (-(R : ℤ)) R ⊆ (A ∩ Ioi (R : ℤ)) ∪ (A ∩ Iio (-(R : ℤ))) := by
    rintro x ⟨hxA, hx⟩
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · exact Or.inr ⟨hxA, hx⟩
    · exact Or.inl ⟨hxA, hx⟩
  have hinf : (A \ Icc (-(R : ℤ)) R).Infinite := hA.sdiff (finite_Icc _ _)
  have hu := (hinf.mono hsplit)
  rcases infinite_union.mp hu with hpos | hneg
  · obtain ⟨t, htK, htn⟩ := hpos.exists_subset_card_eq n
    obtain ⟨b, hb⟩ := (t : Set ℤ).toFinite.bddAbove
    refine ⟨A ∩ Icc ((R : ℤ) + 1) b, ⟨(R : ℤ) + 1, b, rfl⟩, ?_, ?_⟩
    · have hsub : (t : Set ℤ) ⊆ A ∩ Icc ((R : ℤ) + 1) b := fun x hx =>
        ⟨(htK hx).1, by have := (htK hx).2; simp only [mem_Ioi] at this; omega, hb hx⟩
      have hfin : (A ∩ Icc ((R : ℤ) + 1) b).Finite := (finite_Icc _ _).subset inter_subset_right
      calc n = (t : Set ℤ).ncard := by rw [ncard_coe_finset, htn]
        _ ≤ _ := ncard_le_ncard hsub hfin
    · rw [Set.disjoint_left]
      rintro x ⟨-, hx1, -⟩ ⟨-, hx2⟩
      omega
  · obtain ⟨t, htK, htn⟩ := hneg.exists_subset_card_eq n
    obtain ⟨a, ha⟩ := (t : Set ℤ).toFinite.bddBelow
    refine ⟨A ∩ Icc a (-(R : ℤ) - 1), ⟨a, -(R : ℤ) - 1, rfl⟩, ?_, ?_⟩
    · have hsub : (t : Set ℤ) ⊆ A ∩ Icc a (-(R : ℤ) - 1) := fun x hx =>
        ⟨(htK hx).1, ha hx, by have := (htK hx).2; simp only [mem_Iio] at this; omega⟩
      have hfin : (A ∩ Icc a (-(R : ℤ) - 1)).Finite := (finite_Icc _ _).subset inter_subset_right
      calc n = (t : Set ℤ).ncard := by rw [ncard_coe_finset, htn]
        _ ≤ _ := ncard_le_ncard hsub hfin
    · rw [Set.disjoint_left]
      rintro x ⟨-, -, hx1⟩ ⟨hx2, -⟩
      omega

/-- Layers of a strictly descending list: `∑ ⌊|E ∩ J| / 2⌋ ≤ |head ∩ J| / 2` for finite `J`. -/
theorem layers_sum_le (J : Set ℤ) (hJ : J.Finite) :
    ∀ (L : Set ℤ) (t : List (Set ℤ)), (L :: t).IsChain (fun L M => M ⊂ L) →
      ((layers (L :: t)).map fun E => (((E ∩ J).ncard / 2 : ℕ) : ℝ)).sum ≤
        ((L ∩ J).ncard : ℝ) / 2
  | L, [], _ => by
    simp only [layers, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    have h := Nat.cast_div_le (α := ℝ) (m := (L ∩ J).ncard) (n := 2)
    simpa using h
  | L, M :: t, h => by
    have hML : M ⊂ L := (List.isChain_cons_cons.mp h).1
    have ht : (M :: t).IsChain (fun L M => M ⊂ L) := (List.isChain_cons_cons.mp h).2
    have ih := layers_sum_le J hJ M t ht
    simp only [layers, List.map_cons, List.sum_cons] at ih ⊢
    have hfin : (L ∩ J).Finite := hJ.subset inter_subset_right
    have hsub : M ∩ J ⊆ L ∩ J := inter_subset_inter_left _ hML.1
    have hsplit : ((L \ M) ∩ J).ncard + (M ∩ J).ncard = (L ∩ J).ncard := by
      rw [show (L \ M) ∩ J = (L ∩ J) \ (M ∩ J) by ext x; simp; tauto]
      exact ncard_sdiff_add_ncard_of_subset hsub hfin
    have h1 : ((((L \ M) ∩ J).ncard / 2 : ℕ) : ℝ) ≤ (((L \ M) ∩ J).ncard : ℝ) / 2 :=
      Nat.cast_div_le
    have h2 : (((L \ M) ∩ J).ncard : ℝ) + (M ∩ J).ncard = (L ∩ J).ncard := by
      exact_mod_cast hsplit
    linarith

/-- For a nonempty strictly descending list, `p(H, J) ≤ 1/2` (the layers are disjoint). -/
theorem raw_score_le_half {H : List (Set ℤ)} (hne : H ≠ [])
    (h : H.IsChain (fun L M => M ⊂ L)) (J : Set ℤ) :
    def_raw_pairing_score H J ≤ 1 / 2 := by
  obtain ⟨L, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  unfold def_raw_pairing_score
  by_cases hJ : J.Finite
  · have hs := layers_sum_le J hJ L t h
    have hLJ : ((L ∩ J).ncard : ℝ) ≤ J.ncard := by
      exact_mod_cast ncard_le_ncard inter_subset_right hJ
    rcases Nat.eq_zero_or_pos J.ncard with h0 | hpos
    · simp [h0]
    · have hp : (0 : ℝ) < J.ncard := by exact_mod_cast hpos
      rw [one_div_mul_eq_div, div_le_iff₀ hp]
      linarith
  · simp [Set.Infinite.ncard hJ]

/-- The inner infimum of (8). -/
noncomputable def cnSeq (H : List (Set ℤ)) (n : ℕ) (R : ℕ) : ℝ :=
  ⨅ J : farIntervals H n R, def_raw_pairing_score H J

/-- The scores in the inner infimum of (8) are bounded below (witness `0`, see
`raw_score_nonneg`). -/
theorem cnSeq_bddBelow (H : List (Set ℤ)) (n R : ℕ) :
    BddBelow (range fun J : farIntervals H n R => def_raw_pairing_score H J) :=
  ⟨0, by rintro _ ⟨J, rfl⟩; exact raw_score_nonneg H J⟩

/-- The inner infimum is nondecreasing in `R` (infinite start). -/
theorem cnSeq_mono {H : List (Set ℤ)} (hA : (start H).Infinite) (n : ℕ) :
    Monotone (cnSeq H n) := by
  intro R R' hRR'
  have : Nonempty (farIntervals H n R') := (farIntervals_nonempty hA n R').to_subtype
  refine le_ciInf fun J => ?_
  refine ciInf_le (cnSeq_bddBelow H n R) ⟨J.1, J.2.1, J.2.2.1, ?_⟩
  exact J.2.2.2.mono_right (Icc_subset_Icc (by omega) (by exact_mod_cast hRR'))

/-- The inner infimum is nondecreasing in `n` (infinite start). -/
theorem cnSeq_mono_n {H : List (Set ℤ)} (hA : (start H).Infinite) (R : ℕ) :
    Monotone fun n => cnSeq H n R := by
  intro m n hmn
  have : Nonempty (farIntervals H n R) := (farIntervals_nonempty hA n R).to_subtype
  refine le_ciInf fun J => ?_
  exact ciInf_le (cnSeq_bddBelow _ m R) ⟨J.1, J.2.1, hmn.trans J.2.2.1, J.2.2.2⟩

/-- The inner infimum is at most `1/2` (nonempty strictly descending list, infinite start). -/
theorem cnSeq_le_half {H : List (Set ℤ)} (hne : H ≠ []) (h : H.IsChain (fun L M => M ⊂ L))
    (hA : (start H).Infinite) (n R : ℕ) : cnSeq H n R ≤ 1 / 2 := by
  obtain ⟨J⟩ := (farIntervals_nonempty hA n R).to_subtype
  exact (ciInf_le (cnSeq_bddBelow _ n R) J).trans (raw_score_le_half hne h J)

/-- The inner infimum is nonnegative. -/
theorem cnSeq_nonneg (H : List (Set ℤ)) (n R : ℕ) : 0 ≤ cnSeq H n R := by
  unfold cnSeq
  rcases isEmpty_or_nonempty (farIntervals H n R) with h | h
  · simp
  · exact le_ciInf fun J => raw_score_nonneg H J

/-- For a nonempty strictly descending list with infinite start, the inner infimum of (8) tends
(in `R`) to `cn H n`, its supremum, and `0 ≤ cn H n ≤ 1/2`. 
-/
theorem cn_tendsto {H : List (Set ℤ)} (hne : H ≠ []) (h : H.IsChain (fun L M => M ⊂ L))
    (hA : (start H).Infinite) (n : ℕ) :
    Tendsto (cnSeq H n) atTop (𝓝 (cn H n)) ∧ cn H n = ⨆ R, cnSeq H n R ∧
      0 ≤ cn H n ∧ cn H n ≤ 1 / 2 := by
  have hb : BddAbove (range (cnSeq H n)) :=
    ⟨1 / 2, by rintro _ ⟨R, rfl⟩; exact cnSeq_le_half hne h hA n R⟩
  have hT := tendsto_atTop_ciSup (cnSeq_mono hA n) hb
  have heq : cn H n = ⨆ R, cnSeq H n R := hT.limUnder_eq
  refine ⟨heq ▸ hT, heq, ?_, ?_⟩
  · rw [heq]; exact (cnSeq_nonneg _ n 0).trans (le_ciSup hb 0)
  · rw [heq]; exact ciSup_le fun R => cnSeq_le_half hne h hA n R

/-- `cn H n` is nondecreasing in `n` for such lists. -/
theorem cn_mono_n {H : List (Set ℤ)} (hne : H ≠ []) (h : H.IsChain (fun L M => M ⊂ L))
    (hA : (start H).Infinite) : Monotone fun n => cn H n := by
  intro m n hmn
  exact le_of_tendsto_of_tendsto' (cn_tendsto hne h hA m).1 (cn_tendsto hne h hA n).1
    fun R => cnSeq_mono_n hA R hmn

/-- A chain of a language class has an infinite starting language. -/
theorem start_infinite {X : Set (Set ℤ)} (hX : LangClass X) {H : List (Set ℤ)}
    (hH : IsChain X H) : (start H).Infinite := by
  obtain ⟨L, t, rfl⟩ := List.exists_cons_of_ne_nil hH.1
  exact hX.infinite L (hH.2.1 L (by simp))

end ChainsAux

/-- **Claim 3.2** (`claim:cn-eventual-interval-bound`). For a chain `H` starting from `A`, if
`c_n(H) > q`, there is a bounded region `[-R, R]` outside which every relative interval of `A`
with at least `n` points has pairing score greater than `q`. -/
theorem claim_cn_eventual_interval_bound {X : Set (Set ℤ)} (hX : LangClass X)
    {H : List (Set ℤ)} (hH : IsChain X H) {n : ℕ} {q : ℝ} (hq : q < cn H n) :
    ∃ R : ℕ, ∀ J, IsRelInterval (start H) J → n ≤ J.ncard → Disjoint J (Icc (-(R : ℤ)) R) →
      q < def_raw_pairing_score H J := by
  have hA := ChainsAux.start_infinite hX hH
  obtain ⟨hT, -⟩ := ChainsAux.cn_tendsto hH.1 hH.2.2 hA n
  obtain ⟨R, hR⟩ := (hT.eventually (lt_mem_nhds hq)).exists
  refine ⟨R, fun J hJ hn hd => hR.trans_le ?_⟩
  exact ciInf_le (ChainsAux.cnSeq_bddBelow H n R) ⟨J, hJ, hn, hd⟩

/-! ## Admissible obstruction trees -/

/-- A well-founded rooted tree whose vertices are labelled by languages; a vertex is a leaf or
has children indexed by `ℕ`. -/
inductive LTree
  | leaf (L : Set ℤ)
  | node (L : Set ℤ) (child : ℕ → LTree)

namespace LTree

/-- The language label of the root. -/
def label : LTree → Set ℤ
  | leaf L => L
  | node L _ => L

/-- Conditions 2 and 3 of Definition 3.3 at every vertex: each child's label is a language of
`X` properly contained in its parent's label, and if a vertex labelled `L` has children, then for
every finite `F ⊆ L` some child is labelled by `M` with `F ⊆ M ⊊ L`. -/
def Admissible (X : Set (Set ℤ)) : LTree → Prop
  | leaf _ => True
  | node L c =>
      (∀ i, (c i).label ∈ X ∧ (c i).label ⊂ L ∧ Admissible X (c i)) ∧
      ∀ F : Set ℤ, F.Finite → F ⊆ L → ∃ i, F ⊆ (c i).label

/-- The root-to-leaf paths of a tree, as lists of labels `(root label, …, leaf label)`. -/
def paths : LTree → Set (List (Set ℤ))
  | leaf L => {[L]}
  | node L c => {P | ∃ i, ∃ Q ∈ paths (c i), P = L :: Q}

end LTree

/-- **Definition 3.3** (`def:aot`). `T` is an admissible obstruction tree for `K ∈ X`: its root
is labelled `K` (condition 1), conditions 2 and 3 hold at every vertex (`LTree.Admissible`), and
it has no infinite path from the root (condition 4, automatic for a term of the inductive type
`LTree`). The single-vertex tree `LTree.leaf K` is permitted. -/
def def_aot (X : Set (Set ℤ)) (K : Set ℤ) (T : LTree) : Prop :=
  T.label = K ∧ T.Admissible X

/-- Equation (9) (`eq:bn`): `b_n(K) = inf_{T admissible, root label K} sup_{H root-to-leaf} c_n(H)`. -/
noncomputable def bn (X : Set (Set ℤ)) (K : Set ℤ) (n : ℕ) : ℝ :=
  ⨅ T : {T : LTree // def_aot X K T}, ⨆ H : T.1.paths, cn H n

/-- Equation (9) (`eq:bn`): `b(K) = lim_{n → ∞} b_n(K)`. -/
noncomputable def bK (X : Set (Set ℤ)) (K : Set ℤ) : ℝ :=
  limUnder atTop fun n : ℕ => bn X K n

namespace ChainsAux

open Topology

/-- Every root-to-leaf path of an admissible tree starts with the root label and is strictly
descending. -/
theorem paths_spec (X : Set (Set ℤ)) :
    ∀ T : LTree, T.Admissible X → ∀ P ∈ T.paths,
      (∃ t, P = T.label :: t) ∧ P.IsChain (fun L M => M ⊂ L) ∧ ∀ L ∈ P, L = T.label ∨ L ∈ X
  | .leaf L, _, P, hP => by
    have hP : P = [L] := hP
    subst hP
    exact ⟨⟨[], rfl⟩, by simp, by simp [LTree.label]⟩
  | .node L c, hT, P, hP => by
    obtain ⟨i, Q, hQ, rfl⟩ := hP
    obtain ⟨hX, hss, hadm⟩ := hT.1 i
    obtain ⟨⟨t, rfl⟩, hc, hmem⟩ := paths_spec X (c i) hadm _ hQ
    refine ⟨⟨_, rfl⟩, List.IsChain.cons_cons hss hc, ?_⟩
    intro M hM
    rcases List.mem_cons.mp hM with rfl | hM
    · exact Or.inl rfl
    · rcases hmem M hM with rfl | h
      · exact Or.inr hX
      · exact Or.inr h

/-- Every tree has a root-to-leaf path. -/
theorem paths_nonempty : ∀ T : LTree, T.paths.Nonempty
  | .leaf L => ⟨[L], rfl⟩
  | .node L c => by
    obtain ⟨Q, hQ⟩ := paths_nonempty (c 0)
    exact ⟨L :: Q, 0, Q, hQ, rfl⟩

/-- For an admissible tree rooted at `K ∈ X`, every path is a chain of `X` starting at `K`. -/
theorem path_isChain {X : Set (Set ℤ)} {K : Set ℤ} (hK : K ∈ X) {T : LTree}
    (hT : def_aot X K T) {P : List (Set ℤ)} (hP : P ∈ T.paths) :
    IsChain X P ∧ start P = K := by
  obtain ⟨⟨t, rfl⟩, hc, hmem⟩ := paths_spec X T hT.2 P hP
  refine ⟨⟨by simp, fun L hL => ?_, hc⟩, by simp [start, hT.1]⟩
  rcases hmem L hL with rfl | h
  · rw [hT.1]; exact hK
  · exact h

/-- Bounds `0 ≤ c_n(H) ≤ 1/2` along every path of an admissible tree with infinite root. -/
theorem cn_path_bounds {X : Set (Set ℤ)} {T : LTree} (hT : T.Admissible X)
    (hK : T.label.Infinite) (n : ℕ) (H : T.paths) : 0 ≤ cn H.1 n ∧ cn H.1 n ≤ 1 / 2 := by
  obtain ⟨⟨t, ht⟩, hc, -⟩ := paths_spec X T hT H.1 H.2
  have hne : H.1 ≠ [] := by rw [ht]; simp
  have hA : (start H.1).Infinite := by rw [ht]; simpa [start] using hK
  obtain ⟨-, -, h0, h1⟩ := cn_tendsto hne hc hA n
  exact ⟨h0, h1⟩

/-- `c_n` along the paths of such a tree is bounded above. -/
theorem pathSup_bdd {X : Set (Set ℤ)} {T : LTree} (hT : T.Admissible X)
    (hK : T.label.Infinite) (n : ℕ) : BddAbove (range fun H : T.paths => cn H.1 n) :=
  ⟨1 / 2, by rintro _ ⟨H, rfl⟩; exact (cn_path_bounds hT hK n H).2⟩

/-- The supremum over the paths lies in `[0, 1/2]`. -/
theorem pathSup_bounds {X : Set (Set ℤ)} {T : LTree} (hT : T.Admissible X)
    (hK : T.label.Infinite) (n : ℕ) :
    0 ≤ (⨆ H : T.paths, cn H.1 n) ∧ (⨆ H : T.paths, cn H.1 n) ≤ 1 / 2 := by
  have : Nonempty T.paths := (paths_nonempty T).to_subtype
  obtain ⟨H⟩ := (paths_nonempty T).to_subtype
  exact ⟨(cn_path_bounds hT hK n H).1.trans (le_ciSup (pathSup_bdd hT hK n) H),
    ciSup_le fun H => (cn_path_bounds hT hK n H).2⟩

/-- The family in the infimum of (9) is bounded below (witness `0`; nonnegativity of `b_n` is
stated in `bn_bounds`). -/
theorem bn_bddBelow {X : Set (Set ℤ)} {K : Set ℤ} (hK : K.Infinite) (n : ℕ) :
    BddBelow (range fun T : {T : LTree // def_aot X K T} => ⨆ H : T.1.paths, cn H.1 n) :=
  ⟨0, by
    rintro _ ⟨T, rfl⟩
    exact (pathSup_bounds T.2.2 (by rw [T.2.1]; exact hK) n).1⟩

/-- `0 ≤ b_n(K) ≤ 1/2` for infinite `K`. -/
theorem bn_bounds {X : Set (Set ℤ)} {K : Set ℤ} (hK : K.Infinite) (n : ℕ) :
    0 ≤ bn X K n ∧ bn X K n ≤ 1 / 2 := by
  have hT0 : def_aot X K (LTree.leaf K) := ⟨rfl, trivial⟩
  have : Nonempty {T : LTree // def_aot X K T} := ⟨⟨_, hT0⟩⟩
  refine ⟨le_ciInf fun T => (pathSup_bounds T.2.2 (by rw [T.2.1]; exact hK) n).1, ?_⟩
  exact (ciInf_le (bn_bddBelow hK n) ⟨_, hT0⟩).trans (pathSup_bounds (X := X) (T := LTree.leaf K)
    trivial hK n).2

/-- `b_n(K)` is nondecreasing in `n` for infinite `K`. -/
theorem bn_mono {X : Set (Set ℤ)} {K : Set ℤ} (hK : K.Infinite) : Monotone (bn X K) := by
  intro m n hmn
  have hT0 : def_aot X K (LTree.leaf K) := ⟨rfl, trivial⟩
  have : Nonempty {T : LTree // def_aot X K T} := ⟨⟨_, hT0⟩⟩
  refine ciInf_mono (bn_bddBelow hK m) fun T => ?_
  have hT := T.2.2
  have hKT : T.1.label.Infinite := by rw [T.2.1]; exact hK
  have : Nonempty T.1.paths := (paths_nonempty T.1).to_subtype
  refine ciSup_mono (pathSup_bdd hT hKT n) fun H => ?_
  obtain ⟨⟨t, ht⟩, hc, -⟩ := paths_spec X T.1 hT H.1 H.2
  have hne : H.1 ≠ [] := by rw [ht]; simp
  have hA : (start H.1).Infinite := by rw [ht]; simpa [start] using hKT
  exact cn_mono_n hne hc hA hmn

/-- For infinite `K`, `b_n(K)` tends to `bK X K`, and `0 ≤ bK X K ≤ 1/2`. 
-/
theorem bK_tendsto {X : Set (Set ℤ)} {K : Set ℤ} (hK : K.Infinite) :
    Tendsto (bn X K) atTop (𝓝 (bK X K)) ∧ 0 ≤ bK X K ∧ bK X K ≤ 1 / 2 := by
  have hb : BddAbove (range (bn X K)) := ⟨1 / 2, by rintro _ ⟨n, rfl⟩; exact (bn_bounds hK n).2⟩
  have hT := tendsto_atTop_ciSup (bn_mono (X := X) hK) hb
  have heq : bK X K = ⨆ n, bn X K n := hT.limUnder_eq
  refine ⟨heq ▸ hT, ?_, ?_⟩
  · rw [heq]; exact (bn_bounds hK 0).1.trans (le_ciSup hb 0)
  · rw [heq]; exact ciSup_le fun n => (bn_bounds hK n).2

end ChainsAux

/-- **Claim 3.4** (`claim:bn-tree-path-bound`). For any threshold `q < b_n(K)`, every admissible
tree rooted at `K` has a root-to-leaf path with pairing score above `q`. The hypothesis
`hn : 1 ≤ n` mirrors the paper's statement (Claim 3.4 is stated for `b_n` with `n` a positive
integer); the Lean proof does not use it. -/
theorem claim_bn_tree_path_bound {X : Set (Set ℤ)} (hX : LangClass X) {K : Set ℤ} (hK : K ∈ X)
    {n : ℕ} (hn : 1 ≤ n) {q : ℝ} (hq : q < bn X K n) {T : LTree} (hT : def_aot X K T) :
    ∃ H ∈ T.paths, q < cn H n := by
  have hKi : K.Infinite := hX.infinite K hK
  have hKT : T.label.Infinite := by rw [hT.1]; exact hKi
  by_contra hcon
  push Not at hcon
  have : Nonempty T.paths := (ChainsAux.paths_nonempty T).to_subtype
  have hsup : (⨆ H : T.paths, cn H.1 n) ≤ q := ciSup_le fun H => hcon H.1 H.2
  have hle : bn X K n ≤ ⨆ H : T.paths, cn H.1 n :=
    ciInf_le (ChainsAux.bn_bddBelow hKi n) ⟨T, hT⟩
  linarith

end BanachDensity1D
