import BanachDensity1D.Construction

/-!
# The extension lemma for `prot_spec`

`Choices.Valid` asks for a protected set `prot a H` for every index `a` with `s_a > 0` and every
list `H` that is safe for `(N_a, s_a)`. The paper (tex l.3437–3439, l.3796–3799) asks for one only
at the forest's chains `H[a,v]`, `a ⪯ v`, `v` a vertex. `Choices.PaperValid` is that requirement
(with the other fields of `Choices.Valid` unchanged). The lemma `paperValid_extends` shows that,
when the vertices form an initial segment of `ℕ` (as in both vertex systems:
`IsFixedEpsSystem.initial`, `IsCopySystem.all`), the stronger requirement restricts nothing: for
every choice meeting the paper's requirement there is then a choice meeting `Choices.Valid` with
the same forest data at every vertex and the same generator.
(The proof builds that choice by changing the given one only away from the forest's chains; this
agreement is not part of the statement.)
-/

namespace BanachDensity1D

open Set Classical

/-- The paper's requirement on the choices: protected sets only at the forest's chains `H[a,v]`
with `v` a vertex, `a ⪯ v` and `s_a > 0`; the other three fields as in `Choices.Valid`. -/
structure Choices.PaperValid (X : Set (Set ℤ)) (R : Requirements) (C : Choices) : Prop where
  prot_spec : ∀ a v, R.isV v → IsAnc R C a v → 0 < R.s a →
    Safe X (R.N a) (R.s a) (pathChain R C a v) →
    def_history_protected_set X (R.N a) (R.s a) (pathChain R C a v) (C.prot a (pathChain R C a v))
  root_spec : ∀ v, (R.lab v).Infinite → 1 ≤ R.N v →
    ∀ x, (R.lab v ∩ cutBoard (C.rootCuts v) x).ncard = R.N v
  child_spec : ∀ v u Cu Bu, R.lab v ⊆ R.lab u → (R.lab v).Infinite → 1 ≤ R.N v →
    (∀ x, (R.lab u ∩ cutBoard Cu x).Finite ∧ (R.lab u ∩ cutBoard Cu x).ncard ≤ Bu) →
    C.childCuts v u Cu Bu ⊆ Cu ∧
    ∀ x, (R.lab v ∩ cutBoard (C.childCuts v u Cu Bu) x).Finite ∧
      R.N v ≤ (R.lab v ∩ cutBoard (C.childCuts v u Cu Bu) x).ncard ∧
      (R.lab v ∩ cutBoard (C.childCuts v u Cu Bu) x).ncard ≤ R.N v + Bu - 1
  pick_spec : ∀ S used, (S \ used).Nonempty → C.pick S used ∈ S \ used

namespace ExtensionAux

/-- Congruence: two choices with the same board choices that agree on the protected sets the
processing of `v` reads give the same data at `v`. -/
lemma processVertex_congr (R : Requirements) (C₁ C₂ : Choices) (prev : List VData) (v : ℕ)
    (hr : C₁.rootCuts = C₂.rootCuts) (hc : C₁.childCuts = C₂.childCuts)
    (hp : ∀ a ∈ (processVertex R C₁ prev v).anc, 0 < R.s a →
      C₁.prot a (ConstructionAux.readChain R (processVertex R C₁ prev v).anc a) =
        C₂.prot a (ConstructionAux.readChain R (processVertex R C₁ prev v).anc a)) :
    processVertex R C₁ prev v = processVertex R C₂ prev v := by
  obtain ⟨p₁, r₁, c₁, k₁⟩ := C₁
  obtain ⟨p₂, r₂, c₂, k₂⟩ := C₂
  simp only [Choices.rootCuts, Choices.childCuts] at hr hc
  subst hr hc
  simp only [processVertex, Choices.prot, VData.anc, ConstructionAux.readChain] at hp ⊢
  congr 1
  refine iUnion₂_congr fun a ha => ?_
  rw [hp a ha.1 ha.2]
  rfl

/-- The extended choice of protected sets: the given one at every forest chain `H[a,v]` (`v` a
vertex, `a ⪯ v`), and a protected set (if any) elsewhere. -/
noncomputable def extProt (X : Set (Set ℤ)) (R : Requirements) (C : Choices) (a : ℕ)
    (H : List (Set ℤ)) : Set ℤ :=
  if ∃ v, R.isV v ∧ IsAnc R C a v ∧ H = pathChain R C a v then C.prot a H
  else if h : ∃ P, def_history_protected_set X (R.N a) (R.s a) H P then h.choose else ∅

/-- The extended choice: `extProt` for the protected sets, the same board choices and `pick`. -/
noncomputable def extChoices (X : Set (Set ℤ)) (R : Requirements) (C : Choices) : Choices :=
  Choices.mk (extProt X R C) C.rootCuts C.childCuts C.pick

/-- The extended choice's protected sets are `extProt`. -/
lemma extChoices_prot (X : Set (Set ℤ)) (R : Requirements) (C : Choices) :
    (extChoices X R C).prot = extProt X R C := rfl

/-- The forest built with the extended choice agrees with the given one up to `n`, when all of
`0, …, n - 1` are vertices. -/
lemma buildForest_ext (X : Set (Set ℤ)) (R : Requirements) (C : Choices) :
    ∀ n, (∀ v < n, R.isV v) → buildForest R (extChoices X R C) n = buildForest R C n
  | 0, _ => rfl
  | n + 1, h => by
    have ih := buildForest_ext X R C n (fun v hv => h v (Nat.lt_succ_of_lt hv))
    simp only [buildForest]
    rw [ih]
    congr 2
    symm
    refine processVertex_congr R C (extChoices X R C) _ n rfl rfl fun a ha _ => ?_
    have hv : R.isV n := h n (Nat.lt_succ_self n)
    have hanc : IsAnc R C a n := ha
    rw [extChoices_prot, extProt,
      if_pos ⟨n, hv, hanc, (ConstructionAux.pathChain_eq_readChain R C a n).symm⟩]

/-- At every vertex the extended choice gives the same data, when the vertices form an initial
segment. -/
lemma vdata_ext (X : Set (Set ℤ)) (R : Requirements) (C : Choices)
    (hinit : ∀ u v, R.isV v → u ≤ v → R.isV u) (v : ℕ) (hv : R.isV v) :
    vdata R (extChoices X R C) v = vdata R C v := by
  have hb := buildForest_ext X R C v (fun u hu => hinit u v hv hu.le)
  simp only [vdata]
  rw [hb]
  symm
  refine processVertex_congr R C (extChoices X R C) _ v rfl rfl fun a ha _ => ?_
  rw [extChoices_prot, extProt,
    if_pos ⟨v, hv, ha, (ConstructionAux.pathChain_eq_readChain R C a v).symm⟩]

lemma isAnc_ext (X : Set (Set ℤ)) (R : Requirements) (C : Choices)
    (hinit : ∀ u v, R.isV v → u ≤ v → R.isV u) (a y : ℕ) (hy : R.isV y) :
    IsAnc R (extChoices X R C) a y ↔ IsAnc R C a y := by
  simp only [IsAnc, vdata_ext X R C hinit y hy]

section generator

variable (X : Set (Set ℤ)) (R : Requirements) (C : Choices)
  (hinit : ∀ u v, R.isV v → u ≤ v → R.isV u)
include hinit

lemma recordHistory_ext (ws : List ℤ) (v : ℕ) (I : Set ℤ) :
    recordHistory R (extChoices X R C) ws v I = recordHistory R C ws v I := by
  ext y
  simp only [recordHistory, mem_setOf_eq]
  constructor
  · rintro ⟨r, hr, hg, ha, hI⟩
    exact ⟨r, hr, hg, (isAnc_ext X R C hinit v y (ConstructionAux.guess_isV hg)).1 ha, hI⟩
  · rintro ⟨r, hr, hg, ha, hI⟩
    exact ⟨r, hr, hg, (isAnc_ext X R C hinit v y (ConstructionAux.guess_isV hg)).2 ha, hI⟩

lemma lca_ext (S : Set ℕ) (hS : ∀ y ∈ S, R.isV y) :
    lca R (extChoices X R C) S = lca R C S := by
  simp only [lca]
  congr 1
  ext a
  simp only [mem_setOf_eq]
  exact forall₂_congr fun y hy => isAnc_ext X R C hinit a y (hS y hy)

lemma record_ext (ws : List ℤ) (v : ℕ) (I : Set ℤ) :
    record R (extChoices X R C) ws v I = record R C ws v I := by
  simp only [record]
  rw [recordHistory_ext X R C hinit ws v I]
  refine lca_ext X R C hinit _ fun y hy => ?_
  obtain ⟨r, -, hg, -, -⟩ := hy
  exact ConstructionAux.guess_isV hg

/-- The extended choice gives the same boards at every vertex. -/
lemma boardOf_ext (v : ℕ) (hv : R.isV v) (x : ℤ) :
    boardOf R (extChoices X R C) v x = boardOf R C v x := by
  simp only [boardOf, vdata_ext X R C hinit v hv]

lemma pod_ext (ws : List ℤ) (v : ℕ) (hv : R.isV v) :
    pod R (extChoices X R C) ws v = pod R C ws v := by
  simp only [pod, boardOf_ext X R C hinit v hv, record_ext X R C hinit ws v]

/-- The extended choice gives the same output at every round. -/
lemma algStep_ext (ws prevOuts : List ℤ) :
    algStep R (extChoices X R C) ws prevOuts = algStep R C ws prevOuts := by
  unfold algStep
  split
  · rfl
  · rename_i Q hQ
    have hQv := ConstructionAux.guess_isV hQ
    dsimp only
    rw [vdata_ext X R C hinit Q hQv]
    have hfind : (vdata R C Q).anc.find?
          (fun v => decide ((pod R (extChoices X R C) ws v \ {x | x ∈ ws ∨ x ∈ prevOuts}).Nonempty)) =
        (vdata R C Q).anc.find?
          (fun v => decide ((pod R C ws v \ {x | x ∈ ws ∨ x ∈ prevOuts}).Nonempty)) :=
      List.find?_congr fun v hv => by
        rw [pod_ext X R C hinit ws v (ConstructionAux.isV_of_anc R C Q hQv v hv)]
    rw [hfind]
    split
    · rename_i v hv
      have hvm : v ∈ (vdata R C Q).anc := List.mem_of_find?_eq_some hv
      rw [pod_ext X R C hinit ws v (ConstructionAux.isV_of_anc R C Q hQv v hvm)]
      rfl
    · rfl

/-- The extended choice gives the same output list on every input list. -/
lemma algOutputs_ext (ws : List ℤ) :
    algOutputs R (extChoices X R C) ws = algOutputs R C ws := by
  induction h : ws.length generalizing ws with
  | zero =>
    rw [List.length_eq_zero_iff] at h; subst h
    rw [ConstructionAux.algOutputs_nil, ConstructionAux.algOutputs_nil]
  | succ n ih =>
    have hne : ws ≠ [] := by rintro rfl; simp at h
    have hd : ws.dropLast.length = n := by simp [List.length_dropLast, h]
    rw [ConstructionAux.algOutputs_eq R (extChoices X R C) hne, ConstructionAux.algOutputs_eq R C hne,
      ih ws.dropLast hd,
      algStep_ext X R C hinit]

/-- The extended choice gives the same generator. -/
lemma algGen_ext : algGen R (extChoices X R C) = algGen R C := by
  funext ws
  simp only [algGen, algOutputs_ext X R C hinit ws]

end generator

end ExtensionAux

/-- The extension lemma with agreement: for a choice `C` meeting the paper's requirement, when the
vertices form an initial segment, there is a choice `C'` meeting `Choices.Valid` that keeps `C`'s
board choices and `pick`, keeps `C`'s protected set at every chain `H̄[a,v]` of `C`'s forest, and
gives the same data at every vertex and the same generator. -/
theorem paperValid_extends_agree {X : Set (Set ℤ)} {R : Requirements} {C : Choices}
    (hinit : ∀ u v, R.isV v → u ≤ v → R.isV u) (hC : C.PaperValid X R) :
    ∃ C' : Choices, C'.Valid X R ∧
      C'.rootCuts = C.rootCuts ∧ C'.childCuts = C.childCuts ∧ C'.pick = C.pick ∧
      (∀ a v, R.isV v → IsAnc R C a v →
        C'.prot a (pathChain R C a v) = C.prot a (pathChain R C a v)) ∧
      (∀ v, R.isV v → vdata R C' v = vdata R C v) ∧ algGen R C' = algGen R C := by
  refine ⟨ExtensionAux.extChoices X R C, ?_, rfl, rfl, rfl, fun a v hv hav => ?_,
    ExtensionAux.vdata_ext X R C hinit, ExtensionAux.algGen_ext X R C hinit⟩
  · refine ⟨fun a H hs hsafe => ?_, hC.root_spec, hC.child_spec, hC.pick_spec⟩
    rw [ExtensionAux.extChoices_prot, ExtensionAux.extProt]
    split_ifs with h1 h2
    · obtain ⟨v, hv, hav, rfl⟩ := h1
      exact hC.prot_spec a v hv hav hs hsafe
    · exact h2.choose_spec
    · exact absurd (ConstructionAux.prot_exists X _ _ H hsafe) h2
  · rw [ExtensionAux.extChoices_prot, ExtensionAux.extProt, if_pos ⟨v, hv, hav, rfl⟩]

/-- The extension lemma. If the vertices form
an initial segment, then for every choice meeting the paper's requirement on protected sets
(`Choices.PaperValid`) there is a choice meeting `Choices.Valid` with the same data at every
vertex and the same generator. So the stronger `prot_spec` of `Choices.Valid` restricts no
construction the paper allows. (The proof drops conjuncts of `paperValid_extends_agree`, which also states that the extended
choice agrees with the given one on the forest's chains.) -/
theorem paperValid_extends {X : Set (Set ℤ)} {R : Requirements} {C : Choices}
    (hinit : ∀ u v, R.isV v → u ≤ v → R.isV u) (hC : C.PaperValid X R) :
    ∃ C' : Choices, C'.Valid X R ∧ (∀ v, R.isV v → vdata R C' v = vdata R C v) ∧
      algGen R C' = algGen R C := by
  obtain ⟨C', hV, -, -, -, -, hvd, hgen⟩ := paperValid_extends_agree hinit hC
  exact ⟨C', hV, hvd, hgen⟩

/-- Conversely, every valid choice meets the paper's requirement. With `paperValid_extends`,
`Choices.Valid` and `Choices.PaperValid` therefore allow the same constructions when the vertices
form an initial segment of `ℕ`. -/
theorem valid_paperValid {X : Set (Set ℤ)} {R : Requirements} {C : Choices} (hC : C.Valid X R) :
    C.PaperValid X R :=
  ⟨fun a v _ _ hs hsafe => hC.prot_spec a _ hs hsafe, hC.root_spec, hC.child_spec, hC.pick_spec⟩

end BanachDensity1D
