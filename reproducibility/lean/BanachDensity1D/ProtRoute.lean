import BanachDensity1D.Extension
import BanachDensity1D.Forest

/-!
# The paper's route to the protected sets

`Choices.Valid.prot_spec` asks for a protected set at every safe list. The paper obtains its
protected sets from Corollary 6.10 (item 3), and only at the chains `H̄[a,v]` its construction
reads (proof of Lemma 6.13, tex l.3477–3482). This file shows that the paper's route suffices:

* `ProtRouteAux.forest_chain_cor_hyps`: at every chain the construction reads, the hypotheses of
  Corollary 6.10 hold with `A = L_a`, `n = N_a`, `q = s_a`;
* `ProtRouteAux.mkChoices_paperValid`: the choices `mkChoices` meet the paper's requirement
  (`Choices.PaperValid`), with the protected sets obtained from `cor_protected_set` (not from
  `prot_exists`);
* `paperValid_extends_agree` (Extension.lean): the extension lemma, stating also that the
  extended choice keeps the given board choices, `pick` and protected sets at every forest chain;
* `exists_valid_of_paper_route`: Corollary 6.10 at the forest's chains, followed by the extension,
  gives a choice meeting `Choices.Valid` with the same forest and generator.

Away from the forest's chains the extension uses `prot_exists`, which proves item 3 of
Corollary 6.10 for every safe list, without the corollary's standing hypotheses.
-/

namespace BanachDensity1D

open Set Classical

namespace ProtRouteAux

/-- Corollary 6.10 item 3 in the form of Definition 6.11: under the corollary's hypotheses
(`A ∈ X`, `n ≥ 1`, `q < b_n(A)`, `H` a history from `A`, safe for `(A,n,q)`), a protected set for
`H` exists. Proved from `cor_protected_set` (the paper's route), not from `prot_exists`. The
conclusion is also an instance of `ConstructionAux.prot_exists`, which needs only that `H` is safe;
the corollary's hypotheses are kept to exhibit the paper's route. -/
theorem prot_of_cor_protected_set {X : Set (Set ℤ)} (hX : LangClass X) {A : Set ℤ} (hA : A ∈ X)
    {n : ℕ} (hn : 1 ≤ n) {q : ℝ} (hq : q < bn X A n) (H : History X)
    (hH : H ∈ historiesFrom X A) (hs : Safe X n q H.1) :
    ∃ P, def_history_protected_set X n q H.1 P := by
  obtain ⟨P, hPf, hPM, hext⟩ := (cor_protected_set hX hA hn hq).2.2 H hH hs
  exact ⟨P, hPf, hPM, hext⟩

/-- The chain part of the forest invariant, for any choice: every `H̄[a,v]` is a chain of `X`
from `L_a` to `L_v`. It needs only that labels lie in `X`. -/
lemma pathChain_chain {X : Set (Set ℤ)} {R : Requirements}
    (hlab : ∀ v, R.isV v → R.lab v ∈ X) (C : Choices) : ∀ v, R.isV v → ∀ a ∈ (vdata R C v).anc,
    IsChain X (pathChain R C a v) ∧ start (pathChain R C a v) = R.lab a ∧
      chainEnd (pathChain R C a v) = R.lab v := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hv a ha
    have hvX := hlab v hv
    by_cases hav : a = v
    · subst hav
      rw [ForestAux.pathChain_self]
      exact ⟨⟨by simp, by simpa using hvX, by simp⟩, rfl, rfl⟩
    rcases ConstructionAux.vdata_cases R C v with ⟨-, h, -⟩ | ⟨p, -, hpv, hpV, hsub, -, h, -⟩
    · rw [h] at ha; simp at ha; exact absurd ha hav
    have hap : a ∈ (vdata R C p).anc := by
      rw [h] at ha
      rcases List.mem_append.1 ha with ha | ha
      · exact ha
      · simp at ha; exact absurd ha hav
    obtain ⟨hch, hst, hend⟩ := ih p hpv hpV a hap
    rw [ForestAux.pathChain_child R C h hap]
    split_ifs with hpl
    · exact ⟨hch, hst, hend.trans hpl⟩
    · have hss : R.lab v ⊂ chainEnd (pathChain R C a p) := by
        rw [hend]; exact ssubset_iff_subset_ne.2 ⟨hsub, fun h' => hpl h'.symm⟩
      refine ⟨⟨by simp, ?_, ?_⟩, by rw [ForestAux.start_snoc hch.1, hst],
        ConstructionAux.chainEnd_snoc _ _⟩
      · intro L hL
        rcases List.mem_append.1 hL with hL | hL
        · exact hch.2.1 L hL
        · simp at hL; subst hL; exact hvX
      · refine hch.2.2.append (by simp) ?_
        intro x hx y hy
        rw [ForestAux.getLast?_eq_chainEnd hch.1] at hx
        simp at hx hy
        subst hx hy
        exact hss

/-- Where the construction reads a protected set — at `H̄[a,v]` with `v` a vertex, `a ⪯ v`,
`s_a > 0` and `H̄[a,v]` safe for `(L_a, N_a, s_a)` — the hypotheses of Corollary 6.10 hold, with
`A = L_a`, `n = N_a`, `q = s_a`: `L_a ∈ X`, `N_a ≥ 1`, `s_a < b_{N_a}(L_a)`, and `H̄[a,v]` is a
history from `L_a`. For any choice. -/
theorem forest_chain_cor_hyps {X : Set (Set ℤ)} {R : Requirements} (hR : ForestAux.Good X R)
    (C : Choices) {a v : ℕ} (hv : R.isV v) (hav : IsAnc R C a v) (hs : 0 < R.s a) :
    ∃ H : History X, H.1 = pathChain R C a v ∧ H ∈ historiesFrom X (R.lab a) ∧
      R.lab a ∈ X ∧ 1 ≤ R.N a ∧ R.s a < bn X (R.lab a) (R.N a) := by
  have haV := ConstructionAux.isV_of_anc R C v hv a hav
  obtain ⟨hch, hst, -⟩ := pathChain_chain hR.lab_mem C v hv a hav
  exact ⟨⟨_, hch⟩, rfl, hst, hR.lab_mem a haV, hR.N_pos a haV, hR.N_safe a haV hs⟩

/-- The paper's route: the choices `mkChoices` meet the paper's requirement
(`Choices.PaperValid`), with every protected set obtained from Corollary 6.10 at the chains the
construction uses (`prot_exists` is not used). The type also follows from
`ConstructionAux.mkChoices_valid` and `valid_paperValid`; what this declaration certifies is its
proof route, which depends on `cor_protected_set` and not on `prot_exists`, a fact checked by
inspecting its dependencies, not stated by its type. -/
theorem mkChoices_paperValid {X : Set (Set ℤ)} (hX : LangClass X) {R : Requirements}
    (hR : ForestAux.Good X R) : (ConstructionAux.mkChoices X R).PaperValid X R := by
  refine ⟨fun a v hv hav hs hsafe => ?_, ConstructionAux.mkChoices_root_spec X R,
    ConstructionAux.mkChoices_child_spec X R, ConstructionAux.mkChoices_pick_spec X R⟩
  obtain ⟨H, hH1, hHA, hA, hn, hq⟩ := forest_chain_cor_hyps hR (ConstructionAux.mkChoices X R) hv hav hs
  have hex := prot_of_cor_protected_set hX hA hn hq H hHA (hH1 ▸ hsafe)
  rw [hH1] at hex
  show def_history_protected_set X (R.N a) (R.s a) (pathChain R _ a v)
    (if h : ∃ P, def_history_protected_set X (R.N a) (R.s a) (pathChain R _ a v) P
      then h.choose else ∅)
  rw [dif_pos hex]; exact hex.choose_spec

end ProtRouteAux

/-- The paper's route end to end: Corollary 6.10 supplies the protected sets at the forest's
chains (`ProtRouteAux.mkChoices_paperValid`), and the extension (`paperValid_extends`) supplies them
elsewhere through `prot_exists`; the result is a choice meeting `Choices.Valid` with the same forest
and generator as the paper-route choice. The type is also met by `mkChoices` itself
(`ConstructionAux.mkChoices_valid`), so the declaration records a proof route, not a stronger
fact. -/
theorem exists_valid_of_paper_route {X : Set (Set ℤ)} (hX : LangClass X) {R : Requirements}
    (hR : ForestAux.Good X R) (hinit : ∀ u v, R.isV v → u ≤ v → R.isV u) :
    ∃ C' : Choices, C'.Valid X R ∧
      (∀ v, R.isV v → vdata R C' v = vdata R (ConstructionAux.mkChoices X R) v) ∧
      algGen R C' = algGen R (ConstructionAux.mkChoices X R) :=
  paperValid_extends hinit (ProtRouteAux.mkChoices_paperValid hX hR)

end BanachDensity1D
