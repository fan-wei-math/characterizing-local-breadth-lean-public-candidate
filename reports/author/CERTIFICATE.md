> **Privacy-sanitized historical copy.** Historical private-repository links have been replaced with references to the nearest current self-contained reproduction materials. These are navigation aids, not links to the original immutable historical artifacts. Original source commit identities, mathematical statements, results and qualifications are retained; those identities do not identify the comment-sanitized public files. The unchanged historical originals remain private.

# Certificate of Lean verification — *Characterizing Local Breadth in Language Generation*

**Editor- and mathematician-facing reading certificate — November 2, 2026**  
**Manuscript:** Jon Kleinberg and Fan Wei, `Nov 1.tex`, SHA-256 `eee1524496f215c15f2278bd39c6f7b24214d0e1e1dd783a552cca3233977249`  
**Source revision:** `dff2c2b99dc5c685164e37dc70b0818336096fe7` (HD), with pinned 1D dependency `efe7a25711657a5cfd0dad8d902392ce4d711e92`  
**Relationship:** Companion to [the consolidated report](Verification-Report.md).

> **Certification status.** The November 2 correspondence audit reports **65/65 numbered assertions at Level K** under the documented model. The pinned one-dimensional library explicitly handles the empty-family case of Corollary 1.6 through `BanachDensity1D.Oct31.finite_point_rank_all`, so the certificate now lists **all 65 as K without a dagger**. This is independent AI correspondence review rather than human mathematical sign-off; remarks remain excluded.

## Executive summary — Level K verification

**Overall verification status (November 2, 2026).** The formalization and its independent AI-based correspondence review report **Level K for all 65 numbered mathematical assertions** in the exact November 1 manuscript: 18 theorems, 30 lemmas, 8 claims, 7 corollaries, and 2 propositions. No Q, P, or K* obligation remains among these 65 under the recorded manuscript model. **All 65 entries are K**, including Corollary 1.6's explicitly checked empty-family case. The five remarks are excluded; the 14 numbered definitions are represented as definitions, not as proof-bearing theorem statements.

**Definition of Level K.** K is a project-specific exact-statement verification standard, not an official Lean designation. A paper result qualifies only when:

- **K1 — Statement fidelity.** The paper's hypotheses, quantifiers and their order, dimensions, definitions, and conclusion have been compared with the elaborated Lean theorem by a separate AI correspondence reader.
- **K2 — Kernel and axiom verification.** The proof is accepted by Lean's kernel, contains no `sorry` or `admit`, and uses no additional nonstandard axioms. The allowed transitive axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- **K3 — Formal representation bridges.** Required transitions between manuscript mathematical objects and their Lean encodings—such as tree occurrences, density limits, earlier family constructions, or the strategy-state domain—are proved in Lean, not merely claimed verbally.
- **K4 — Full statement strength.** No weaker conclusion or extra unproved premise replaces the printed result. Interpretive choices in the paper's standing model are recorded rather than silently changed.

**Prior published work.** No item in the 65-result verification index depends on an *unformalized prior-paper theorem* as an additional Lean axiom or unproved premise. Proposition B.1 explicitly represents and proves the required facts about the previously constructed language family. The remaining earlier mathematical results needed by these proofs are incorporated in the pinned Lean libraries; Mathlib is a formalized dependency, not a citation used as an unchecked axiom.

**Validation.** Recorded checks include all 62 one-dimensional and 55 higher-dimensional proof-bearing modules, a transitive axiom sweep of 5,271 project declarations, and successful replay of 3,874 project theorems. The fresh project build uses cached pinned dependencies. Optional replay of all imported Mathlib theorems from empty timed out and is not claimed complete. Statement correspondence was AI-reviewed, **not signed off by a human mathematician**; line-by-line validation of the manuscript's prose proofs is not claimed.

**Reproducibility:** Follow the [immutable reproduction guide](../../reproducibility/README.md) and the [versioned source/checksum audit package](../../reproducibility/evidence/VERIFICATION-RESULTS.md). The repositories are private and require reviewer access.

---

## 1. What certifies the mathematical statements

For the result of a Lean formalization to count as a theorem of the paper, **three checks are necessary**:

1. **Statement correspondence.** A mathematician must determine that the definitions, quantifiers, hypotheses and conclusion of the elaborated Lean theorem mean what the manuscript says. This project used a separate AI reader to audit each of the 65 numbered assertions, with important representation bridges proved in Lean. It has not been independently signed off by a human.
2. **Kernel acceptance.** The Lean 4 kernel checks every formal proof. The programmatic replay also checked the project's logical declarations against a Mathlib-only base with no project declarations loaded.
3. **Axiom discipline.** The complete transitive axiom sweep reported no assumptions beyond `propext`, `Classical.choice`, and `Quot.sound`; the source-token scan found no `sorry`, `admit`, `sorryAx` or new axiom declarations in the mathematical source.

A different proof from the manuscript may still certify the **same statement**. Conversely, a valid Lean proof of a strictly stronger-premise theorem does not by itself certify the weaker-premise paper statement. The exact-statement additions were made to address this distinction in the previously qualified Section 7 and Appendix A results.

## 1a. How to read Lean without knowing Lean

| Lean syntax | Mathematical reading |
|:--|:--|
| `theorem t (h : P) : Q` | A theorem proving `Q` from hypothesis `P`. |
| `{x : T}` | Universal parameter inferred implicitly by Lean. |
| `∀ K ∈ X, ...` | For every member `K` of `X`. |
| `∃ G, ...` | There is one `G` satisfying the following conditions. Quantifier order matters. |
| `P ∧ Q`, `P ↔ Q`, `P → Q` | Conjunction, equivalence, implication. |
| `ℕ`, `ℤ`, `ℝ` | Naturals (including zero), integers, reals. |
| `Pt d`, `Fin d → ℤ` | Integer lattice `ℤ^d`, indexed by `0,...,d-1`. |
| `Set α`, `Set (Set α)` | A subset; a family of subsets. |
| `Set.Icc a b` | Inclusive interval/box. |
| `Finset α`, `S.ncard` | A finite set; cardinality of a (finite) set. |
| `↑x` | Coercion of `x` to another appropriate type. |
| `∀ n, 1 ≤ n → ...` | A statement for every positive integer n. |
| `Nonempty T` | The type `T` has an inhabitant, i.e. the structured object exists. |
| `MonotoneOn u (Ici 1)` | `u` is nondecreasing on arguments at least 1. |
| `Icc (0 : ℝ) 1` | The closed interval `[0,1]`. |
| `fun L => max (α L - ε) 0` | Positive-part quota `(α(L)-ε)_+`. |
| `⨆ n, f n` / `⨅ R, g R` | Supremum / infimum, with the indicated index. |
| `LangClass X` | Nonempty, countable family of infinite languages. |
| `IsFullEnumeration w K` | The sequence w has range exactly K; repetition allowed. |
| `G.Admissible` / `Fresh` | Global availability/freshness requirement. |
| `EventuallyValidOn X` | All but finitely many outputs are in each target on every full text. |
| `:= by` | The proof follows; the examples below omit proof bodies but link to source. |
| `noncomputable` | The definition may invoke classical choice; not a new theorem axiom. |

## 2. Where to find and reproduce the verification

**Start with the pinned [reproduction guide](../../reproducibility/README.md)**. The source and evidence are privately published here:

- **Actual HD source and proof modules:** [Open verified resource](../../reproducibility/lean/)
- **Imported 1D source at the pin:** [Open verified resource](../../reproducibility/lean/)
- **Versioned audit/evidence package with checksums:** [Open verified resource](../../reproducibility/evidence/VERIFICATION-RESULTS.md)
- **Full elaborated type/dependency register:** [Open verified resource](../../reproducibility/evidence/ELABORATED-REGISTRY.json)
- **All 65 full theorem correspondences:** [Open verified resource](../../reproducibility/evidence/ASSERTION-CERTIFICATION.md)
- **Independent review and corrections:** [Open verified resource](../../reproducibility/evidence/ASSERTION-CERTIFICATION.md)

Once the repositories and the pinned 1D local-path dependency have been configured exactly as in the guide, run in the HD checkout:

```sh
lake build BanachDensityHD
lake build BanachDensityHD.ExactStatements
lake env lean exact-statement-verification/CompleteRegistry.lean
lake env lean exact-statement-verification/AllModuleAxioms.lean
lake env lean exact-statement-verification/ReplayOwnLibraries.lean
```

In the 1D checkout, the recorded command is `lake build MyFormalization BanachDensity1D BanachDensity1D.Nov1`. Run the two `shasum -a256 -c` manifest commands from the versioned audit directory. The complete instructions include the HD Lake package's absolute 1D local-path dependency and the requirement to use its exact Git pin; merely cloning the HD source is not sufficient. The repos are **private**, so GitHub access is required.

**Recorded results:** 62 proof-bearing 1D modules; 55 HD modules; 5,271 project-origin declarations across the complete 126-module closure (standard axioms only); complete project replay of 5,248 logical constants including 3,874 theorems; 54 previously approved 1D and 97 HD declarations unchanged. One optional entire-Mathlib-from-empty replay timed out and is **not** counted as passed. The fresh project build used cached pinned external dependencies.

## 3. Principal paper statements next to their actual Lean counterparts

The mathematical summaries are **expository**; the code blocks reproduce the source theorem *signatures* (without proof bodies). Namespace openings, typeclass parameters and implicit source-level variables should be interpreted via the linked `.lean` files and the [elaborated-type register](../../reproducibility/evidence/ELABORATED-REGISTRY.json). For a complete exact verification of binder order and definitions, consult that register, not just these excerpts.
### Theorem 1.5

**Paper meaning.** Exact 1D value, topological/combinatorial agreement, universal lower generator and universal-generator upper bound.

**Source:** [BanachDensity1D/Theorems.lean](../../reproducibility/lean/BanachDensity1D/Theorems.lean)

```lean
theorem thm_intro_one_dimensional {X : Set (Set ℤ)} (hX : LangClass X) :
    (∀ K ∈ X, ∀ n : ℕ, 1 ≤ n → bn X K n = bnTop X K n) ∧
    (∀ G : Generator, G.Admissible → G.EventuallyValidOn X →
      ∀ K ∈ X, ∃ w, IsFullEnumeration w K ∧ outputDensity (G.outputSet w) K ≤ bK X K) ∧
    (∃ G : Generator, G.Admissible ∧ G.EventuallyValidOn X ∧
      ∀ K ∈ X, ∀ w, IsFullEnumeration w K → bK X K ≤ outputDensity (G.outputSet w) K) :=
```

**Correspondence reading.** Nonemptiness belongs to the `LangClass` standing hypothesis. The existential lower generator is placed before every target and enumeration; the competing upper generator is universal.

### Corollary 1.6

**Paper meaning.** A countable family of infinite languages whose targets all have finite point rank admits one globally fresh, eventually valid generator achieving the optimal one-half lower Banach density for every target. No uniform rank bound and no nonemptiness assumption are required.

**Source:** [BanachDensity1D/Oct31Bridges.lean](../../reproducibility/lean/BanachDensity1D/Oct31Bridges.lean)

```lean
theorem finite_point_rank_all {X : Set (Set ℤ)} (hcount : X.Countable)
    (hinf : ∀ L ∈ X, L.Infinite) (hrank : ∀ L ∈ X, ∃ r, CBrank X L r) :
    (∃ G : Generator, G.Admissible ∧ G.EventuallyValidOn X ∧
      ∀ K ∈ X, ∀ w, IsFullEnumeration w K →
        1 / 2 ≤ outputDensity (G.outputSet w) K) ∧
    (∀ G : Generator, G.Admissible → G.EventuallyValidOn X →
      ∀ K ∈ X, ∃ w, IsFullEnumeration w K ∧
        outputDensity (G.outputSet w) K ≤ 1 / 2) := by
```

**Correspondence reading.** This exact wrapper is present in the pinned 1D library at commit `efe7a25711657a5cfd0dad8d902392ce4d711e92`. It applies the original `cor_intro_one_dimensional_rank` theorem to a nonempty family and explicitly uses the existing globally admissible `fresh` generator for an empty family. The [follow-up's theorem type and axiom record](../../reproducibility/evidence/VERIFICATION-RESULTS.md) confirms its standard-only dependencies and successful build. The formal conclusion therefore covers the printed corollary without an extra nonempty-family hypothesis.

### Theorem 1.8

**Paper meaning.** The one-dimensional exact structural guarantee: one generator attains b(K) for every target; every competitor can be forced down to b(K) at each chosen target.

**Source:** [BanachDensity1D/Theorems.lean](../../reproducibility/lean/BanachDensity1D/Theorems.lean)

```lean
theorem thm_main_oneD {X : Set (Set ℤ)} (hX : LangClass X) :
    (∃ G : Generator, G.Admissible ∧ ∀ K ∈ X, ∀ w, IsFullEnumeration w K →
      G.AllAvailable w ∧ G.AlmostAllIn w K ∧ bK X K ≤ outputDensity (G.outputSet w) K) ∧
    (∀ G : Generator, G.Admissible → G.EventuallyValidOn X →
      ∀ K ∈ X, ∃ w, IsFullEnumeration w K ∧ outputDensity (G.outputSet w) K ≤ bK X K) :=
```

**Correspondence reading.** Both parts are included. `AllAvailable` reflects the paper’s global freshness requirement; `AlmostAllIn` is equivalent to eventual validity for admissible generators.

### Theorem 6.2

**Paper meaning.** A single family has optimum 1/4 at one distinguished language and 1/2 at the others, while any common generator faces x+y≤1/2.

**Source:** [BanachDensityHD/Separation.lean](../../reproducibility/lean/BanachDensityHD/Separation.lean)

```lean
theorem thm_main_not_simul (d : ℕ) (hd : 2 ≤ d) :
    ∃ (X : Set (Set (Pt d))) (L₀ : Set (Pt d)) (G₀ G₁ : Generator (Pt d)),
      LangClass X ∧ (∀ L ∈ X, ∀ x ∈ L, ∀ i, 0 ≤ x i) ∧ L₀ ∈ X ∧
      G₀ ∈ ValidGen X ∧ G₁ ∈ ValidGen X ∧
      ∀ h : ℕ → ℝ, IsThreshold h → SeparatesWith (dH h) X L₀ G₀ G₁ :=
```

**Correspondence reading.** `SeparatesWith` is a nontrivial conjunction, not an uninterpreted assumption: its fields encode the exact individual optima, the simultaneous other-target witness and the trade-off. This theorem chooses X, L0, G0, G1 before h.

### Theorem 7.1 (sufficiency)

**Paper meaning.** Protected trees at the prescribed quota for each target imply that one admissible universally valid generator simultaneously guarantees the quota.

**Source:** [BanachDensityHD/ExactStatements/PositiveThreshold.lean](../../reproducibility/lean/BanachDensityHD/ExactStatements/PositiveThreshold.lean)

```lean
theorem fixed_quota_suff_positive {d : ℕ} (hd : 2 ≤ d)
    {X : Set (Set (Pt d))} (hX : LangClass X) {u : ℝ → ℝ}
    (hu : ∀ x, 1 ≤ x → 0 < u x) (hum : MonotoneOn u (Ici 1))
    (q : Set (Pt d) → ℝ) (hq : ∀ K ∈ X, q K ∈ Icc (0 : ℝ) 1)
    (ht : ∀ K ∈ X, ∃ T, IsProtectedTree X (hLog u) q K T) :
    Achievable (hLog u) X q :=
```

**Correspondence reading.** This is for `u>0`, not merely `u≥1`. The complete tree cutoff transport is the separate `protected_normalization` theorem.

### Theorem 7.1 (necessity)

**Paper meaning.** If a common profile is achieved, every target admits a protected tree for all positive additive slacks.

**Source:** [BanachDensityHD/ExactStatements/PositiveThreshold.lean](../../reproducibility/lean/BanachDensityHD/ExactStatements/PositiveThreshold.lean)

```lean
theorem fixed_quota_nec_positive {d : ℕ} (hd : 2 ≤ d)
    {X : Set (Set (Pt d))} (hX : LangClass X) {u : ℝ → ℝ}
    (hu : ∀ x, 1 ≤ x → 0 < u x) (hum : MonotoneOn u (Ici 1))
    (α : Set (Pt d) → ℝ) (hα : ∀ K ∈ X, α K ∈ Icc (0 : ℝ) 1)
    (hach : Achievable (hLog u) X α) :
    ∀ ε : ℝ, 0 < ε → ∀ K ∈ X, ∃ T,
      IsProtectedTree X (hLog u) (fun L => max (α L - ε) 0) K T :=
```

**Correspondence reading.** The existential tree follows the target and epsilon; the proof does not claim zero slack.

### Theorem 7.2

**Paper meaning.** An achievable profile is exactly characterized by protected trees on all dyadic accuracy copies, with actual repeated occurrence structure.

**Source:** [BanachDensityHD/ExactStatements/PaperExports.lean](../../reproducibility/lean/BanachDensityHD/ExactStatements/PaperExports.lean)

```lean
theorem exact_profile_occurrences_positive {d : ℕ} (hd : 2 ≤ d)
    {X : Set (Set (Pt d))} (hX : LangClass X) {u : ℝ → ℝ}
    (hu : ∀ x, 1 ≤ x → 0 < u x) (hum : MonotoneOn u (Ici 1))
    (α : Set (Pt d) → ℝ) (hα : ∀ K ∈ X, α K ∈ Icc (0 : ℝ) 1) :
    Achievable (hLog u) X α ↔
      ∀ K ∈ X, ∀ k : ℕ, 1 ≤ k →
        ∃ (ι : Type) (T : CopyOccurrenceTree ι d), T.Protected X (hLog u) (dyadicQuota α) K k :=
```

**Correspondence reading.** `dyadicQuota` is `(α(K)-2^(-k))_+`. The bridge `all_dyadic_iff_reciprocal` and occurrence/tree transport are formally proved, not assumed.

### Corollary 7.8

**Paper meaning.** A protected tree exists precisely when a *single global* geometric assignment meets every admissible countable vertex obstruction tree.

**Source:** [BanachDensityHD/ExactStatements/VertexCharacterization.lean](../../reproducibility/lean/BanachDensityHD/ExactStatements/VertexCharacterization.lean)

```lean
theorem exact_vertex_obstruction_characterization {d : ℕ} {X : Set (Set (Pt d))}
    {h : ℕ → ℝ} {q : Set (Pt d) → ℝ} {K : Set (Pt d)}
    (hX : X.Countable) (hK : K ∈ X) :
    (∃ (ι : Type) (T : OccurrenceTree ι d), T.Protected X h q K) ↔
      ∃ s a : List (Set (Pt d)) → ℝ,
        (∀ H, IsChain X H → H.headD ∅ = K → 1 ≤ s H ∧ 0 ≤ a H) ∧
        (∀ H M, IsChain X (H ++ [M]) → H ≠ [] → H.headD ∅ = K → a H < a (H ++ [M])) ∧
        ∀ (V : Type) [Countable V] (T : VertexObstruction V (Pt d)),
          T.label T.root = K → T.Admissible X →
            ∃ P, T.Terminal T.root P ∧ ∃ hP : P ≠ [], DecoratedGood h q s a P hP :=
```

**Correspondence reading.** Ordering matters: `∃ s a` precedes `∀ V T`. No finite-height or finite-branching assumption replaces countable obstruction trees.

### Lemma 7.17

**Paper meaning.** For the generator *actually constructed from the supplied literal dyadic tree family*, each specified copy satisfies its density quota.

**Source:** [BanachDensityHD/ExactStatements/CopyForest.lean](../../reproducibility/lean/BanachDensityHD/ExactStatements/CopyForest.lean)

```lean
theorem dyadic_fixed_copy_density_positive {d : ℕ} (hd : 2 ≤ d)
    {X : Set (Set (Pt d))} (hX : LangClass X) {g : ℝ → ℝ}
    (hg0 : ∀ x, 1 ≤ x → 0 < g x) (hgm : MonotoneOn g (Ici 1)) {α : Set (Pt d) → ℝ}
    (hα : ∀ K ∈ X, α K ∈ Icc (0 : ℝ) 1)
    (Tf : Set (Pt d) → ℕ → DTree d)
    (hTf : ∀ K ∈ X, ∀ k, 1 ≤ k → DyadicCopyProtected X (hLog g) α K k (Tf K k))
    (lab : ℕ → Set (Pt d)) (acc : ℕ → ℕ)
    (hlab : ∀ j, lab j ∈ X) (hacc : ∀ j, 1 ≤ acc j)
    (Pb : Set (Rect d)) (cst : ℝ) (hs : Sew Pb (hLog g) cst) :
    let c := cfgOf false ⊤ lab acc Tf (fun v => dyadicQuota α v.L v.k) (hLog g) Pb
    ∀ z w, IsFullEnumeration w (lab z) → c.gen.EventuallyValid w (lab z) ∧
      dyadicQuota α (lab z) (acc z) ≤ deltaH (hLog g) (c.gen.outputSet w) (lab z) :=
```

**Correspondence reading.** This is about the concrete `cfgOf` generator and literal dyadic copies, not merely an unrelated existence theorem.

### Lemma 8.1

**Paper meaning.** For every eligible finite packet of rectangles there is one successful local response strategy, also in dimension one.

**Source:** [BanachDensityHD/Nov1/LocalRectangle.lean](../../reproducibility/lean/BanachDensityHD/Nov1/LocalRectangle.lean)

```lean
theorem local_rectangle_strategy_positive_dimension {d : ℕ} (hd : 1 ≤ d)
    {τ : ℝ} (hτ : 0 < τ) :
    ∀ η : ℝ, 0 < η → η < 1 / 2 →
      ∃ C : ℝ, 0 < C ∧ ∀ (E : Finset (Pt d)) (Rs : Finset (Rect d)),
        (claimGame E (Rs.filter fun R =>
            C * hTau τ R.vol ≤ ((↑E ∩ R.pts : Set (Pt d)).ncard : ℝ)) (1 / 2 - η)).Feasible :=
```

**Correspondence reading.** Packet-feasible means one White policy handles every rectangle in the packet; the threshold C is chosen before E and Rs.

### Theorem 9.1

**Paper meaning.** For d>=2, no globally fresh causal generator can guarantee filtered density at least 1/2 against all full enumerations of the whole lattice.

**Source:** [BanachDensityHD/Endpoint.lean](../../reproducibility/lean/BanachDensityHD/Endpoint.lean)

```lean
theorem end_main {d : ℕ} (hd : 2 ≤ d) (h : ℕ → ℝ) (hpos : ∀ n, 1 ≤ n → 0 < h n)
    (hsup : ¬ BddAbove ((fun n : ℕ => (n : ℝ) / h n) '' Ici 1))
    (G : Generator (Pt d)) (hG : G.Fresh) :
    ∃ w, IsFullEnumeration w (univ : Set (Pt d)) ∧ deltaH h (G.outputSet w) univ < 1 / 2 :=
```

**Correspondence reading.** This is slightly stronger than the printed hypothesis because it does not require h to be monotone; no additional assumption was inserted.

### Lemma A.2

**Paper meaning.** An abstract potential satisfying locality, (P1)--(P4) at the relevant on-play states, and required probes yields a causal local-quota strategy.

**Source:** [BanachDensityHD/ExactStatements/OnPlayPotential.lean](../../reproducibility/lean/BanachDensityHD/ExactStatements/OnPlayPotential.lean)

```lean
theorem quotas_of_properties {d : ℕ} (T : RegionTree d) (hT : T.WellFormed) (Pot : T.V → T.State → ℝ)
    (σ : ℝ) (hP : Properties T Pot σ) (bs : List (Pt d)) (hbs : T.LegalBlack Pot bs)
    (hcomplete : ∀ x ∈ T.E T.root, x ∈ (T.run Pot bs).black ∨ x ∈ (T.run Pot bs).white) :
    ∀ v, ∀ Q ∈ T.reqs v, T.quota v Q ≤ ((T.run Pot bs).white ∩ Q).card :=
```

**Correspondence reading.** `Properties` is the localized on-play predicate of the *new* module, not the stronger arbitrary-bookkeeping-state predicate. The formalized one-way bridge from the broad concrete potential is `of_bookkeeping`.

### Proposition A.5

**Paper meaning.** The conditional (G1)--(G3) scale/potential hypotheses imply the simultaneous finite-rectangle statement; no appeal to unconditional Claim A.6 is substituted.

**Source:** [BanachDensityHD/ExactStatements/OnPlayRectangle.lean](../../reproducibility/lean/BanachDensityHD/ExactStatements/OnPlayRectangle.lean)

```lean
theorem conditional_rectangle_on_play {d : ℕ} (_hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ)
    (hG : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 → ∃ (D : Scales) (c : ℝ), PlayScaleConditions d D ε τ c) :
    ∀ η : ℝ, 0 < η → η < 1 / 2 →
      ∃ C : ℝ, 0 < C ∧ ∀ (E : Finset (Pt d)) (Rs : Finset (Rect d)),
        (claimGame E (Rs.filter fun R =>
            C * hTau τ R.vol ≤ ((↑E ∩ R.pts : Set (Pt d)).ncard : ℝ)) (1 / 2 - η)).Feasible :=
```

**Correspondence reading.** The assumptions are uniform in E and the packet, matching the recorded manuscript reading. In the proof, the dyadic tree is shown WellFormed from its scales; this is not silently added as an assumption.

### Proposition B.1

**Paper meaning.** The exact family printed in the earlier paper gives structural b_n(K_0)=0 for every positive n and b(K_0)=0.

**Source:** [BanachDensity1D/PriorZeroValue.lean](../../reproducibility/lean/BanachDensity1D/PriorZeroValue.lean)

```lean
theorem prop_prior_zero_value (D : PreviousPaperIntervals) :
    LangClass D.toConstruction.printedFamily ∧
    Construction.K0 ∈ D.toConstruction.printedFamily ∧
    (∀ n : ℕ, 1 ≤ n → bn D.toConstruction.printedFamily Construction.K0 n = 0) ∧
    bK D.toConstruction.printedFamily Construction.K0 = 0 :=
```

**Correspondence reading.** `printedLanguage_eq` and `printedFamily_eq` formally identify the family with the earlier printed sumset construction; this is not an unrelated substitute family.

### Lemma B.2

**Paper meaning.** Every α in [0,1/2] occurs as the exact one-dimensional optimum b_X(K).

**Source:** [BanachDensity1D/Nov1/FullRange.lean](../../reproducibility/lean/BanachDensity1D/Nov1/FullRange.lean)

```lean
theorem cor_full_range {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2) :
    ∃ X : Set (Set ℤ), LangClass X ∧ ∃ K ∈ X, bK X K = α :=
```

**Correspondence reading.** The achieved value is exact, including both endpoints. The matching-generation significance follows from Theorem 1.8; that theorem is proved separately.

### Lemma B.3

**Paper meaning.** For every permissible threshold and every sequence α_i in [0,1/2], some family has *exactly* the product region of simultaneously achievable profiles.

**Source:** [BanachDensityHD/Nov1/ProfileRealization.lean](../../reproducibility/lean/BanachDensityHD/Nov1/ProfileRealization.lean)

```lean
theorem prop_profile_realization {d : ℕ} (hd : 2 ≤ d) (h : ℕ → ℝ) (hh : IsThreshold h)
    (α : ℕ → ℝ) (hα : ∀ i, 0 ≤ α i ∧ α i ≤ 1 / 2) :
    ∃ K : ℕ → Set (Pt d), Function.Injective K ∧ LangClass (range K) ∧
      (∃ G ∈ ValidGen (range K), ∀ i, Guarantees (dH h) G (K i) (α i)) ∧
      (∀ β : ℕ → ℝ, ProfileDomain β →
        (IndexedAchievable h K β ↔ ∀ i, β i ∈ Icc (0 : ℝ) (α i))) ∧
      (∀ β : Set (Pt d) → ℝ, (∀ i, β (K i) ∈ Icc (0 : ℝ) 1) →
        (Achievable h (range K) β ↔ ∀ i, β (K i) ∈ Icc (0 : ℝ) (α i))) :=
```

**Correspondence reading.** `IsThreshold` here is read together with the theorem assumptions in the authoritative paper; the family is permitted to depend on h. The conjunction proves both indexed and full-family profile equivalences and one generator meeting the top profile.

### Claim B.5 (intended upper bound)

**Paper meaning.** The constructed staged family satisfies the upper bound b(L_q)≤α_q and hence exact b(L_q)=α_q, in addition to the literal repeated lower heading.

**Source:** [BanachDensityHD/ExactStatements/ProfileInternal.lean](../../reproducibility/lean/BanachDensityHD/ExactStatements/ProfileInternal.lean)

```lean
theorem staged_bK_upper {m : ℕ → ℕ} {hm : ∀ s, 0 < m s}
    (α : Cut → ℝ) (hα : ∀ q, 0 ≤ α q ∧ α q ≤ 1 / 2)
    (f : ℕ → Requirement m hm) (hf : ∀ R, ∀ B : ℕ, ∃ k ≥ B, f k = R)
    (h : ℕ → ℝ) (hh : PositiveThreshold h)
    (hscale : ∀ s : ℕ, (s + 1 : ℝ) ≤ (m s : ℝ) / h ((2 + 2 * (s + 1)) * m s))
    (q : Cut) :
    BanachDensity1D.bK (range (language (Staged.atoms α f)))
      (language (Staged.atoms α f) q) ≤ α q :=
```

**Correspondence reading.** The printed B.5 heading repeats the lower sign; this statement formalizes what its proof argues. `staged_bK_exact` also establishes equality for the same staged language family.

## 4. Definitions and representation conventions used by the theorems

The 14 numbered definitions have mathematical representations in the development. They are **definitions**, not additional proved assertions, so the 65 theorem count does not add them. Some are realized by several equivalent Lean predicates rather than one identical spelling; the important equivalences used by numbered theorems were audited separately.

| Paper definition | Content | Lean definition or representation |
|:--|:--|:--|
| Definition 1.2 | Lower asymptotic density | Background definition; 1D notation and finite prefixes |
| Definition 1.3 | Lower Banach density | `BanachDensityHD.banach`, target-relative bridge to `deltaH` |
| Definition 1.4 | Filtered lower Banach density | `BanachDensityHD.testInf`, `deltaH`, `deltaH_tendsto` |
| Definition 2.1 | Relative intervals, raw pairing score | `BanachDensity1D.def_raw_pairing_score`, layer and interval definitions |
| Definition 2.3 | Admissible obstruction trees | `BanachDensity1D.LTree.Admissible`, `TreeCorrespondence.PaperObstruction` |
| Definition 3.1 | Cantor--Bendixson point rank | `BanachDensity1D.CBrank`, derivative constructions |
| Definition 5.2 | Safe and unsafe histories | `BanachDensity1D.def_safe_unsafe_history` |
| Definition 5.3 | History topology | `BanachDensityHD.historyTopology`; 1D history topology |
| Definition 5.11 | Protected sets | `BanachDensity1D.def_history_protected_set` |
| Definition 7.4 | Geometric feasibility | `BanachDensityHD.GeomFeasible`; finite `StopGame.Feasible` |
| Definition 7.5 | Protected trees | `BanachDensityHD.IsProtectedTree`; occurrence-tree equivalence |
| Definition 7.6 | Geometric decorations | `BanachDensityHD.IsQGoodDecoration`; paper decoration |
| Definition 7.14 | Protected trees on accuracy copies | `BanachDensityHD.ExactStatements.DyadicCopyProtected` |
| Definition A.1 | Activation rule | `BanachDensityHD.RegionTree.activationStep` |

### 4a. Filtered density: infimum over eligible boxes

In the paper, with `m_B(R)=|B∩R|` and `V(R)=|R|`, the quantity `δ_h(A,B)` is the monotone outer limit of the **inner infimum over rectangles** satisfying `m_B(R)≥s h(V(R))`, using 1 for an empty infimum. The Lean implementation takes a supremum over *natural* cutoffs for the outer limit; the inner operation remains an infimum. The monotone outer limit and cofinal natural-cutoff supremum agree. This is not a change to a supremum over boxes.

### 4b. Structural values and occurrence trees

In one dimension, `b_n(K)` is a minimax structural value over admissible well-founded obstruction trees with relative-interval pairing scores; the limiting value is `b(K)`. In higher dimensions, stopping-game feasibility, geometric decorations, and protected accuracy-copy trees encode a compatible family of simultaneous constraints. The exact statement extensions distinguish *occurrences* of repeated labels from the labels themselves; this is necessary for the literal copy construction.

### 4c. The axioms and noncomputability

The permitted axioms are the standard axioms `propext`, `Classical.choice` and `Quot.sound`. The word `noncomputable` on a function only permits a nonalgorithmic definition under the ordinary theory; it does not assert a new external mathematical premise. The project's mechanical scan and transitive axiom sweep should be consulted to confirm the actual trust boundary.

## 5. Full index of all 65 numbered mathematical assertions

The item count is **18 theorems + 30 lemmas + 8 claims + 7 corollaries + 2 propositions = 65**. All 65 assertions are marked **K**. In particular, the Corollary 1.6 row uses the already-pinned Lean wrapper covering both empty and nonempty families, as explained above. No item needs an unformalized result from a prior paper as an extra axiom or unproved premise. The final correspondence classification is independent AI review, not human approval. Full source statements, complete elaborated types and individual checking evidence are available in the [detailed 65-row report](../../reproducibility/evidence/ASSERTION-CERTIFICATION.md); this compact table is a navigation index rather than a second Lean proof.

| Paper result | Level | Lean declaration(s) | Unformalized prior result required? | Certified content / scope |
|:--|:--:|:--|:--|:--|
| **Theorem 1.5** | **K** | `BanachDensity1D.thm_intro_one_dimensional` | **No** — proof in pinned Lean sources | Equality of structural values, adversarial upper bound, and one simultaneous lower generator. |
| **Corollary 1.6** | **K** | `BanachDensity1D.Oct31.finite_point_rank_all` | **No** — proof in pinned Lean sources | Finite point rank; no uniform rank bound and no empty-family exception. |
| **Theorem 1.7** | **K** | `BanachDensityHD.thm_intro_higher_nonsimultaneous` / `BanachDensityHD.thm_main_not_simul` | **No** — proof in pinned Lean sources | Same witness family and generators for the ordinary density separation and trade-off. |
| **Theorem 1.8** | **K** | `BanachDensity1D.thm_main_oneD` | **No** — proof in pinned Lean sources | One exact lower generator and a target-wise adversarial upper enumeration. |
| **Claim 2.2** | **K** | `BanachDensity1D.claim_cn_eventual_interval_bound` | **No** — proof in pinned Lean sources | Eventual relative-interval bound for a fixed refinement chain. |
| **Claim 2.4** | **K** | `BanachDensity1D.claim_bn_tree_path_bound` | **No** — proof in pinned Lean sources | Tree-path witness at a strict threshold below b_n. |
| **Theorem 2.5** | **K** | `BanachDensity1D.thm_lower` | **No** — proof in pinned Lean sources | Exact achievability, eventual validity, and global freshness. |
| **Theorem 2.6** | **K** | `BanachDensity1D.thm_topological_bn` | **No** — proof in pinned Lean sources | Topological-combinatorial equality for b_n. |
| **Lemma 3.2** | **K** | `BanachDensity1D.lem_finite_rank_witness` | **No** — proof in pinned Lean sources | Finite-rank witness with a strict rank decrease. |
| **Corollary 3.3** | **K** | `BanachDensity1D.cor_finite_rank_b` | **No** — proof in pinned Lean sources | Explicit finite-n rank loss and limiting half-density. |
| **Theorem 4.1** | **K** | `BanachDensity1D.thm_upper` | **No** — proof in pinned Lean sources | Upper bound against every admissible eventually valid generator. |
| **Lemma 4.2** | **K** | `BanachDensity1D.lem_upper_race` | **No** — proof in pinned Lean sources | Finite adversarial race on previously unused points. |
| **Theorem 5.1** | **K** | `BanachDensity1D.thm_fixed_epsilon` | **No** — proof in pinned Lean sources | One epsilon-dependent generator works for every target. |
| **Lemma 5.4** | **K** | `BanachDensityHD.HistoriesAux.lem_history_topology_gen` | **No** — proof in pinned Lean sources | Basic-neighborhood/topological construction preserving refinement history. |
| **Lemma 5.5** | **K** | `BanachDensity1D.lem_finest_history_topology` | **No** — proof in pinned Lean sources | Finest compatible topology using countable diagonal arguments. |
| **Lemma 5.6** | **K** | `BanachDensityHD.HistoriesAux.lem_obstruction_closure_gen` | **No** — proof in pinned Lean sources | Closure characterized by arbitrary countable well-founded branching. |
| **Corollary 5.7** | **K** | `BanachDensity1D.cor_safety_interior` | **No** — proof in pinned Lean sources | Safety and unsafety as interior/closure properties. |
| **Theorem 5.8** | **K** | `BanachDensity1D.thm_topological_bn_restated` | **No** — already-proved Theorem 2.6 restated | Topological b_n formula restated in proof context. |
| **Theorem 5.9** | **K** | `BanachDensity1D.thm_topological_main` | **No** — proof in pinned Lean sources | Full generation theorem in terms of topological b. |
| **Corollary 5.10** | **K** | `BanachDensity1D.cor_protected_set` | **No** — proof in pinned Lean sources | Basic finite-protection and safety equivalence. |
| **Lemma 5.12** | **K** | `BanachDensity1D.lem_boards` | **No** — proof in pinned Lean sources | Finite-trace board existence and exact size bounds. |
| **Lemma 5.13** | **K** | `BanachDensity1D.lem_forest_invariant` | **No** — proof in pinned Lean sources | Protected-path and ancestry invariants of the forest. |
| **Lemma 5.14** | **K** | `BanachDensity1D.lem_uniform_board` | **No** — proof in pinned Lean sources | Board quota max(0,s-1/N), including freezing. |
| **Lemma 5.15** | **K** | `BanachDensity1D.lem_memory` | **No** — proof in pinned Lean sources | Conditional memory/record-language inclusion. |
| **Lemma 5.16** | **K** | `BanachDensityHD.ForestAux.capture_gen` | **No** — proof in pinned Lean sources | Finite-evidence eventual capture, without target identification. |
| **Lemma 5.17** | **K** | `BanachDensity1D.lem_validity` | **No** — proof in pinned Lean sources | Only finitely many invalid outputs. |
| **Lemma 5.18** | **K** | `BanachDensityHD.lem_pairing_game` | **No** — proof in pinned Lean sources | Total rounded-half bound for the filtered pairing game. |
| **Corollary 5.19** | **K** | `BanachDensity1D.cor_regular_board_density` | **No** — proof in pinned Lean sources | Regular-board density guarantee. |
| **Lemma 5.20** | **K** | `BanachDensity1D.lem_copies_chain` | **No** — proof in pinned Lean sources | Adjacent accuracy copies of a language form an ancestor chain. |
| **Lemma 5.21** | **K** | `BanachDensity1D.lem_capture_fixed_copy` | **No** — proof in pinned Lean sources | Eventual capture of each specified copy. |
| **Lemma 5.22** | **K** | `BanachDensity1D.lem_fixed_copy_density` | **No** — proof in pinned Lean sources | One fixed-copy quota approaches the optimal value. |
| **Theorem 5.23** | **K** | `BanachDensity1D.thm_oneD_lower_conclusion` | **No** — proof in pinned Lean sources | One generator achieves b(K) on all targets and enumerations. |
| **Theorem 6.1** | **K** | `BanachDensityHD.Oct31.separation_gap_one_sixteenth` | **No** — proof in pinned Lean sources | Explicit universal 1/16 separation, with witnesses before h. |
| **Theorem 6.2** | **K** | `BanachDensityHD.thm_main_not_simul` / `BanachDensityHD.family7_witnesses` | **No** — proof in pinned Lean sources | Exact optima 1/4 and 1/2, simultaneous other-target guarantee, trade-off. |
| **Lemma 6.3** | **K** | `BanachDensityHD.lem_validity_commitment` | **No** — proof in pinned Lean sources | Finite commitment under eventual validity. |
| **Lemma 6.4** | **K** | `BanachDensityHD.ExactStatements.distinct_input_block_forcing` | **No** — proof in pinned Lean sources | Block forcing from a distinct initial input list. |
| **Lemma 6.5** | **K** | `BanachDensityHD.prop_tradeoff` | **No** — proof in pinned Lean sources | Trade-off from horizontal/vertical layer races. |
| **Claim 6.6** | **K** | `BanachDensityHD.claim_horizontal_test` | **No** — proof in pinned Lean sources | Adversarial horizontal test with a complete finite strip prefix. |
| **Theorem 7.1** | **K** | `BanachDensityHD.ExactStatements.fixed_quota_suff_positive` / `BanachDensityHD.ExactStatements.fixed_quota_nec_positive` | **No** — proof in pinned Lean sources | Both protected-tree directions for positive nondecreasing u. |
| **Theorem 7.2** | **K** | `BanachDensityHD.ExactStatements.exact_profile_occurrences_positive` | **No** — proof in pinned Lean sources | Exact achievable profiles using dyadic copy occurrence trees. |
| **Theorem 7.3** | **K** | `BanachDensityHD.Oct31.finite_rank_near_half_all` / `BanachDensityHD.end_main` | **No** — proof in pinned Lean sources | Near-half at every finite point-rank target and strict endpoint obstruction. |
| **Theorem 7.7** | **K** | `BanachDensityHD.TreeCorrespondence.paper_topological_characterization` | **No** — proof in pinned Lean sources | Occurrence-tree/topological neighborhood equivalence. |
| **Corollary 7.8** | **K** | `BanachDensityHD.TreeCorrespondence.exact_vertex_obstruction_characterization` | **No** — proof in pinned Lean sources | Global assignment then arbitrary countable vertex obstructions. |
| **Corollary 7.9** | **K** | `BanachDensityHD.TreeCorrespondence.PaperDecoration.finite_protection` | **No** — proof in pinned Lean sources | Finite protection on good basic neighborhoods. |
| **Lemma 7.10** | **K** | `BanachDensityHD.lem_hd_capture` | **No** — proof in pinned Lean sources | Critical-vertex capture for the actual HD forest. |
| **Lemma 7.11** | **K** | `BanachDensityHD.ExactStatements.sewing_positive` | **No** — proof in pinned Lean sources | Exact weighted sewing bound for positive nondecreasing u. |
| **Lemma 7.12** | **K** | `BanachDensityHD.lem_hd_help` | **No** — proof in pinned Lean sources | Simulation/virtual play preserves real outputs. |
| **Lemma 7.13** | **K** | `BanachDensityHD.ExactStatements.commitments_including_final_reply` | **No** — proof in pinned Lean sources | Commitment includes the reply to the last committing input. |
| **Lemma 7.15** | **K** | `BanachDensityHD.ExactStatements.adjacent_copy_ancestry` | **No** — proof in pinned Lean sources | Nonstrict scan preserves adjacent equal-language accuracy copies. |
| **Lemma 7.16** | **K** | `BanachDensityHD.ExactStatements.capture_specified_copy` | **No** — proof in pinned Lean sources | Literal nonstrict copy-forest capture. |
| **Lemma 7.17** | **K** | `BanachDensityHD.ExactStatements.dyadic_fixed_copy_density_positive` | **No** — proof in pinned Lean sources | Fixed-copy density from the actual dyadic forest and generator. |
| **Lemma 8.1** | **K** | `BanachDensityHD.Nov1.local_rectangle_strategy_positive_dimension` | **No** — proof in pinned Lean sources | One game strategy for every rectangle in a finite packet; d>=1. |
| **Theorem 8.2** | **K** | `BanachDensityHD.Oct31.finite_rank_near_half_all` | **No** — proof in pinned Lean sources | Near-half simultaneously without a uniform bound on finite ranks. |
| **Theorem 9.1** | **K** | `BanachDensityHD.end_main` | **No** — proof in pinned Lean sources | Exact-half endpoint impossibility for d>=2. |
| **Lemma 9.2** | **K** | `BanachDensityHD.end_strip` | **No** — proof in pinned Lean sources | Adversarial strip game including off-strip White responses. |
| **Lemma A.2** | **K** | `BanachDensityHD.ExactStatements.OnPlay.quotas_of_properties` | **No** — proof in pinned Lean sources | Local potential strategy under on-play hypotheses and necessary probes. |
| **Claim A.3** | **K** | `BanachDensityHD.claim_discardsmall` | **No** — proof in pinned Lean sources | Discarded small remainders have a controlled total fraction. |
| **Claim A.4** | **K** | `BanachDensityHD.claim_quotassuffice` | **No** — proof in pinned Lean sources | Quotas on local pieces imply the desired global rectangle guarantee. |
| **Proposition A.5** | **K** | `BanachDensityHD.ExactStatements.conditional_rectangle_on_play` | **No** — proof in pinned Lean sources | True conditional implication under G1-G3, without invoking A.6. |
| **Claim A.6** | **K** | `BanachDensityHD.claim_cf_potential_existence_uniform` | **No** — proof in pinned Lean sources | Uniform concrete scale and potential construction. |
| **Proposition B.1** | **K** | `BanachDensity1D.PriorZero.prop_prior_zero_value` | **No** — printed earlier family formalized | Exact printed earlier sumset family has b_n(K0)=0 for every n. |
| **Lemma B.2** | **K** | `BanachDensity1D.cor_full_range` | **No** — prior zero-family constructed in Lean | Every exact optimum alpha in [0,1/2] occurs. |
| **Lemma B.3** | **K** | `BanachDensityHD.prop_profile_realization` | **No** — proof in pinned Lean sources | Every prescribed product profile region occurs for an appropriate family. |
| **Claim B.4** | **K** | `BanachDensity1D.ProfileAux.Staged.bK_lower` | **No** — proof in pinned Lean sources | Lower structural value at each rational cutoff of staged family. |
| **Claim B.5** | **K** | `BanachDensityHD.ExactStatements.staged_bK_upper` / `BanachDensityHD.ExactStatements.staged_bK_exact` | **No** — proof in pinned Lean sources | Literal repeated heading and intended upper bound; resulting equality. |

## 6. What has and has not been established

**Established by the recorded mechanical checks:** the project builds, its own logical declarations replay through the Lean kernel against pinned Mathlib, and the imported project declarations have standard-only transitive axiom dependencies. The project contains representations of all 65 numbered assertions, with the crucial tree, schedule, game and state-domain bridges separately proved. The independently written AI audit reports 65 Level K entries and no remaining Q/P obligations for this scoped inventory.

**Mathematical correspondence remains an editorial judgment:** although independent AI reviewers compared the Lean theorems to the paper, **no human mathematician has signed off on every elaborated statement**. The report's Level K classification is a project-specific result of that review, not an official Lean designation or third-party certification.

**Corollary 1.6:** the pinned theorem `BanachDensity1D.Oct31.finite_point_rank_all` explicitly covers the empty family, using the existing admissible `fresh` generator. Its underlying nonempty case remains `cor_intro_one_dimensional_rank`. The wrapper has a recorded successful build and standard-only axiom check; no additional proof or manuscript assumption is needed.

**Excluded statements:** five remarks, unnumbered theorem summaries, the guiding question, figures, editorial exposition, and line-by-line equivalence of the authors' written proofs with the Lean proof routes. These are not additional theorem obligations under the declared Level K scope.

**Editorial/prose notes:** the B.5 heading repeats B.4's lower sign although its proof establishes an upper bound; both directions are formally treated for the actual constructed family. Remark 5 begins with one interval and its language layers are disjoint, so an overlapping-test-window counterexample does not disprove its literal single-interval bound; a *stronger* arbitrary-packet interpretation is not verified. A previous-paper theorem number and an absent general-sewing appendix cross-reference are noted. See [Mathematical notices](../../reproducibility/CERTIFICATE.md).

**Reproduction boundary:** the project replay passed, but an optional full *imported Mathlib from empty* replay timed out. The clean build recompiled project sources with cached dependencies. The code and reports are versioned privately and cannot be reproduced by unauthorized readers without repository access.

## 7. How this certificate was compiled

This is a **reader-facing compilation** of the immutable November 2 Codex/Lean source, the independent completeness review and the mechanical evidence. It is not the student's separate Claude formalization and does not incorporate that repository's results or claims as evidence. The student certificate and addendum were used **only as examples of accessible organization**: theorem statements next to Lean signatures, a glossary, reproducibility instructions, and a full item list. The source version, predicate names and audit judgments in this certificate refer exclusively to the Codex development above.

**Suggested accurate claim for the manuscript:** “Using Lean 4 and Mathlib, we formally verified the 65 numbered mathematical assertions of the November 1 manuscript under the declared model conventions, with kernel-checked proofs and an independent AI correspondence audit. The source, exact statement correspondence, validation logs and reproduction instructions are available in the versioned repositories. Remarks and line-by-line certification of written proofs are not included.” For the strongest literal-all-families statement, first add the trivial Corollary 1.6 empty-family wrapper.
