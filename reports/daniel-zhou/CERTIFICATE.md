# Certificate of correctness — Characterizing Local Breadth in Language Generation (Kleinberg, Wei)

This repository is a Lean 4 formalization of J. Kleinberg and F. Wei, "Characterizing Local Breadth
in Language Generation". It follows the statements and the numbering of the paper's numbered
results in its **version of 1 November 2026**. Paper references below are to that numbering
(Theorem 1.5, Definition 1.3, …) and its sections.

## 1. What certifies the proofs

A Lean formalization certifies a theorem through three things together:

1. **The statements.** The Lean statements of the main theorems, and the definitions they use, say
   what the paper says. This is the only part a person has to read. Sections 3 and 4 below put
   each statement and definition next to the paper's wording, and section 1a explains the Lean
   notation they use.
2. **The kernel check.** Lean's kernel accepts every proof in the repository. Nobody needs to read
   the proofs; `lake build` re-checks all of them.
3. **The axiom check.** Nothing is assumed beyond Lean's three standard axioms (`propext`,
   `Classical.choice`, `Quot.sound`): no `sorry`, no extra `axiom`.

The proofs themselves (about 27,500 lines in `LocalBreadth/`) need not be read. Each of the
paper's 79 numbered items has a Lean counterpart there (listed in `LocalBreadth/Main.lean` and in
section 6 below): every theorem, lemma, corollary, proposition and claim is stated and proved, and
every numbered definition is defined. One result, Proposition B.1, is proved under a named
hypothesis describing a family the paper cites but does not define (section 6); a family
satisfying that hypothesis is constructed in Lean, so the hypothesis can be met.

## 1a. Reading the Lean statements (no Lean knowledge assumed)

| Lean | Meaning |
|---|---|
| `theorem name (x : A) (h : P) : Q` | For every `x` of type `A`, if `P` holds then `Q` holds. Each `(h : P)` before the final colon is a hypothesis; the text after the final colon is the conclusion. |
| `{d : ℕ}` | like `(d : ℕ)` ("for every natural number d"); the braces only mean Lean infers `d` itself |
| `def name … : T := body`, `structure name … where` | Defines `name` to be `body`; a `structure` of type `Prop` is the conjunction of its listed fields. `Prop` means "a statement". |
| `∀ x ∈ X, …` / `∃ x ∈ X, …` | for every / there is an `x` in `X` such that … |
| `fun i => e` | the function i ↦ e |
| `A → B` (as a type) | functions from `A` to `B` |
| `ℕ`, `ℤ`, `ℝ`, `ℚ` | natural numbers (including 0), integers, reals, rationals |
| `Fin d → ℤ` | the lattice ℤ^d (points are d-tuples of integers); `Fin d` is {0, …, d−1} |
| `Set α`, `Set (Set α)` | subsets of `α` (a language); families of languages |
| `Set.univ` | the whole space (here ℤ^d) |
| `Set.range f` | the set of values of `f` |
| `Set.Icc a b` | the box {x : a ≤ x ≤ b} (coordinatewise in ℤ^d) |
| `S.ncard` | the number of elements of a finite set `S` |
| `A ∩ B`, `A \ B`, `A ⊆ B`, `A ⊂ B` | intersection, difference, inclusion, proper inclusion |
| `⨆ s : ℕ, f s`, `⨅ R, f R` | supremum over s ∈ ℕ, infimum over R |
| `sSup S` | the supremum of the set `S` of reals |
| `List α` | finite sequences of elements of `α`; `H ++ [M]` appends `M` |
| `P ∧ Q`, `P ∨ Q`, `¬ P`, `P → Q`, `P ↔ Q` | and, or, not, implies, if and only if |
| `(n : ℝ)` | the natural number `n` regarded as a real number |
| `∀ᶠ t in atTop, P t` | `P t` holds for all sufficiently large `t` |
| `Function.Injective K` | `K i ≠ K j` whenever `i ≠ j` |
| `X.Countable`, `L.Infinite`, `X.Nonempty` | `X` is countable, `L` is infinite, `X` is nonempty |
| `⟨K, hK⟩` | `K`, regarded as an element of the family `X` (with the proof `hK` that `K ∈ X`) |
| `noncomputable`, `open … in` | technical markers; they do not affect the meaning |

## 2. How to check it yourself

Requirements: `elan` (the Lean installer; https://github.com/leanprover/elan) and `git`.

```
git clone https://github.com/ZRTMRH/kleinberg-wei-local-breadth-lean.git
cd kleinberg-wei-local-breadth-lean
lake exe cache get        # downloads Mathlib's prebuilt files (a few GB)
lake build                # kernel-checks every proof; must end "Build completed successfully"
lake env lean Certificate.lean
```

The last command restates thirteen main statements in full (each `example` must be accepted) and
prints, for each, the axioms it uses. Expected output, thirteen lines of the form:

```
'LocalBreadth.thm_1_5' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Versions: Lean `v4.35.0` (`lean-toolchain`), Mathlib tag `v4.35.0`, commit
`56a005855ea17e0b0958f73ec801ae140b0a1679` (`lake-manifest.json`).

**Results of these checks (2 November 2026).**
- `lake build` in this repository: `Build completed successfully (9072 jobs)`, with no `sorry`.
- `lake env lean Certificate.lean`: all thirteen `example`s accepted; each of the thirteen
  theorems depends on `[propext, Classical.choice, Quot.sound]` only.
- `#print axioms` on all 71 Lean declarations listed for the numbered theorems, lemmas,
  corollaries, propositions and claims (section 6), and on the retired `lem_C_1`: each depends on
  `[propext, Classical.choice, Quot.sound]` only.
- **Independent kernel replay.** Lean's separate checker `leanchecker` re-checked the compiled
  library, module by module (`lake env leanchecker <module>`), on the same Lean sources
  (commit `d356d16` of the working project). All 24 modules that contain declarations
  (`LocalBreadth.Common`, `Examples`, `Intro`, `OneD`, `Sec5`–`Sec9`, `AppA`, `AppB`, `AppB2`,
  `AppB3` and its five helper modules, `KWZeroFamily`, `Balanced`, `AppC`, `Main`) were accepted
  (exit code 0; at most 6.9 GB of memory per module). The root file `LocalBreadth.lean` contains
  only `import` lines and no declarations; replaying it as one unit re-checks the whole import
  closure at once and was stopped at a 12 GB memory cap, so it is covered by the per-module
  replays.

## 3. The main theorems

Conventions used throughout.
- ℤ^d is `Fin d → ℤ`; in dimension one the lattice is `ℤ` itself. Boxes are order intervals
  `Set.Icc a b` with `a ≤ b`: the finite axis-parallel boxes.
- Times are indexed from 0: the paper's input x_{t+1} is `x t` and its output o_{t+1} is
  `output G x t`.
- A generator `G : Generator α` is a function from the finite list of inputs received so far to its
  next output. The generators of the paper are deterministic, so this loses no generality.
- The paper requires every generator to satisfy the global freshness condition. So "for every
  eventually valid generator" is read as "for every generator that is fresh (`FreshOn`) and
  universally eventually valid (`EventuallyValidOn`)", and existence statements provide a
  generator with both properties.
- "Adversarial enumeration" of the introduction is the "full enumeration" of the model conventions
  (`IsFullEnumeration`).
- Limits of nondecreasing quantities (lim_{s→∞}, lim_{n→∞}, lim_{R→∞}) are written as suprema
  over ℕ; for a nondecreasing sequence the two coincide.

The theorems are in `LocalBreadth/Intro.lean` (1.5–1.8), `Sec6.lean` (6.1, 6.2), `Sec7.lean`
(7.2, 7.7, 7.8), `AppA.lean` (8.2), `Sec9.lean` (9.1), `AppB2.lean` (B.2) and `AppB3.lean` (B.3).

### Theorem 1.5 (exact one-dimensional value and simultaneous optimality)

> Let 𝒳 be a nonempty countable family of infinite subsets of ℤ. Then for every K ∈ 𝒳 and every
> n ≥ 1, b_n^comb(K) = b_n^top(K). Denote their common value by b_n(K), and let
> b(K) = lim_{n→∞} b_n(K). (1) (Upper bound) For every generator that is eventually valid on 𝒳
> and every K ∈ 𝒳, there exists an adversarial enumeration of K for which d_*(O,K) ≤ b(K).
> (2) (Lower bound) There exists a single eventually valid generator such that, for every K ∈ 𝒳
> and every adversarial enumeration of K, its output set O satisfies d_*(O,K) ≥ b(K).

```lean
theorem thm_1_5 (X : Set (Set ℤ)) (hX : IsLanguageFamily X) :
    (∀ K ∈ X, ∀ n : ℕ, 1 ≤ n → bn X K n = bnTop X K n) ∧
    (∀ G : Generator ℤ, FreshOn G X → EventuallyValidOn G X → ∀ K ∈ X,
      ∃ x, IsFullEnumeration K x ∧ lowerBanachDensity (outputSet G x) K ≤ bK X K) ∧
    (∃ G : Generator ℤ, FreshOn G X ∧ EventuallyValidOn G X ∧ ∀ K ∈ X, ∀ x,
      IsFullEnumeration K x → bK X K ≤ lowerBanachDensity (outputSet G x) K)
```

`bn` is b_n^comb (equation (eq:bn)); `bK` is b(K), defined from `bn`.

### Corollary 1.6

> Let 𝒳 be a countable family of infinite subsets of ℤ, and suppose that every language in 𝒳 has
> finite Cantor–Bendixson point rank. Then a single eventually valid generator achieves the
> optimal lower Banach density 1/2 for every target language.

```lean
theorem cor_1_6 (X : Set (Set ℤ)) (hcount : X.Countable) (hinf : ∀ L ∈ X, L.Infinite)
    (hrank : ∀ L : X, HasFinitePointRank X L) :
    (∃ G : Generator ℤ, FreshOn G X ∧ EventuallyValidOn G X ∧ ∀ K ∈ X, ∀ x,
      IsFullEnumeration K x → 1 / 2 ≤ lowerBanachDensity (outputSet G x) K) ∧
    (∀ G : Generator ℤ, FreshOn G X → EventuallyValidOn G X → ∀ K ∈ X,
      ∃ x, IsFullEnumeration K x ∧ lowerBanachDensity (outputSet G x) K ≤ 1 / 2)
```

"Achieves the optimal density 1/2" is spelled out as both halves: 1/2 is achieved, and no
generator does better.

### Theorem 1.7 (failure of simultaneous optimality, informal version of Theorems 6.1 and 6.2)

> For every d ≥ 2, there exists a countable language family 𝒳 with a distinguished language K₀
> such that: some eventually valid generator guarantees d_*(O,K₀) ≥ 1/4; another eventually valid
> generator guarantees d_*(O,K) ≥ 1/2 simultaneously for every K ∈ 𝒳 ∖ {K₀}. Both generators are
> eventually valid on the entire family 𝒳. Nevertheless, any single eventually valid generator
> guaranteeing density x at K₀ and density y at every other language must satisfy x + y ≤ 1/2.

```lean
theorem thm_1_7 (d : ℕ) (hd : 2 ≤ d) :
    ∃ X : Set (Set (Fin d → ℤ)), ∃ K₀ ∈ X, IsLanguageFamily X ∧
      (∃ G : Generator (Fin d → ℤ), FreshOn G X ∧ EventuallyValidOn G X ∧
        ∀ x, IsFullEnumeration K₀ x → 1 / 4 ≤ lowerBanachDensity (outputSet G x) K₀) ∧
      (∃ G : Generator (Fin d → ℤ), FreshOn G X ∧ EventuallyValidOn G X ∧
        ∀ K ∈ X, K ≠ K₀ → ∀ x, IsFullEnumeration K x →
          1 / 2 ≤ lowerBanachDensity (outputSet G x) K) ∧
      (∀ G : Generator (Fin d → ℤ), FreshOn G X → EventuallyValidOn G X → ∀ a b : ℝ,
        (∀ x, IsFullEnumeration K₀ x → a ≤ lowerBanachDensity (outputSet G x) K₀) →
        (∀ K ∈ X, K ≠ K₀ → ∀ x, IsFullEnumeration K x →
          b ≤ lowerBanachDensity (outputSet G x) K) →
        a + b ≤ 1 / 2)
```

The family is also a family of infinite languages (`IsLanguageFamily`), as in Theorems 6.1, 6.2.

### Theorem 1.8 (exact structural characterization)

> Let 𝒳 be a nonempty countable collection of infinite subsets of ℤ. (1) Achievability. There is a
> single generator such that, for every K ∈ 𝒳 and every full enumeration of K, every output is
> available, all but finitely many outputs belong to K, and its output set O satisfies
> d_*(O,K) ≥ b(K). (2) Optimality. Let 𝒜 be any generator that is eventually valid on every full
> enumeration of every language in 𝒳. Then, for every K ∈ 𝒳, there is a full enumeration of K such
> that the output set O produced by 𝒜 satisfies d_*(O,K) ≤ b(K).

```lean
theorem thm_1_8 (X : Set (Set ℤ)) (hX : IsLanguageFamily X) :
    (∃ G : Generator ℤ, ∀ K ∈ X, ∀ x, IsFullEnumeration K x →
      IsAvailable G x ∧ EventuallyIn G x K ∧ bK X K ≤ lowerBanachDensity (outputSet G x) K) ∧
    (∀ G : Generator ℤ, FreshOn G X → EventuallyValidOn G X → ∀ K ∈ X,
      ∃ x, IsFullEnumeration K x ∧ lowerBanachDensity (outputSet G x) K ≤ bK X K)
```

### Theorem 6.1 (failure of simultaneous optimality in dimension d ≥ 2)

> For every d ≥ 2, there exist a countable family 𝒳 of infinite languages in ℕ^d and a constant
> c = 1/16 such that, for every admissible threshold h and every generator G eventually valid on
> 𝒳, there is a language L ∈ 𝒳 satisfying β_{G,h}(L) ≤ β_h(L) − c.

```lean
theorem thm_6_1 (d : ℕ) (hd : 2 ≤ d) :
    ∃ X : Set (Set (Fin d → ℤ)), IsLanguageFamily X ∧ (∀ L ∈ X, ∀ p ∈ L, ∀ i, 0 ≤ p i) ∧
      ∀ h : ℕ → ℝ, IsAdmissibleThreshold h →
        ∀ G : Generator (Fin d → ℤ), FreshOn G X → EventuallyValidOn G X →
          ∃ L ∈ X, betaG h G L ≤ betaOpt X h L - 1 / 16
```

"Languages in ℕ^d" is `∀ L ∈ X, ∀ p ∈ L, ∀ i, 0 ≤ p i` (all coordinates nonnegative).

### Theorem 6.2

> For every d ≥ 2, there exist a single countable family 𝒳 of infinite languages in ℕ^d and a
> distinguished language L₀ ∈ 𝒳 such that the following hold for every threshold function h
> satisfying the conditions above: (1) β_h(L₀) = 1/4 and β_h(L) = 1/2 for every L ≠ L₀. (2) There
> is one generator eventually valid on all of 𝒳 that guarantees δ_h(O,L) ≥ 1/2 simultaneously for
> every L ∈ 𝒳 ∖ {L₀}. (3) If one eventually valid generator guarantees density x at L₀ and density
> y at every other language, then necessarily x + y ≤ 1/2. Consequently, no eventually valid
> generator guarantees δ_h(O,L) ≥ β_h(L) − ε at every L ∈ 𝒳 for any fixed 0 < ε < 1/8.

```lean
theorem thm_6_2 (d : ℕ) (hd : 2 ≤ d) :
    ∃ X : Set (Set (Fin d → ℤ)), ∃ L₀ ∈ X, IsLanguageFamily X ∧ (∀ L ∈ X, ∀ p ∈ L, ∀ i, 0 ≤ p i) ∧
      ∀ h : ℕ → ℝ, IsAdmissibleThreshold h →
        (betaOpt X h L₀ = 1 / 4 ∧ ∀ L ∈ X, L ≠ L₀ → betaOpt X h L = 1 / 2) ∧
        (∃ G : Generator (Fin d → ℤ), FreshOn G X ∧ EventuallyValidOn G X ∧
          ∀ L ∈ X, L ≠ L₀ → ∀ e, IsFullEnumeration L e →
            1 / 2 ≤ filteredBanachDensity h (outputSet G e) L) ∧
        (∀ G : Generator (Fin d → ℤ), FreshOn G X → EventuallyValidOn G X → ∀ x y : ℝ,
          (∀ e, IsFullEnumeration L₀ e → x ≤ filteredBanachDensity h (outputSet G e) L₀) →
          (∀ L ∈ X, L ≠ L₀ → ∀ e, IsFullEnumeration L e →
            y ≤ filteredBanachDensity h (outputSet G e) L) →
          x + y ≤ 1 / 2) ∧
        (∀ ε : ℝ, 0 < ε → ε < 1 / 8 →
          ¬ ∃ G : Generator (Fin d → ℤ), FreshOn G X ∧ EventuallyValidOn G X ∧
            ∀ L ∈ X, ∀ e, IsFullEnumeration L e →
              betaOpt X h L - ε ≤ filteredBanachDensity h (outputSet G e) L)
```

The family and L₀ are chosen before h, as the paper says ("the family 𝒳 and distinguished
language L₀ are independent of h").

### Theorem 7.2 (exact simultaneous profile characterization)

> A profile α is achieved by one globally fresh, universally eventually valid generator if and only
> if every accuracy copy (K,k) has a protected tree on copies in the sense of Definition 7.14.

```lean
theorem thm_7_2 (hS : Sec7Standing d X h) {α : Set (Fin d → ℤ) → ℝ} (hα : IsProfile X α) :
    AchievableProfile X h α ↔
      ∀ K ∈ X, ∀ k : ℕ, 1 ≤ k → ∃ T, IsCopyProtectedTree X h α (K, k) T
```

`Sec7Standing d X h` is the standing hypothesis of Section 7 (section 4); it requires u > 0, as in
the version of 1 November.

### Theorem 7.7 (topological characterization)

> A q-protected tree rooted at K exists if and only if (K) has an open neighborhood in 𝓗_K that
> admits a q-good geometric decoration.

```lean
theorem thm_7_7 (hS : Sec7Standing d X h) {q : Set (Fin d → ℤ) → ℝ} (hq : IsQuota X q)
    {K : Set (Fin d → ℤ)} (hK : K ∈ X) :
    (∃ T, IsProtectedTree X h q K T) ↔
      ∃ U : Set (History X), IsPrefixClosedNbhd X K U ∧
        ∃ sd ad : List (Set (Fin d → ℤ)) → ℝ, IsQGoodDecoration h q U sd ad
```

The neighbourhood is also required to be closed under prefixes, as Definition 7.6 requires of the
sets it decorates.

### Corollary 7.8 (admissible obstruction-tree characterization)

> Fix a quota profile q and a language K. … A q-protected tree rooted at K exists if and only if
> there is a global geometric assignment Θ such that every admissible obstruction tree rooted at K
> has at least one terminal history that is Θ-good.

```lean
theorem cor_7_8 (hS : Sec7Standing d X h) {q : Set (Fin d → ℤ) → ℝ} (hq : IsQuota X q)
    {K : Set (Fin d → ℤ)} (hK : K ∈ X) :
    (∃ T, IsProtectedTree X h q K T) ↔
      ∃ sd ad : List (Set (Fin d → ℤ)) → ℝ, IsGlobalAssignment X K sd ad ∧
        ∀ T : AdmissibleTree X K, ∃ H ∈ T.leaves, IsThetaGood h q sd ad H
```

The assignment Θ = (s_H, a_H) is the pair of functions `sd`, `ad` on histories.

### Theorem 8.2 (finite-rank near-half guarantee)

> Fix d ≥ 2, τ > 0, and 0 < ε < 1/2, and let 𝒳 be a nonempty countable family of infinite subsets
> of ℤ^d. Define h_τ(V) = log^{1+τ}(2+V). There is one universally eventually valid generator such
> that, for every target K ∈ 𝒳 of finite Cantor–Bendixson point rank, δ_{h_τ}(O,K) ≥ 1/2 − ε.
> No common upper bound on the finite ranks is required.

```lean
theorem thm_8_2 (d : ℕ) (hd : 2 ≤ d) (τ : ℝ) (hτ : 0 < τ) (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2)
    (X : Set (Set (Fin d → ℤ))) (hX : IsLanguageFamily X) :
    ∃ G : Generator (Fin d → ℤ), FreshOn G X ∧ EventuallyValidOn G X ∧
      ∀ K (hK : K ∈ X), HasFinitePointRank X ⟨K, hK⟩ → ∀ x, IsFullEnumeration K x →
        1 / 2 - ε ≤ filteredBanachDensity (hTau τ) (outputSet G x) K
```

`hTau τ V = log(2 + V)^(1+τ)`. The generator is also fresh, the paper's standing requirement.

### Theorem 9.1 (failure of exact half-density)

> Let h : ℕ_{≥1} → (0,∞) be nondecreasing and satisfy sup_{n≥1} n/h(n) = ∞. For every causal
> generator satisfying the freshness condition, there is a full enumeration of ℤ^d on which
> δ_h(O, ℤ^d) < 1/2.

```lean
theorem thm_9_1 (d : ℕ) (hd : 2 ≤ d) (h : ℕ → ℝ) (hh : IsSublinearThreshold h)
    (hmono : ∀ m n, 1 ≤ m → m ≤ n → h m ≤ h n) (G : Generator (Fin d → ℤ))
    (hG : FreshOn G {Set.univ}) :
    ∃ x, IsFullEnumeration Set.univ x ∧
      filteredBanachDensity h (outputSet G x) Set.univ < 1 / 2
```

The theorem does not name d; it is in the paper's part on higher dimensions, and the Lean states it
for d ≥ 2 (nothing is claimed for d = 1). The monotonicity of h, new in the version of 1 November,
is the hypothesis `hmono`; the proof does not use it. Validity is automatic for the target ℤ^d, so
only freshness is assumed.

### Lemma B.2 (every optimal value occurs in one dimension) — new in the version of 1 November

> For every α ∈ [0,1/2], there are a nonempty countable family 𝒳 of infinite subsets of ℤ and
> K ∈ 𝒳 whose optimal lower Banach-density guarantee is b_𝒳(K) = α.

```lean
theorem lem_B_2 (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2) :
    ∃ X : Set (Set ℤ), ∃ K ∈ X, IsLanguageFamily X ∧ bK X K = α ∧
      (∃ G : Generator ℤ, FreshOn G X ∧ EventuallyValidOn G X ∧
        ∀ x, IsFullEnumeration K x → α ≤ lowerBanachDensity (outputSet G x) K) ∧
      (∀ G : Generator ℤ, FreshOn G X → EventuallyValidOn G X →
        ∃ x, IsFullEnumeration K x ∧ lowerBanachDensity (outputSet G x) K ≤ α)
```

"Optimal guarantee b_𝒳(K) = α" is spelled out: b(K) = α, α is achieved, and no generator does
better (the meaning Theorem 1.8 gives to b(K)).

### Lemma B.3 (realization of prescribed optimal profiles) — new in the version of 1 November

> Fix d ≥ 2 and a positive nondecreasing threshold h : ℕ_{≥1} → (0,∞) satisfying
> sup_N N/h(N) = ∞. For every sequence (α_i)_{i≥1} ∈ [0,1/2]^ℕ, there is a countable family of
> distinct infinite languages 𝒳 = {K_i : i ≥ 1} in ℤ^d whose region of simultaneously achievable
> h-filtered density profiles is exactly ∏_{i≥1} [0,α_i]. In particular, one universally eventually
> valid generator attains the greatest profile (α_i)_i. The family may depend on h.

```lean
theorem lem_B_3 (d : ℕ) (hd : 2 ≤ d) (h : ℕ → ℝ) (hh : Sec6.IsAdmissibleThreshold h)
    (α : ℕ → ℝ) (hα : ∀ i, 0 ≤ α i ∧ α i ≤ 1 / 2) :
    ∃ K : ℕ → Set (Fin d → ℤ), Function.Injective K ∧ IsLanguageFamily (Set.range K) ∧
      (∀ a : Set (Fin d → ℤ) → ℝ, Sec7.IsProfile (Set.range K) a →
        (AchievableProfile (Set.range K) h a ↔ ∀ i, a (K i) ≤ α i)) ∧
      (∃ G : Generator (Fin d → ℤ), FreshOn G (Set.range K) ∧
        EventuallyValidOn G (Set.range K) ∧
        ∀ i x, IsFullEnumeration (K i) x →
          α i ≤ filteredBanachDensity h (outputSet G x) (K i))
```

Indexing starts at 0 (`α i`, `K i` are the paper's α_{i+1}, K_{i+1}). "Distinct" is
`Function.Injective K`. A profile takes values in [0,1] (`IsProfile`), so "a(K_i) ≤ α_i for all i"
is "a ∈ ∏[0,α_i]". The family is chosen after h, as the paper allows.

## 4. The definitions these statements use

Lean definitions are in `LocalBreadth/Common.lean` unless another file is named.

- **Model conventions** (before Theorem 1.8): "A full enumeration … of a target K is an infinite
  sequence (x_t)_{t≥1} of elements of K whose range is exactly K; repetitions are permitted. …
  After receiving x_t, the generator produces one output o_t. Throughout the paper we require the
  global freshness condition o_t ∉ S_t ∪ O_{t−1} for every t. We call a point satisfying this
  condition available. … A generator is universally eventually valid on 𝒳 if, for every K ∈ 𝒳
  and every full enumeration of K, all but finitely many outputs belong to K."
  ```lean
  def Generator (α : Type*) : Type _ := List α → α
  def IsFullEnumeration (K : Set α) (x : ℕ → α) : Prop := Set.range x = K
  def inputsUpTo (x : ℕ → α) (t : ℕ) : List α := (List.range (t + 1)).map x
  def output (G : Generator α) (x : ℕ → α) (t : ℕ) : α := G (inputsUpTo x t)
  def outputSet (G : Generator α) (x : ℕ → α) : Set α := Set.range (output G x)
  def IsAvailable (G : Generator α) (x : ℕ → α) : Prop :=
    ∀ t, output G x t ∉ x '' Set.Iic t ∧ output G x t ∉ output G x '' Set.Iio t
  def EventuallyIn (G : Generator α) (x : ℕ → α) (K : Set α) : Prop :=
    ∀ᶠ t in atTop, output G x t ∈ K
  def EventuallyValidOn (G : Generator α) (X : Set (Set α)) : Prop :=
    ∀ K ∈ X, ∀ x, IsFullEnumeration K x → EventuallyIn G x K
  def FreshOn (G : Generator α) (X : Set (Set α)) : Prop :=
    ∀ K ∈ X, ∀ x, IsFullEnumeration K x → IsAvailable G x
  ```
  `x '' Set.Iic t` is {x_0, …, x_t} (the inputs so far) and `output G x '' Set.Iio t` the earlier
  outputs.
- **Language family**: "a nonempty countable family of infinite subsets".
  ```lean
  structure IsLanguageFamily (X : Set (Set α)) : Prop where
    nonempty : X.Nonempty
    countable : X.Countable
    infinite : ∀ L ∈ X, L.Infinite
  ```
- **Boxes and relative density.**
  ```lean
  def boxes : Set (Set α) := {R | ∃ a b : α, a ≤ b ∧ R = Set.Icc a b}
  noncomputable def relDensity (A B R : Set α) : ℝ :=
    ((A ∩ B ∩ R).ncard : ℝ) / ((B ∩ R).ncard : ℝ)
  ```
- **Lower Banach density, Definition 1.3**: d_*(A,B) = liminf_{|R∩B|→∞} |A∩B∩R| / |B∩R| over
  finite axis-parallel boxes R. In Lean: the supremum over s of the infimum over boxes with
  |B ∩ R| ≥ s.
  ```lean
  noncomputable def lowerBanachDensity (A B : Set α) : ℝ :=
    ⨆ s : ℕ, ⨅ R : {R : Set α // R ∈ boxes ∧ s ≤ (B ∩ R).ncard}, relDensity A B R.1
  ```
- **Filtered lower Banach density, Definition 1.4**: δ_h(A,B) = lim_{s→∞} inf { |A∩B∩R| / m_B(R) :
  m_B(R) ≥ s·h(V(R)) }, "an empty infimum is interpreted as 1".
  ```lean
  noncomputable def infOne (S : Set ℝ) : ℝ := by
    classical exact if S.Nonempty then sInf S else 1
  noncomputable def filteredBanachDensity (h : ℕ → ℝ) (A B : Set α) : ℝ :=
    ⨆ s : ℕ, infOne {r | ∃ R ∈ boxes, (s : ℝ) * h R.ncard ≤ (B ∩ R).ncard ∧ r = relDensity A B R}
  noncomputable def hTau (τ : ℝ) (V : ℕ) : ℝ := Real.log (2 + V) ^ (1 + τ)
  ```
- **Finite Cantor–Bendixson point rank, Definition 3.1**: X^{(0)} = X, X^{(r+1)} is X^{(r)} with
  its isolated points removed (in the finite-evidence topology, generated by the sets
  U_{L,F} = {M ∈ X : F ⊆ M ⊆ L}, F ⊆ L finite); L has point rank r if L ∈ X^{(r)} ∖ X^{(r+1)}.
  ```lean
  def basicNbhd (X : Set (Set α)) (L F : Set α) : Set (Set α) := {M | M ∈ X ∧ F ⊆ M ∧ M ⊆ L}
  def finiteEvidenceTopology (X : Set (Set α)) : TopologicalSpace X :=
    TopologicalSpace.generateFrom
      {U | ∃ L ∈ X, ∃ F : Set α, F.Finite ∧ F ⊆ L ∧ U = Subtype.val ⁻¹' basicNbhd X L F}
  def cbDeriv (X : Set (Set α)) : ℕ → Set X
    | 0 => Set.univ
    | r + 1 => cbDeriv X r ∩ @derivedSet X (finiteEvidenceTopology X) (cbDeriv X r)
  def HasPointRank (X : Set (Set α)) (L : X) (r : ℕ) : Prop :=
    L ∈ cbDeriv X r ∧ L ∉ cbDeriv X (r + 1)
  def HasFinitePointRank (X : Set (Set α)) (L : X) : Prop := ∃ r, HasPointRank X L r
  ```
- **Chains, layers, relative intervals, Definition 2.1 (raw pairing score) and equation (eq:cn)**:
  p(H,J) = (1/|J|) Σ_{layers E of H} ⌊|E∩J|/2⌋, and
  c_n(H) = lim_{R→∞} inf { p(H,J) : J a relative interval of A, |J| ≥ n, J ∩ [−R,R] = ∅ }.
  ```lean
  def IsHistory (X : Set (Set α)) (H : List (Set α)) : Prop :=
    H ≠ [] ∧ (∀ L ∈ H, L ∈ X) ∧ H.IsChain (fun L M => M ⊂ L)
  def History (X : Set (Set α)) : Type _ := {H : List (Set α) // IsHistory X H}
  def hStart (H : List (Set α)) : Set α := H.headD ∅
  def hEnd (H : List (Set α)) : Set α := H.getLastD ∅
  def layers {α : Type*} : List (Set α) → List (Set α)
    | [] => []
    | [L] => [L]
    | L :: M :: t => (L \ M) :: layers (M :: t)
  def IsRelInterval (A J : Set ℤ) : Prop := ∃ a b : ℤ, J = A ∩ Set.Icc a b
  noncomputable def rawPairingScore (H : List (Set ℤ)) (J : Set ℤ) : ℝ :=
    (((layers H).map (fun E => (E ∩ J).ncard / 2)).sum : ℝ) / (J.ncard : ℝ)
  noncomputable def pairingScore (n : ℕ) (H : List (Set ℤ)) : ℝ :=
    ⨆ R : ℕ, ⨅ J : {J : Set ℤ // IsRelInterval (hStart H) J ∧ n ≤ J.ncard ∧
        Disjoint J (Set.Icc (-(R : ℤ)) R)}, rawPairingScore H J.1
  ```
  A history is a strictly decreasing chain of languages of X, oldest first. `(E ∩ J).ncard / 2`
  is division in ℕ, i.e. ⌊|E∩J|/2⌋.
- **Admissible obstruction tree, Definition 2.3, and b_n, b (equation (eq:bn))**:
  b_n(K) = inf over admissible trees T with root label K of sup over root-to-leaf paths H of
  c_n(H); b(K) = lim_n b_n(K).
  ```lean
  structure AdmissibleTree (X : Set (Set α)) (K : Set α) where
    nodes : Set (List (Set α))
    root_mem : [K] ∈ nodes
    isHistory : ∀ H ∈ nodes, IsHistory X H ∧ hStart H = K
    prefix_closed : ∀ H M, H ≠ [] → H ++ [M] ∈ nodes → H ∈ nodes
    branching : ∀ H ∈ nodes, (∃ M, H ++ [M] ∈ nodes) →
      ∀ F : Set α, F.Finite → F ⊆ hEnd H → ∃ M, H ++ [M] ∈ nodes ∧ F ⊆ M ∧ M ⊂ hEnd H
    wellFounded : ¬ ∃ f : ℕ → List (Set α), (∀ k, f k ∈ nodes) ∧ ∀ k, ∃ M, f (k + 1) = f k ++ [M]
  def AdmissibleTree.leaves (T : AdmissibleTree X K) : Set (List (Set α)) :=
    {H | H ∈ T.nodes ∧ ∀ M, H ++ [M] ∉ T.nodes}
  noncomputable def bn (X : Set (Set ℤ)) (K : Set ℤ) (n : ℕ) : ℝ :=
    ⨅ T : AdmissibleTree X K, ⨆ H : T.leaves, pairingScore n H.1
  noncomputable def bK (X : Set (Set ℤ)) (K : Set ℤ) : ℝ := ⨆ n : ℕ, bn X K (n + 1)
  ```
  A tree is represented by the set of its root-to-vertex label sequences, so two children of one
  vertex with the same label are merged. Keeping one child per label in a tree of the paper's kind
  gives a tree of this kind, still admissible, whose leaves are leaves of the original; so b_n is
  unchanged (an argument recorded in the docstring, not a Lean proof).
- **Topological number b_n^top** (Theorem 2.6 and the introduction): the supremum, over open
  sets 𝓤 ⊆ 𝓗_K of histories containing (K), of inf_{H∈𝓤} c_n(H). `bnTop` (Common.lean) with the
  history topology of Definition 5.3 (`historyTopology`, Common.lean).
- **Admissible threshold** (Section 6, `Sec6.lean`): "a finite-valued nondecreasing threshold
  h : ℕ_{≥1} → (0,∞) satisfying sup_{N≥1} N/h(N) = ∞".
  ```lean
  def IsThreshold (h : ℕ → ℝ) : Prop :=
    (∀ n, 1 ≤ n → 0 < h n) ∧ ∀ m n, 1 ≤ m → m ≤ n → h m ≤ h n
  structure IsAdmissibleThreshold (h : ℕ → ℝ) : Prop where
    threshold : IsThreshold h
    unbounded : ∀ C : ℝ, ∃ N : ℕ, 1 ≤ N ∧ C < (N : ℝ) / h N
  ```
- **β_{G,h}(L) and β_h(L)** (Section 6): "the largest α ∈ [0,1] such that G guarantees
  δ_h(O,L) ≥ α on every full enumeration of L … β_h(L) = sup_G β_{G,h}(L), where the supremum is
  over generators eventually valid on the entire candidate family 𝒳".
  ```lean
  noncomputable def betaG (h : ℕ → ℝ) (G : Generator α) (L : Set α) : ℝ :=
    sSup {a : ℝ | a ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ x, IsFullEnumeration L x → a ≤ filteredBanachDensity h (outputSet G x) L}
  noncomputable def betaOpt (X : Set (Set α)) (h : ℕ → ℝ) (L : Set α) : ℝ :=
    ⨆ G : {G : Generator α // FreshOn G X ∧ EventuallyValidOn G X}, betaG h G.1 L
  ```
- **Achievable profile** (Section 7): one generator, fresh and universally eventually valid on X,
  guarantees δ_h(O,K) ≥ a(K) for every K ∈ X and every full enumeration of K.
  ```lean
  def AchievableProfile (X : Set (Set α)) (h : ℕ → ℝ) (a : Set α → ℝ) : Prop :=
    ∃ G : Generator α, FreshOn G X ∧ EventuallyValidOn G X ∧
      ∀ K ∈ X, ∀ x, IsFullEnumeration K x → a K ≤ filteredBanachDensity h (outputSet G x) K
  ```
- **Standing hypotheses of Section 7** (`Sec7.lean`): "Throughout this section, fix d ≥ 2 and a
  nonempty countable family 𝒳 of infinite subsets of ℤ^d. … fix a threshold of the form
  h(V) = u(V) log(2+V), where u : [1,∞) → (0,∞) is nondecreasing", with h a threshold as in
  Definition 1.4; profiles and quotas take values in [0,1].
  ```lean
  structure Sec7Threshold (h : ℕ → ℝ) : Prop where
    threshold : IsThreshold h
    factor : ∃ u : ℕ → ℝ, (∀ V, 1 ≤ V → 0 < u V) ∧ (∀ V W, 1 ≤ V → V ≤ W → u V ≤ u W) ∧
      ∀ V, 1 ≤ V → h V = u V * Real.log (2 + V)
  structure Sec7Standing (d : ℕ) (X : Set (Set (Fin d → ℤ))) (h : ℕ → ℝ) : Prop where
    two_le_d : 2 ≤ d
    family : IsLanguageFamily X
    thresh : Sec7Threshold h
  def IsQuota (X : Set (Set (Fin d → ℤ))) (q : Set (Fin d → ℤ) → ℝ) : Prop :=
    ∀ L ∈ X, 0 ≤ q L ∧ q L ≤ 1
  def IsProfile (X : Set (Set (Fin d → ℤ))) (α : Set (Fin d → ℤ) → ℝ) : Prop :=
    ∀ L ∈ X, 0 ≤ α L ∧ α L ≤ 1
  ```
  u is given on the integers V ≥ 1 only; only these values are used.
- **The structural notions of Section 7** used by Theorems 7.2, 7.7 and Corollary 7.8 are longer
  and are not reproduced here; each is in `Sec7.lean` with the paper's wording in its docstring:
  the finite stopping game and geometric q-feasibility (Definition 7.4, `IsQFeasible`, built on
  `Reachable`, `IsLegalReply`, `packetSupport`), the q-protected tree (Definition 7.5,
  `IsProtectedTree`), geometric decorations (Definition 7.6, `IsGeomDecoration`,
  `IsQGoodDecoration`, `IsPrefixClosedNbhd`), the global geometric assignment and Θ-good histories
  of Corollary 7.8 (`IsGlobalAssignment`, `IsThetaGood`), and the protected tree on accuracy copies
  (Definition 7.14, `IsCopyProtectedTree`, with quotas q(K,k) = (α(K) − 2^{−k})_+, `copyQuota`).
- **Threshold of Theorem 9.1** (`Sec9.lean`): h : ℕ_{≥1} → (0,∞) with sup n/h(n) = ∞ (the
  monotonicity added on 1 November is the separate hypothesis `hmono` of `thm_9_1`).
  ```lean
  structure IsSublinearThreshold (h : ℕ → ℝ) : Prop where
    pos : ∀ n, 1 ≤ n → 0 < h n
    unbounded : ∀ C : ℝ, ∃ n : ℕ, 1 ≤ n ∧ C < (n : ℝ) / h n
  ```

## 5. What has and has not been reviewed

- **The kernel check and the axiom check** are mechanical and reproducible by anyone with the
  commands of section 2. The independent kernel replay is reported in section 2.
- **Faithfulness of the statements** (part 1 of section 1) is a human judgement. During the
  formalization, separate Claude instances (each given a single criterion and no access to the
  others' reviews) compared the Lean statements with the paper. The formalization was first made
  for the version of the paper of 31 October 2026; the results that are new or changed in the
  version of 1 November (Lemmas B.2, B.3, Claims B.4, B.5, the Section 7 threshold, Lemma 6.4,
  Lemma 8.1, Theorem 9.1) were then formalized on top of it and checked by one further
  independent Claude reviewer, who found them faithful. These reviewers are instances of the same
  AI model that wrote the code, so they are not independent in the way a human referee is. **No
  human has yet checked the Lean statements against the paper, and the authors have not yet
  reviewed this certificate.** Sections 1a, 3 and 4 are written so that a mathematician can check
  the main statements without knowing Lean.
- **Differences from the paper that a reader should know.** Each is a convention or a formal
  reading, not a change of meaning:
  - "for every eventually valid generator" ranges over generators that are also fresh (the paper's
    standing requirement), and constructed generators are shown to be fresh as well;
  - 0-based time and indexing (`x t` is x_{t+1}; in Lemma B.3, `K i` is K_{i+1});
  - limits of nondecreasing quantities are written as suprema over ℕ;
  - obstruction trees merge equal-labelled siblings (section 4);
  - Theorem 9.1 and Lemma 9.2 are stated for d ≥ 2 (the paper names no dimension there);
  - in Section 7 the factor u is given on integers V ≥ 1. Before Lemma 7.11 the paper restates the
    threshold with u : [1,∞) → [1,∞); the Lean follows the standing definition u : [1,∞) → (0,∞)
    (the stronger theorems, which imply the other reading).

  Some hypotheses stated in the paper are not needed by the Lean proofs and are kept so that the
  statements are the paper's; for the main theorems these are the monotonicity of h in
  Theorem 9.1, and, in Theorems 7.7 and Corollary 7.8, that q is a quota and parts of the Section 7
  standing hypotheses. The Lean docstrings say so.
- **Intermediate results.** `LocalBreadth/Main.lean` lists the numbered items with their Lean
  names. Some proofs take a different route from the paper's. Some readings concern intermediate
  results only (section 6). A detailed audit report and an addendum for the version of 1 November
  are available from the authors on request.
- **Line references in the Lean docstrings.** References marked "Nov 1 revision" are to the
  version of 1 November. Other `tex l.` references are to the version of 31 October, on which the
  formalization was first made; the numbering of results is the same in both, except for
  Appendices B and C (section 6).

## 6. All numbered results

Status "proved" means: stated in Lean and proved, with no `sorry` and standard axioms only.
Definitions are "defined". Notes point to readings that a reader should know.

| Paper | Lean | Status |
|---|---|---|
| Definition 1.2 | `lowerAsymptoticDensity` | defined |
| Definition 1.3 | `lowerBanachDensity` | defined |
| Definition 1.4 | `filteredBanachDensity` | defined |
| Theorem 1.5 | `thm_1_5` | proved |
| Corollary 1.6 | `cor_1_6` | proved |
| Theorem 1.7 | `thm_1_7` | proved |
| Theorem 1.8 | `thm_1_8` | proved |
| Definition 2.1 | `rawPairingScore` | defined |
| Claim 2.2 | `claim_2_2` | proved |
| Definition 2.3 | `AdmissibleTree` | defined (equal-labelled siblings merged, section 4) |
| Claim 2.4 | `claim_2_4` | proved |
| Theorem 2.5 | `thm_2_5` | proved |
| Theorem 2.6 | `thm_2_6` | proved |
| Definition 3.1 | `cbDeriv` `HasPointRank` `HasFiniteCBRank` | defined |
| Lemma 3.2 | `lem_3_2` | proved |
| Corollary 3.3 | `cor_3_3_part1` `cor_3_3_part2` | proved |
| Theorem 4.1 | `thm_4_1` | proved |
| Lemma 4.2 | `lem_4_2` | proved |
| Theorem 5.1 | `Sec5.thm_5_1` | proved |
| Definition 5.2 | `Sec5.IsUnsafeHistory` `Sec5.IsSafeHistory` | defined |
| Definition 5.3 | `historyTopology` `InBasicNbhd` `historyBasicOpens` | defined |
| Lemma 5.4 | `Sec5.lem_5_4` | proved |
| Lemma 5.5 | `Sec5.lem_5_5` | proved |
| Lemma 5.6 | `Sec5.lem_5_6` | proved |
| Corollary 5.7 | `Sec5.cor_5_7_part1` `Sec5.cor_5_7_part2` | proved |
| Theorem 5.8 | `thm_2_6` | proved (restatement of Theorem 2.6) |
| Theorem 5.9 | `Sec5.thm_5_9_part1` `Sec5.thm_5_9_part2` | proved |
| Corollary 5.10 | `Sec5.cor_5_10_part1` `Sec5.cor_5_10_part2` `Sec5.cor_5_10_part3` | proved |
| Definition 5.11 | `Sec5.IsProtectedSet` | defined |
| Lemma 5.12 | `Sec5.lem_5_12` | proved |
| Lemma 5.13 | `Sec5.lem_5_13` | proved |
| Lemma 5.14 | `Sec5.lem_5_14` | proved |
| Lemma 5.15 | `Sec5.lem_5_15` | proved |
| Lemma 5.16 | `Sec5.lem_5_16` | proved |
| Lemma 5.17 | `Sec5.lem_5_17` | proved |
| Lemma 5.18 | `Sec5.lem_5_18` | proved |
| Corollary 5.19 | `Sec5.cor_5_19` | proved |
| Lemma 5.20 | `Sec5.lem_5_20` | proved |
| Lemma 5.21 | `Sec5.lem_5_21` | proved |
| Lemma 5.22 | `Sec5.lem_5_22` | proved |
| Theorem 5.23 | `Sec5.thm_5_23` | proved |
| Theorem 6.1 | `Sec6.thm_6_1` | proved |
| Theorem 6.2 | `Sec6.thm_6_2` | proved |
| Lemma 6.3 | `Sec6.lem_6_3` | proved; the Lean adds "L countable", left implicit in Section 6 |
| Lemma 6.4 | `Sec6.lem_6_4` | proved |
| Lemma 6.5 | `Sec6.lem_6_5` | proved |
| Claim 6.6 | `Sec6.claim_6_6` | proved |
| Theorem 7.1 | `Sec7.thm_7_1_part1` `Sec7.thm_7_1_part2` | proved |
| Theorem 7.2 | `Sec7.thm_7_2` | proved |
| Theorem 7.3 | `Sec7.thm_7_3_part1` `Sec7.thm_7_3_part2` | proved |
| Definition 7.4 | `Sec7.IsQFeasible` | defined |
| Definition 7.5 | `Sec7.IsProtectedTree` | defined |
| Definition 7.6 | `Sec7.IsGeomDecoration` `Sec7.IsQGoodDecoration` | defined |
| Theorem 7.7 | `Sec7.thm_7_7` | proved |
| Corollary 7.8 | `Sec7.cor_7_8` | proved |
| Corollary 7.9 | `Sec7.cor_7_9` | proved |
| Lemma 7.10 | `Sec7.lem_7_10` | proved |
| Lemma 7.11 | `Sec7.lem_7_11` | proved |
| Lemma 7.12 | `Sec7.lem_7_12` | proved |
| Lemma 7.13 | `Sec7.lem_7_13` | proved, under a weaker reading of its item 1 (docstring) |
| Definition 7.14 | `Sec7.IsCopyProtectedTree` | defined |
| Lemma 7.15 | `Sec7.lem_7_15` | proved |
| Lemma 7.16 | `Sec7.lem_7_16` | proved |
| Lemma 7.17 | `Sec7.lem_7_17` | proved |
| Lemma 8.1 | `lem_8_1` | proved |
| Theorem 8.2 | `thm_8_2` | proved |
| Theorem 9.1 | `Sec9.thm_9_1` | proved, for d ≥ 2 |
| Lemma 9.2 | `Sec9.lem_9_2` | proved, for d ≥ 2 |
| Definition A.1 | `AppA.IsActivatedVertex` | defined |
| Lemma A.2 | `AppA.lem_A_2` | proved; the potentials' properties (P1)–(P4) are required at every consistent game state (docstring) |
| Claim A.3 | `AppA.claim_A_3` | proved |
| Claim A.4 | `AppA.claim_A_4` | proved |
| Proposition A.5 | `AppA.prop_A_5` | proved; same reading as Lemma A.2, parameter conditions read uniformly (`AppA.GoodParameters`) |
| Claim A.6 | `AppA.claim_A_6` | proved |
| Proposition B.1 | `AppB.prop_B_1` | proved under the hypothesis `AppB.IsKWZeroFamily` (the properties of the cited family 𝒳₀, which the paper does not define); a family with these properties is constructed in `KWZeroFamily.lean` |
| Lemma B.2 | `AppB.lem_B_2` | proved (new on 1 November) |
| Lemma B.3 | `AppB.lem_B_3` | proved (new on 1 November) |
| Claim B.4 | `AppB3.claim_B_4` | proved (new on 1 November) |
| Claim B.5 | `AppB3.claim_B_5` | proved (new on 1 November) |

Appendix C (Lemma C.1) of the version of 31 October was deleted on 1 November. Its Lean statement
and proof (`lem_C_1`, `LocalBreadth/AppC.lean`) are kept, marked "Retired", and still checked;
nothing else uses them. The unnumbered definitions the paper introduces in its text are listed
with their Lean names at the end of `LocalBreadth/Main.lean`.

## 7. How this formalization was produced

The Lean code was written by Claude (Anthropic's AI model), running in Claude Code, under the
formalize-paper autoformalization and auditing workflow designed and directed by Runtian Zhou.
Separate Claude instances, each given one criterion and no access to the others' reviews, audited
the Lean statements against the paper and the proofs for substance (see section 5 for what this
does and does not establish). The additions for the version of 1 November were built on the
delivered Lean by further Claude agents, checked by an independent Claude reviewer and re-checked
by the kernel replay of section 2. The formalization builds on Lean's Mathlib library.
