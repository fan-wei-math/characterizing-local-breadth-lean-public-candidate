import BanachDensity1D.Common

/-!
# The one-dimensional model: languages, generators, lower Banach density

Kleinberg–Wei, *Determination of lower Banach density in the KM model*: the setting of
Section 1.1 (generation in the limit), Definition 1.3 for `d = 1`, and Definition 2.1.

* A *language class* `X` is a nonempty countable family of infinite subsets of `ℤ`
  (`LangClass`).
* A *generator* sees the inputs `w 0, …, w t` and produces the output `o t`
  (`Generator`, `Generator.out`). Since a generator is deterministic, its own earlier outputs are
  a function of the inputs, so a map `List ℤ → ℤ` describes every generator.
* A *full enumeration* (complete text, string enumeration) of `K` is a sequence `w : ℕ → ℤ`
  whose set of values is exactly `K` (`IsFullEnumeration`); repetitions are allowed.
* An output is *available* if it has neither been input nor output before (Section 1.1:
  "a new string … that has neither been revealed nor previously generated").
* Every generator of the model outputs an available string at every round, on every input
  sequence (`Generator.Admissible`); it may output strings outside the target. Every theorem
  quantifies over admissible generators only.
* A generator is *eventually valid* on a text of `K` if from some time on every output lies in
  `K` and is available (Section 1.1, generation in the limit); for an admissible generator the
  availability part holds at every round anyway.
-/

namespace BanachDensity1D

open Set

/-- The standing hypothesis of Part *Dimension one*: `X` is a nonempty countable collection of
infinite subsets of `ℤ`. -/
structure LangClass (X : Set (Set ℤ)) : Prop where
  nonempty : X.Nonempty
  countable : X.Countable
  infinite : ∀ L ∈ X, L.Infinite

/-! ## Definition 1.3 (`d = 1`): lower Banach density -/

/-- **Definition 1.3** (`def:banach-intro`), specialized to dimension one. For `A ⊆ B ⊆ ℤ` with
`B` infinite,
`δ_B(A,B) = liminf_{|R ∩ B| → ∞} |A ∩ R| / |B ∩ R|`,
where `R` ranges over the finite axis-parallel boxes of `ℤ`, i.e. the integer intervals
`[a, b]`. The `liminf` as `|R ∩ B| → ∞` is `lim_{n→∞} inf_{|R ∩ B| ≥ n}`, and the infimum is
nondecreasing in `n`, so the limit is the supremum over `n`. -/
noncomputable def def_banach_intro (A B : Set ℤ) : ℝ :=
  ⨆ n : ℕ, ⨅ R : {R : ℤ × ℤ // n ≤ (B ∩ Icc R.1 R.2).ncard},
    ((A ∩ Icc R.1.1 R.1.2).ncard : ℝ) / (B ∩ Icc R.1.1 R.1.2).ncard

/-- The density of an output set `O` in the target `K`, by the author's convention
`δ_B(O, K) := δ_B(O ∩ K, K)` (Definition 1.3 with `d = 1`). -/
noncomputable def outputDensity (O K : Set ℤ) : ℝ :=
  def_banach_intro (O ∩ K) K

namespace BasicAux

open Filter Topology

/-- An infinite set of integers has at least `n` points in some interval `[a, b]`. -/
lemma exists_Icc_ncard_ge {K : Set ℤ} (hK : K.Infinite) (n : ℕ) :
    ∃ a b : ℤ, n ≤ (K ∩ Icc a b).ncard := by
  obtain ⟨t, htK, htn⟩ := hK.exists_subset_card_eq n
  obtain ⟨a, ha⟩ := (t : Set ℤ).toFinite.bddBelow
  obtain ⟨b, hb⟩ := (t : Set ℤ).toFinite.bddAbove
  refine ⟨a, b, ?_⟩
  have hsub : (t : Set ℤ) ⊆ K ∩ Icc a b := fun x hx => ⟨htK hx, ha hx, hb hx⟩
  have hfin : (K ∩ Icc a b).Finite := (finite_Icc a b).subset inter_subset_right
  calc n = (t : Set ℤ).ncard := by rw [ncard_coe_finset, htn]
    _ ≤ _ := ncard_le_ncard hsub hfin

/-- For infinite `B`, the index family of the `n`-th infimum is nonempty. -/
theorem banach_inf_nonempty {B : Set ℤ} (hB : B.Infinite) (n : ℕ) :
    Nonempty {R : ℤ × ℤ // n ≤ (B ∩ Icc R.1 R.2).ncard} := by
  obtain ⟨a, b, h⟩ := exists_Icc_ncard_ge hB n
  exact ⟨⟨(a, b), h⟩⟩

/-- For `A ⊆ B` every ratio `|A ∩ [a,b]| / |B ∩ [a,b]|` is at most `1`. -/
theorem banach_ratio_le_one {A B : Set ℤ} (hAB : A ⊆ B) (a b : ℤ) :
    ((A ∩ Icc a b).ncard : ℝ) / (B ∩ Icc a b).ncard ≤ 1 := by
  have hfin : (B ∩ Icc a b).Finite := (finite_Icc a b).subset inter_subset_right
  have hle : (A ∩ Icc a b).ncard ≤ (B ∩ Icc a b).ncard :=
    ncard_le_ncard (inter_subset_inter_left _ hAB) hfin
  rcases Nat.eq_zero_or_pos (B ∩ Icc a b).ncard with h0 | hpos
  · simp [h0]
  · rw [div_le_one (by exact_mod_cast hpos)]; exact_mod_cast hle

/-- The `n`-th infimum in `def_banach_intro A B`. -/
noncomputable def banachInf (A B : Set ℤ) (n : ℕ) : ℝ :=
  ⨅ R : {R : ℤ × ℤ // n ≤ (B ∩ Icc R.1 R.2).ncard},
    ((A ∩ Icc R.1.1 R.1.2).ncard : ℝ) / (B ∩ Icc R.1.1 R.1.2).ncard

/-- The ratios are bounded below (the proof uses the bound `0`). -/
theorem banachInf_bddBelow (A B : Set ℤ) (n : ℕ) :
    BddBelow (range fun R : {R : ℤ × ℤ // n ≤ (B ∩ Icc R.1 R.2).ncard} =>
      ((A ∩ Icc R.1.1 R.1.2).ncard : ℝ) / (B ∩ Icc R.1.1 R.1.2).ncard) :=
  ⟨0, by rintro _ ⟨R, rfl⟩; positivity⟩

/-- The infima are nonnegative. -/
theorem banachInf_nonneg (A B : Set ℤ) (n : ℕ) : 0 ≤ banachInf A B n := by
  unfold banachInf
  rcases isEmpty_or_nonempty {R : ℤ × ℤ // n ≤ (B ∩ Icc R.1 R.2).ncard} with h | h
  · simp
  · exact le_ciInf fun R => by positivity

/-- For infinite `B`, the infima are nondecreasing in `n`. -/
theorem banachInf_mono {A B : Set ℤ} (hB : B.Infinite) : Monotone (banachInf A B) := by
  intro m n hmn
  have := banach_inf_nonempty hB n
  refine le_ciInf fun R => ?_
  exact ciInf_le (banachInf_bddBelow A B m) ⟨R.1, hmn.trans R.2⟩

/-- For `A ⊆ B` with `B` infinite, the infima are at most `1`. -/
theorem banachInf_le_one {A B : Set ℤ} (hAB : A ⊆ B) (hB : B.Infinite) (n : ℕ) :
    banachInf A B n ≤ 1 := by
  obtain ⟨R⟩ := banach_inf_nonempty hB n
  exact (ciInf_le (banachInf_bddBelow A B n) R).trans (banach_ratio_le_one hAB _ _)

/-- `outputDensity O K = δ_B(O ∩ K, K)` is the limit of its infima and lies in `[0, 1]`, for
infinite `K`. -/
theorem outputDensity_tendsto {O K : Set ℤ} (hK : K.Infinite) :
    Tendsto (banachInf (O ∩ K) K) atTop (𝓝 (outputDensity O K)) ∧
      0 ≤ outputDensity O K ∧ outputDensity O K ≤ 1 := by
  have hb : BddAbove (range (banachInf (O ∩ K) K)) :=
    ⟨1, by rintro _ ⟨n, rfl⟩; exact banachInf_le_one inter_subset_right hK n⟩
  have h := tendsto_atTop_ciSup (banachInf_mono (A := O ∩ K) hK) hb
  have heq : outputDensity O K = ⨆ n, banachInf (O ∩ K) K n := rfl
  refine ⟨heq ▸ h, ?_, ?_⟩
  · rw [heq]; exact (banachInf_nonneg _ K 0).trans (le_ciSup hb 0)
  · rw [heq]; exact ciSup_le fun n => banachInf_le_one inter_subset_right hK n

end BasicAux

/-! ## Generators and enumerations -/

/-- A generator: given the inputs `w 0, …, w t` revealed so far (in order), it produces its
output for round `t`. -/
abbrev Generator := List ℤ → ℤ

/-- The inputs `w 0, …, w t` of the first `t + 1` rounds. -/
def inputsUpTo (w : ℕ → ℤ) (t : ℕ) : List ℤ := List.ofFn fun i : Fin (t + 1) => w i

namespace BasicAux

/-- If `w` agrees with `h` on the first `|h|` places, the inputs of the rounds `≤ t < |h|` are
`h.take (t + 1)`. -/
theorem inputsUpTo_eq {w : ℕ → ℤ} {h : List ℤ} (hw : ∀ i (hi : i < h.length), w i = h[i])
    {t : ℕ} (ht : t < h.length) : inputsUpTo w t = h.take (t + 1) := by
  unfold inputsUpTo
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_take]; omega
  · intro i h1 h2
    simp only [List.getElem_ofFn, List.getElem_take]
    exact hw i (by simp only [List.length_ofFn] at h1; omega)

/-- Prefixes of the inputs: for `r ≤ t`, the first `r + 1` inputs up to round `t` are the inputs
up to round `r` (the instance `h := inputsUpTo w t` of `inputsUpTo_eq`). -/
lemma inputsUpTo_take (w : ℕ → ℤ) {r t : ℕ} (h : r ≤ t) :
    (inputsUpTo w t).take (r + 1) = inputsUpTo w r :=
  (inputsUpTo_eq (h := inputsUpTo w t)
    (fun _ _ => by simp only [inputsUpTo, List.getElem_ofFn])
    (by simp only [inputsUpTo, List.length_ofFn]; omega)).symm

end BasicAux

/-- A full enumeration (complete text) of `K`: every value is in `K` and every point of `K`
appears. -/
def IsFullEnumeration (w : ℕ → ℤ) (K : Set ℤ) : Prop := range w = K

namespace Generator

/-- The output of `G` in round `t` on the text `w`. -/
def out (G : Generator) (w : ℕ → ℤ) (t : ℕ) : ℤ := G (inputsUpTo w t)

/-- The output set `O` of `G` on the text `w`. -/
def outputSet (G : Generator) (w : ℕ → ℤ) : Set ℤ := range (G.out w)

/-- The output of round `t` is *available*: it is none of the inputs `w 0, …, w t` and none of
the earlier outputs. -/
def Available (G : Generator) (w : ℕ → ℤ) (t : ℕ) : Prop :=
  (∀ i ≤ t, w i ≠ G.out w t) ∧ ∀ s < t, G.out w s ≠ G.out w t

/-- Every output is available. -/
def AllAvailable (G : Generator) (w : ℕ → ℤ) : Prop := ∀ t, G.Available w t

/-- `G` is a generator of the model (*admissible*): on every input sequence, the output of every
round is available, i.e. it is neither an input revealed so far (including the current one) nor
an earlier output. Outputs outside the target are allowed; availability is required at every
round, for every finite input history (each is a prefix of some sequence `w`). This is the
model; Section 1.1 states the
newness requirement, and the paper's proofs use it for every generator (e.g. Theorem 5.1). -/
def Admissible (G : Generator) : Prop := ∀ w t, G.Available w t

/-- All but finitely many outputs belong to `K`: only finitely many rounds have an output
outside `K`. -/
def AlmostAllIn (G : Generator) (w : ℕ → ℤ) (K : Set ℤ) : Prop :=
  {t | G.out w t ∉ K}.Finite

/-- `G` is eventually valid on the text `w` of `K`: from some round on, every output belongs to
`K` and is available (generation in the limit, Section 1.1). -/
def EventuallyValid (G : Generator) (w : ℕ → ℤ) (K : Set ℤ) : Prop :=
  ∃ t₀, ∀ t ≥ t₀, G.out w t ∈ K ∧ G.Available w t

/-- `G` is eventually valid on every full enumeration of every language in `X`. -/
def EventuallyValidOn (G : Generator) (X : Set (Set ℤ)) : Prop :=
  ∀ K ∈ X, ∀ w, IsFullEnumeration w K → G.EventuallyValid w K

end Generator

/-! ## Definition 2.1: the finite-evidence topology and Cantor–Bendixson rank -/

/-- The basic open set `U_{L,F} = {M ∈ X : F ⊆ M ⊆ L}`, as a set of points of the subspace `X`. -/
def evidenceSet (X : Set (Set ℤ)) (L F : Set ℤ) : Set X := {M | F ⊆ M.1 ∧ M.1 ⊆ L}

/-- **Definition 2.1** (`CBrank`), first part: the finite-evidence topology on `X`, generated by
the sets `U_{L,F}` with `L ∈ X` and `F ⊆ L` finite. -/
abbrev evidenceTopology (X : Set (Set ℤ)) : TopologicalSpace X :=
  TopologicalSpace.generateFrom
    {U | ∃ L ∈ X, ∃ F : Set ℤ, F.Finite ∧ F ⊆ L ∧ U = evidenceSet X L F}

/-- **Definition 2.1** (`CBrank`): the Cantor–Bendixson derivatives `X^{(r)}`. `X^{(0)} = X`,
and `X^{(r+1)}` is `X^{(r)}` with its isolated points (isolated in the subspace `X^{(r)}`)
removed; `x` is isolated in `S` when some open `U` has `U ∩ S = {x}`. -/
def cbDerived (X : Set (Set ℤ)) : ℕ → Set X
  | 0 => univ
  | r + 1 => {x | x ∈ cbDerived X r ∧
      ¬ ∃ U : Set X, (evidenceTopology X).IsOpen U ∧ U ∩ cbDerived X r = {x}}

/-- **Definition 2.1** (`CBrank`): the language `L` has rank `r`, i.e.
`L ∈ X^{(r)} \ X^{(r+1)}`. -/
def CBrank (X : Set (Set ℤ)) (L : Set ℤ) (r : ℕ) : Prop :=
  ∃ h : L ∈ X, (⟨L, h⟩ : X) ∈ cbDerived X r ∧ (⟨L, h⟩ : X) ∉ cbDerived X (r + 1)

/-- **Definition 2.1** (`CBrank`): `X` has finite Cantor–Bendixson rank, i.e.
`X^{(r)} = ∅` for some `r`. -/
def FiniteCBRank (X : Set (Set ℤ)) : Prop := ∃ r, cbDerived X r = ∅

end BanachDensity1D
