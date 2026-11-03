import Mathlib

/-!
# The model and the densities

Kleinberg–Wei, *Characterizing Local Breadth in Language Generation*.
Historical source numbering is retained; current mappings are in the release registry.

-/

namespace BanachDensityHD

open Set Filter
open scoped Classical

/-! ## Ambient space, rectangles, counting -/

/-- `ℤ^d`. -/
abbrev Pt (d : ℕ) := Fin d → ℤ

/-- A rectangle: a nonempty finite axis-parallel integer box `∏ᵢ [loᵢ, hiᵢ]` (singleton sides
allowed), §8 "Rectangles". -/
inductive Rect (d : ℕ)
  | mk (lo hi : Pt d) (le : lo ≤ hi)

/-- The lower corner `lo` of a rectangle. -/
def Rect.lo {d : ℕ} : Rect d → Pt d
  | .mk lo _ _ => lo

/-- The upper corner `hi` of a rectangle. -/
def Rect.hi {d : ℕ} : Rect d → Pt d
  | .mk _ hi _ => hi

/-- The corners of a rectangle are ordered: `lo ≤ hi`. -/
theorem Rect.le {d : ℕ} : ∀ R : Rect d, R.lo ≤ R.hi
  | .mk _ _ h => h

/-- The lattice points of a rectangle. -/
def Rect.pts {d : ℕ} (R : Rect d) : Set (Pt d) := Icc R.lo R.hi

/-- `V(R) = |R|`, the number of lattice points. -/
noncomputable def Rect.vol {d : ℕ} (R : Rect d) : ℕ := R.pts.ncard

/-- `m_L(R) = |L ∩ R|`. -/
noncomputable def mass {d : ℕ} (L : Set (Pt d)) (R : Rect d) : ℕ := (L ∩ R.pts).ncard

/-- `Q_a = [-a,a]^d ∩ ℤ^d`. -/
def core (d : ℕ) (a : ℝ) : Set (Pt d) := {x | ∀ i, |(x i : ℝ)| ≤ a}

/-! ## The generator model (ported from `BanachDensity1D.Generator`, generalized) -/

/-- The standing hypothesis: `X` is a nonempty countable class of infinite sets. -/
structure LangClass {α : Type*} (X : Set (Set α)) : Prop where
  nonempty : X.Nonempty
  countable : X.Countable
  infinite : ∀ L ∈ X, L.Infinite

/-- A deterministic causal generator: from the inputs `x₁,…,x_t` (in order) it produces `y_t`. -/
abbrev Generator (α : Type*) := List α → α

/-- The inputs of rounds `0,…,t`. -/
def inputsUpTo {α : Type*} (w : ℕ → α) (t : ℕ) : List α := List.ofFn fun i : Fin (t + 1) => w i

/-- A full enumeration of `K`: an input sequence with range exactly `K` (repetitions allowed). -/
def IsFullEnumeration {α : Type*} (w : ℕ → α) (K : Set α) : Prop := range w = K

namespace Generator
variable {α : Type*}

/-- The output `y_t` on input sequence `w`. -/
def out (G : Generator α) (w : ℕ → α) (t : ℕ) : α := G (inputsUpTo w t)

/-- The output set `O`. -/
def outputSet (G : Generator α) (w : ℕ → α) : Set α := range (G.out w)

/-- Global freshness, eq. (fresh): `y_t ∉ S_t ∪ O_{t-1}` at every round of every input sequence
This is the global freshness model throughout Part HD. -/
def Fresh (G : Generator α) : Prop :=
  ∀ w t, (∀ i ≤ t, w i ≠ G.out w t) ∧ ∀ s < t, G.out w s ≠ G.out w t

/-- Only finitely many outputs lie outside `K`. -/
def EventuallyValid (G : Generator α) (w : ℕ → α) (K : Set α) : Prop :=
  {t | G.out w t ∉ K}.Finite

/-- Universally eventually valid on `X`: on every full enumeration of every target in `X`. -/
def EventuallyValidOn (G : Generator α) (X : Set (Set α)) : Prop :=
  ∀ K ∈ X, ∀ w, IsFullEnumeration w K → G.EventuallyValid w K

end Generator

/-- The generators of the model that are eventually valid on all of `X`. -/
def ValidGen {α : Type*} (X : Set (Set α)) : Set (Generator α) :=
  {G | G.Fresh ∧ G.EventuallyValidOn X}

/-! ## Densities -/

/-- An admissible threshold (§7, §10, Q7): `h : ℕ_{≥1} → (0,∞)` finite-valued, nondecreasing,
with `sup_{V ≥ 1} V / h(V) = ∞`. (Values at `0` are irrelevant: `V(R) ≥ 1`.) -/
def IsThreshold (h : ℕ → ℝ) : Prop :=
  (∀ n, 1 ≤ n → 0 < h n) ∧ MonotoneOn h (Ici 1) ∧
    ¬ BddAbove ((fun n : ℕ => (n : ℝ) / h n) '' Ici 1)

/-- The inner infimum of `δ_h` at level `λ`: the infimum of `|O ∩ L ∩ R| / m_L(R)` over the
level-`λ` tests `m_L(R) ≥ λ h(|R|)`; an empty test set has infimum `1`. Division is total:
a zero-mass test contributes `0`, so level `0` with empty `L` has infimum `0`, not `1`.
For positive levels and positive thresholds, admitted tests have positive mass, giving the
positive-denominator density interpretation. -/
noncomputable def testInf {d : ℕ} (h : ℕ → ℝ) (O L : Set (Pt d)) (s : ℝ) : ℝ :=
  let S := {r : ℝ | ∃ R : Rect d, s * h R.vol ≤ mass L R ∧
                    r = ((O ∩ L ∩ R.pts).ncard : ℝ) / mass L R}
  if S.Nonempty then sInf S else 1

/-- **`δ_h(O,L)`** (§7, eq. (density) of §8): `lim_{λ → ∞}` of the level-`λ` infimum. -/
noncomputable def deltaH {d : ℕ} (h : ℕ → ℝ) (O L : Set (Pt d)) : ℝ :=
  limUnder atTop (testInf h O L)

/-- **Definition 1.3** (`def:banach-intro`), literally, with values in the extended reals:
for `A, B ⊆ ℤ^d`, `d_banach(A,B) = liminf_{|R ∩ B| → ∞} |A ∩ R| / |B ∩ R|
= sup_n inf_{|R ∩ B| ≥ n} |A ∩ R| / |B ∩ R|`. `A` need not lie inside `B`, so the value may be
`+∞` (for instance a sparse infinite `B` inside a dense `A`); a real-valued limit could not
represent it. For infinite `B` with `A \ B` finite it is finite and equals `δ₁(A,B)`
(`banach_eq_deltaH_one`). -/
noncomputable def banach {d : ℕ} (A B : Set (Pt d)) : EReal :=
  ⨆ n : ℕ, ⨅ (R : Rect d) (_ : n ≤ mass B R), ((((A ∩ R.pts).ncard : ℝ) / mass B R : ℝ) : EReal)

/-- The conditions on `g` in **Definition 1.8**: `g : [1,∞) → [1,∞)` nondecreasing, `g → ∞`. -/
def GoodG (g : ℝ → ℝ) : Prop :=
  (∀ x, 1 ≤ x → 1 ≤ g x) ∧ MonotoneOn g (Ici 1) ∧ Tendsto g atTop atTop

/-- The filter function of Definitions 1.8–1.9: `g(V) log^{1+τ}(2+V)`. -/
noncomputable def filterFn (g : ℝ → ℝ) (τ : ℝ) (V : ℕ) : ℝ :=
  g V * Real.log (2 + V) ^ (1 + τ)

/-- **Definition 1.9** (`def:filtered-banach-intro`) for `A ⊆ B`: the liminf of
`|A ∩ R| / |B ∩ R|` over rectangles with `|R ∩ B| / (g(Vol R) log^{1+τ}(2+Vol R)) → ∞`, empty
infimum `1`. Applied to an output set as `filtered g τ (O ∩ K) K`. -/
noncomputable def filtered {d : ℕ} (g : ℝ → ℝ) (τ : ℝ) (A B : Set (Pt d)) : ℝ :=
  deltaH (filterFn g τ) A B

/-- `δ_h` as an extended-real density notion (for `Guarantees`, `bG`, `bOpt`). -/
noncomputable def dH {d : ℕ} (h : ℕ → ℝ) (O L : Set (Pt d)) : EReal := ((deltaH h O L : ℝ) : EReal)

namespace BasicAux

/-- A rectangle is finite. -/
theorem rect_pts_finite {d : ℕ} (R : Rect d) : R.pts.Finite := Set.finite_Icc _ _

/-- A rectangle has at least one lattice point. -/
theorem rect_vol_pos {d : ℕ} (R : Rect d) : 1 ≤ R.vol := by
  unfold Rect.vol
  have : 0 < R.pts.ncard :=
    (Set.ncard_pos (rect_pts_finite R)).2 ⟨R.lo, Set.left_mem_Icc.2 R.le⟩
  omega

/-- Each ratio `|O ∩ L ∩ R| / m_L(R)` lies in `[0,1]`. Division is total: when
`m_L(R) = 0`, the numerator is also zero and the ratio is `0`. -/
theorem ratio_mem {d : ℕ} (O L : Set (Pt d)) (R : Rect d) :
    ((O ∩ L ∩ R.pts).ncard : ℝ) / mass L R ∈ Icc (0 : ℝ) 1 := by
  refine ⟨by positivity, div_le_one_of_le₀ ?_ (by positivity)⟩
  unfold mass
  have hsub : O ∩ L ∩ R.pts ⊆ L ∩ R.pts := fun x hx => ⟨hx.1.2, hx.2⟩
  exact_mod_cast Set.ncard_le_ncard hsub ((rect_pts_finite R).inter_of_right L)

/-- The level-`s` tests of `testInf`. -/
def tests {d : ℕ} (h : ℕ → ℝ) (O L : Set (Pt d)) (s : ℝ) : Set ℝ :=
  {r : ℝ | ∃ R : Rect d, s * h R.vol ≤ mass L R ∧
                    r = ((O ∩ L ∩ R.pts).ncard : ℝ) / mass L R}

theorem testInf_eq {d : ℕ} (h : ℕ → ℝ) (O L : Set (Pt d)) (s : ℝ) :
    testInf h O L s = if (tests h O L s).Nonempty then sInf (tests h O L s) else 1 := rfl

theorem tests_bdd {d : ℕ} (h : ℕ → ℝ) (O L : Set (Pt d)) (s : ℝ) :
    BddBelow (tests h O L s) := ⟨0, by rintro _ ⟨R, -, rfl⟩; exact (ratio_mem O L R).1⟩

theorem testInf_mem {d : ℕ} (h : ℕ → ℝ) (O L : Set (Pt d)) (s : ℝ) :
    testInf h O L s ∈ Icc (0 : ℝ) 1 := by
  rw [testInf_eq]
  split_ifs with hne
  · obtain ⟨_, R, hR, rfl⟩ := hne
    refine ⟨le_csInf ⟨_, R, hR, rfl⟩ ?_, (csInf_le (tests_bdd h O L s) ⟨R, hR, rfl⟩).trans
      (ratio_mem O L R).2⟩
    rintro _ ⟨R', -, rfl⟩
    exact (ratio_mem O L R').1
  · exact ⟨zero_le_one, le_rfl⟩

theorem testInf_mono {d : ℕ} (h : ℕ → ℝ) (hpos : ∀ n, 1 ≤ n → 0 < h n) (O L : Set (Pt d)) :
    Monotone (testInf h O L) := by
  intro s t hst
  have hsub : tests h O L t ⊆ tests h O L s := by
    rintro _ ⟨R, hR, rfl⟩
    exact ⟨R, le_trans (mul_le_mul_of_nonneg_right hst (hpos _ (rect_vol_pos R)).le) hR, rfl⟩
  by_cases ht : (tests h O L t).Nonempty
  · rw [testInf_eq, testInf_eq, ite_eq_left ht, ite_eq_left (ht.mono hsub)]
    exact csInf_le_csInf (tests_bdd h O L s) ht hsub
  · rw [testInf_eq h O L t, ite_eq_right ht]
    exact (testInf_mem h O L s).2

end BasicAux

/-- Junk-value safeguard for `δ_h`: for a threshold positive on `ℕ_{≥1}`, the level-`λ` infima
converge, `deltaH` is their limit, and `deltaH` lies in `[0,1]`. -/
theorem deltaH_tendsto {d : ℕ} (h : ℕ → ℝ) (hpos : ∀ n, 1 ≤ n → 0 < h n) (O L : Set (Pt d)) :
    Tendsto (testInf h O L) atTop (nhds (deltaH h O L)) ∧ deltaH h O L ∈ Icc (0 : ℝ) 1 := by
  have hmono := BasicAux.testInf_mono h hpos O L
  have hbdd : BddAbove (range (testInf h O L)) :=
    ⟨1, by rintro _ ⟨s, rfl⟩; exact (BasicAux.testInf_mem h O L s).2⟩
  have ht := tendsto_atTop_ciSup hmono hbdd
  have heq : deltaH h O L = ⨆ s, testInf h O L s := ht.limUnder_eq
  rw [heq]
  refine ⟨ht, le_ciSup_of_le hbdd 0 (BasicAux.testInf_mem h O L 0).1,
    ciSup_le fun s => (BasicAux.testInf_mem h O L s).2⟩

namespace BasicAux

/-- The level-`n` infima of `d_banach` are nondecreasing in `n`. -/
theorem banach_level_mono {d : ℕ} (A B : Set (Pt d)) :
    Monotone (fun n : ℕ => ⨅ (R : Rect d) (_ : n ≤ mass B R),
      ((((A ∩ R.pts).ncard : ℝ) / mass B R : ℝ) : EReal)) := by
  intro n m hnm
  exact iInf_mono fun R => iInf_mono' fun h => ⟨le_trans hnm h, le_rfl⟩

/-- `banach_tendsto` without the hypothesis `B.Infinite` (the corresponding theorem retains it). -/
theorem banach_tendsto_aux {d : ℕ} (A B : Set (Pt d)) :
    Tendsto (fun n : ℕ => ⨅ (R : Rect d) (_ : n ≤ mass B R),
      ((((A ∩ R.pts).ncard : ℝ) / mass B R : ℝ) : EReal)) atTop (nhds (banach A B)) :=
  tendsto_atTop_iSup (banach_level_mono A B)

/-- An infinite set has rectangles of arbitrarily large mass. -/
theorem exists_rect_mass_ge {d : ℕ} (B : Set (Pt d)) (hB : B.Infinite) (n : ℕ) :
    ∃ R : Rect d, n ≤ mass B R := by
  obtain ⟨T, hTB, hTc⟩ := hB.exists_subset_card_eq (n + 1)
  have hT : T.Nonempty := by rw [← Finset.card_pos, hTc]; omega
  refine ⟨Rect.mk (T.inf' hT id) (T.sup' hT id) ((Finset.inf'_le id hT.choose_spec).trans (Finset.le_sup' id hT.choose_spec)), ?_⟩
  have hsub : (T : Set (Pt d)) ⊆ B ∩ (Rect.mk (T.inf' hT id) (T.sup' hT id)
      ((Finset.inf'_le id hT.choose_spec).trans (Finset.le_sup' id hT.choose_spec))).pts := fun x hx =>
    ⟨hTB hx, Finset.inf'_le id hx, Finset.le_sup' id hx⟩
  have := Set.ncard_le_ncard hsub ((Set.finite_Icc _ _).inter_of_right B)
  rw [Set.ncard_coe_finset, hTc] at this
  unfold mass; omega

end BasicAux

/-- `d_banach` is the limit of its level-`n` infima (for infinite `B`, each infimum is over a
nonempty set). -/
theorem banach_tendsto {d : ℕ} (A B : Set (Pt d)) (hB : B.Infinite) :
    Tendsto (fun n : ℕ => ⨅ (R : Rect d) (_ : n ≤ mass B R),
      ((((A ∩ R.pts).ncard : ℝ) / mass B R : ℝ) : EReal)) atTop (nhds (banach A B)) := by
  -- The limit exists for every `B`; this formulation also takes the hypothesis `hB`.
  have _ := hB
  exact BasicAux.banach_tendsto_aux A B

namespace BasicAux

/-- Lower bound of the level-`n` infimum of `d_banach` by the level-`n` infimum of `δ₁`. -/
theorem banach_level_ge {d : ℕ} (A B : Set (Pt d)) (n : ℕ) :
    ((testInf (fun _ => (1 : ℝ)) A B n : ℝ) : EReal) ≤ ⨅ (R : Rect d) (_ : n ≤ mass B R),
      ((((A ∩ R.pts).ncard : ℝ) / mass B R : ℝ) : EReal) := by
  refine le_iInf₂ fun R hR => EReal.coe_le_coe_iff.2 ?_
  have hmem : ((A ∩ B ∩ R.pts).ncard : ℝ) / mass B R ∈ tests (fun _ => (1 : ℝ)) A B n :=
    ⟨R, by simpa using (Nat.cast_le (α := ℝ)).2 hR, rfl⟩
  rw [testInf_eq, ite_eq_left ⟨_, hmem⟩]
  refine (csInf_le (tests_bdd _ A B _) hmem).trans
    (div_le_div_of_nonneg_right ?_ (by positivity))
  have hsub : A ∩ B ∩ R.pts ⊆ A ∩ R.pts := fun x hx => ⟨hx.1.1, hx.2⟩
  exact_mod_cast Set.ncard_le_ncard hsub ((rect_pts_finite R).inter_of_right A)

/-- Upper bound of the level-`n` infimum of `d_banach` by the level-`n` infimum of `δ₁`, up to
`(|A \ B| + 1)/n`. -/
theorem banach_level_le {d : ℕ} (A B : Set (Pt d)) (hB : B.Infinite) (hfin : (A \ B).Finite)
    (n : ℕ) (hn : 1 ≤ n) :
    (⨅ (R : Rect d) (_ : n ≤ mass B R), ((((A ∩ R.pts).ncard : ℝ) / mass B R : ℝ) : EReal)) ≤
      ((testInf (fun _ => (1 : ℝ)) A B n + (((A \ B).ncard : ℝ) + 1) / n : ℝ) : EReal) := by
  obtain ⟨R₀, hR₀⟩ := exists_rect_mass_ge B hB n
  have hne : (tests (fun _ => (1 : ℝ)) A B n).Nonempty :=
    ⟨_, R₀, by simpa using (Nat.cast_le (α := ℝ)).2 hR₀, rfl⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨_, ⟨R, hR, rfl⟩, hlt⟩ := Real.lt_sInf_add_pos hne (one_div_pos.2 hnpos)
  have hR' : n ≤ mass B R := by
    have : (n : ℝ) ≤ mass B R := by simpa using hR
    exact_mod_cast this
  have hm : (n : ℝ) ≤ mass B R := by exact_mod_cast hR'
  have hmpos : (0 : ℝ) < mass B R := lt_of_lt_of_le hnpos hm
  refine (iInf₂_le R hR').trans (EReal.coe_le_coe_iff.2 ?_)
  rw [testInf_eq, ite_eq_left hne]
  have hcount : ((A ∩ R.pts).ncard : ℝ) ≤ (A ∩ B ∩ R.pts).ncard + (A \ B).ncard := by
    have hsub : A ∩ R.pts ⊆ (A ∩ B ∩ R.pts) ∪ (A \ B) := by
      intro x hx
      by_cases hxB : x ∈ B
      · exact Or.inl ⟨⟨hx.1, hxB⟩, hx.2⟩
      · exact Or.inr ⟨hx.1, hxB⟩
    have h1 := Set.ncard_le_ncard hsub
      (((rect_pts_finite R).inter_of_right _).union hfin)
    have h2 := Set.ncard_union_le (A ∩ B ∩ R.pts) (A \ B)
    exact_mod_cast h1.trans h2
  have hc0 : (0 : ℝ) ≤ (A \ B).ncard := by positivity
  calc ((A ∩ R.pts).ncard : ℝ) / mass B R
      ≤ ((A ∩ B ∩ R.pts).ncard + (A \ B).ncard) / mass B R :=
        div_le_div_of_nonneg_right hcount hmpos.le
    _ = ((A ∩ B ∩ R.pts).ncard : ℝ) / mass B R + (A \ B).ncard / mass B R := add_div _ _ _
    _ ≤ ((A ∩ B ∩ R.pts).ncard : ℝ) / mass B R + (A \ B).ncard / n := by
        gcongr
    _ ≤ sInf (tests (fun _ => (1 : ℝ)) A B n) + 1 / n + (A \ B).ncard / n := by
        linarith
    _ = sInf (tests (fun _ => (1 : ℝ)) A B n) + (((A \ B).ncard : ℝ) + 1) / n := by
        ring

end BasicAux

/-- Bridge: for infinite `B` and finite `A \ B` (the case of the output set of a generator that is
eventually valid on the full enumeration), `d_banach(A,B)` is finite and equals `δ₁(A,B)`. -/
theorem banach_eq_deltaH_one {d : ℕ} (A B : Set (Pt d)) (hB : B.Infinite) (hfin : (A \ B).Finite) :
    banach A B = dH (fun _ => 1) A B := by
  have hg : Tendsto (fun n : ℕ => testInf (fun _ => (1 : ℝ)) A B n) atTop
      (nhds (deltaH (fun _ => 1) A B)) :=
    (deltaH_tendsto _ (fun _ _ => one_pos) A B).1.comp tendsto_natCast_atTop_atTop
  have hg' : Tendsto (fun n : ℕ => testInf (fun _ => (1 : ℝ)) A B n +
      (((A \ B).ncard : ℝ) + 1) / n) atTop (nhds (deltaH (fun _ => 1) A B)) := by
    simpa using hg.add (tendsto_const_div_atTop_nhds_zero_nat (((A \ B).ncard : ℝ) + 1))
  have hf : Tendsto (fun n : ℕ => ⨅ (R : Rect d) (_ : n ≤ mass B R),
      ((((A ∩ R.pts).ncard : ℝ) / mass B R : ℝ) : EReal)) atTop
      (nhds ((deltaH (fun _ => 1) A B : ℝ) : EReal)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      ((continuous_coe_real_ereal.tendsto _).comp hg)
      ((continuous_coe_real_ereal.tendsto _).comp hg')
      (Eventually.of_forall fun n => BasicAux.banach_level_ge A B n) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact BasicAux.banach_level_le A B hB hfin n hn
  exact tendsto_nhds_unique (BasicAux.banach_tendsto_aux A B) hf

/-! ## Guarantees and optima (extended-real valued: no junk values for `⨅`/`⨆`) -/

/-- `G` guarantees density at least `x` at `K` for the density notion `D`, against every full
enumeration of `K`. -/
def Guarantees {d : ℕ} (D : Set (Pt d) → Set (Pt d) → EReal) (G : Generator (Pt d))
    (K : Set (Pt d)) (x : ℝ) : Prop :=
  ∀ w, IsFullEnumeration w K → (x : EReal) ≤ D (G.outputSet w) K

/-- `b_G(L)`: the largest density `G` guarantees at `L` (worst case over full enumerations). -/
noncomputable def bG {d : ℕ} (D : Set (Pt d) → Set (Pt d) → EReal) (G : Generator (Pt d))
    (L : Set (Pt d)) : EReal :=
  ⨅ w : {w : ℕ → Pt d // IsFullEnumeration w L}, D (G.outputSet w.1) L

/-- `b(L) = sup_G b_G(L)` over generators of the model eventually valid on all of `X`. -/
noncomputable def bOpt {d : ℕ} (D : Set (Pt d) → Set (Pt d) → EReal) (X : Set (Set (Pt d)))
    (L : Set (Pt d)) : EReal :=
  ⨆ G : ValidGen X, bG D G.1 L

/-- The conclusions of the separation theorem for one density notion `D`, with `X`, `K₀`,
`G₀`, `G₁` fixed beforehand. -/
def SeparatesWith {d : ℕ} (D : Set (Pt d) → Set (Pt d) → EReal) (X : Set (Set (Pt d)))
    (K₀ : Set (Pt d)) (G₀ G₁ : Generator (Pt d)) : Prop :=
  Guarantees D G₀ K₀ (1 / 4) ∧
  (∀ K ∈ X, K ≠ K₀ → Guarantees D G₁ K (1 / 2)) ∧
  (∀ G ∈ ValidGen X, ∀ x y : ℝ, Guarantees D G K₀ x →
      (∀ K ∈ X, K ≠ K₀ → Guarantees D G K y) → x + y ≤ 1 / 2) ∧
  bOpt D X K₀ = 1 / 4 ∧ (∀ K ∈ X, K ≠ K₀ → bOpt D X K = 1 / 2)


/-- The threshold of §8: `h(V) = g(V) log(2+V)`, `g : [1,∞) → [1,∞)` nondecreasing. -/
noncomputable def hLog (g : ℝ → ℝ) (V : ℕ) : ℝ := g V * Real.log (2 + V)

/-- **Definition 1.14** (unlabelled): `α` is achievable for `δ_h`: one generator of the model,
eventually valid on all of `X`, guarantees `δ_h(O,K) ≥ α(K)` on every full enumeration of
every `K ∈ X`. -/
def Achievable {d : ℕ} (h : ℕ → ℝ) (X : Set (Set (Pt d))) (α : Set (Pt d) → ℝ) : Prop :=
  ∃ G ∈ ValidGen X, ∀ K ∈ X, Guarantees (dH h) G K (α K)


/-- `K` is nonvacuous for `h`: `sup_R m_K(R) / h(V(R)) = ∞`. -/
def Nonvacuous {d : ℕ} (h : ℕ → ℝ) (K : Set (Pt d)) : Prop :=
  ¬ BddAbove (range fun R : Rect d => (mass K R : ℝ) / h R.vol)

/-- `U_{L,F}` as a set of points of the subspace `X` (ported from 1D `evidenceSet`). -/
def evidenceSet {α : Type*} (X : Set (Set α)) (L F : Set α) : Set X := {M | F ⊆ M.1 ∧ M.1 ⊆ L}

/-- **Definition 2.1**: the finite-evidence topology on `X`. 

-/
abbrev evidenceTopology {α : Type*} (X : Set (Set α)) : TopologicalSpace X :=
  TopologicalSpace.generateFrom
    {U | ∃ L ∈ X, ∃ F : Set α, F.Finite ∧ F ⊆ L ∧ U = evidenceSet X L F}

/-- **Definition 2.1**: the Cantor–Bendixson derivatives `X^{(r)}` of the finite-evidence topology. 
-/
def cbDerived {α : Type*} (X : Set (Set α)) : ℕ → Set X
  | 0 => univ
  | r + 1 => {x | x ∈ cbDerived X r ∧
      ¬ ∃ U : Set X, (evidenceTopology X).IsOpen U ∧ U ∩ cbDerived X r = {x}}

/-- **Definition 2.1**: the individual language `K` has finite point rank `r`:
`K ∈ X^{(r)} \ X^{(r+1)}` in the finite-evidence topology. 
-/
def PointRank {α : Type*} (X : Set (Set α)) (K : Set α) (r : ℕ) : Prop :=
  ∃ hK : K ∈ X, (⟨K, hK⟩ : X) ∈ cbDerived X r ∧ (⟨K, hK⟩ : X) ∉ cbDerived X (r + 1)

/-- **Definition 2.1**: the whole family has finite Cantor–Bendixson rank, a different,
stronger property than individual finite point rank; it is not assumed in Theorem 9.2. 
-/
def FiniteCBRank {α : Type*} (X : Set (Set α)) : Prop := ∃ r, cbDerived X r = ∅

/-- `h_d(V) = log^{1+τ}(2+V)`. -/
noncomputable def hTau (τ : ℝ) (V : ℕ) : ℝ := Real.log (2 + V) ^ (1 + τ)


/-- The outputs produced while the inputs `l` are read: `{G (l.take (i+1)) | i < |l|}`. -/
def outsOf {α : Type*} (G : Generator α) (l : List α) : Set α :=
  {y | ∃ i < l.length, G (l.take (i + 1)) = y}


/-- The points used (input or output) during the run on the input list `l`. -/
def usedBy {α : Type*} (G : Generator α) (l : List α) : Set α := {x | x ∈ l} ∪ outsOf G l



end BanachDensityHD
