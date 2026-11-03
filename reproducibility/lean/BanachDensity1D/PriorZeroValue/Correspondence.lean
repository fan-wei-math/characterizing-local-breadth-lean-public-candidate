import BanachDensity1D.PriorZeroValue.Construction

/-! # Explicit correspondence with the previous paper's printed sumsets.

The finite tuple has length d. The last printed finite term starts at zero;
all preceding finite terms start at one. The normalization used by the proof
is proved equal here, including d=0 and d=1.
-/

namespace BanachDensity1D.PriorZero.Construction
open Set
variable (C : BanachDensity1D.PriorZero.Construction)

def sumset (A B : Set ℤ) : Set ℤ := {x | ∃ p ∈ A, ∃ q ∈ B, x = p + q}
def firstPoints (k : ℕ) : Set ℤ := {x | ∃ i < k, x = (C.endpoint i : ℤ)}

/-- P[k] really consists of the first k increasing endpoints, not an arbitrary
finite subset chosen for the score proof. -/
lemma firstPoints_eq_cut (k : ℕ) :
    C.firstPoints k = C.points ∩ Iio (C.endpoint k : ℤ) := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨⟨i, rfl⟩, ?_⟩
    change (C.endpoint i : ℤ) < (C.endpoint k : ℤ)
    exact_mod_cast C.endpoint_strictMono hi
  · rintro ⟨⟨i, rfl⟩, hi⟩
    change (C.endpoint i : ℤ) < (C.endpoint k : ℤ) at hi
    have hi' : C.endpoint i < C.endpoint k := by exact_mod_cast hi
    exact ⟨i, C.endpoint_strictMono.lt_iff_lt.mp hi', rfl⟩

lemma thick_sumset (a : ℕ) : C.thick a = sumset C.points (Icc 0 (a : ℤ)) := by
  ext x
  constructor
  · rintro ⟨i, hlo, hup⟩
    exact ⟨C.endpoint i, ⟨i, rfl⟩, x - C.endpoint i, ⟨by omega, by omega⟩, by omega⟩
  · rintro ⟨p, ⟨i, rfl⟩, q, ⟨hlo, hup⟩, rfl⟩
    dsimp only at *
    exact ⟨i, by omega, by omega⟩

lemma finiteBlock_sumset (k a : ℕ) :
    C.finiteBlock k a = sumset (C.firstPoints k) (Icc 1 (a : ℤ)) := by
  ext x
  constructor
  · rintro ⟨i, hi, hlo, hup⟩
    exact ⟨C.endpoint i, ⟨i, hi, rfl⟩, x - C.endpoint i, ⟨by omega, by omega⟩, by omega⟩
  · rintro ⟨p, ⟨i, hi, rfl⟩, q, ⟨hlo, hup⟩, rfl⟩
    exact ⟨i, hi, by omega, by omega⟩

lemma zeroBlock_sumset (k a : ℕ) :
    sumset (C.firstPoints k) (Icc 0 (a : ℤ)) = C.firstPoints k ∪ C.finiteBlock k a := by
  ext x
  constructor
  · rintro ⟨p, ⟨i, hi, rfl⟩, q, ⟨hlo, hup⟩, rfl⟩
    by_cases hq : q = 0
    · left; exact ⟨i, hi, by omega⟩
    · right; exact ⟨i, hi, by omega, by omega⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, hlo, hup⟩)
    · exact ⟨C.endpoint i, ⟨i, hi, rfl⟩, 0, ⟨le_rfl, by positivity⟩, by omega⟩
    · exact ⟨C.endpoint i, ⟨i, hi, rfl⟩, x - C.endpoint i,
        ⟨by omega, by omega⟩, by omega⟩

def printedExceptions : ℕ → List ℕ → Set ℤ
  | _, [] => ∅
  | a, [h] => sumset (C.firstPoints h) (Icc 0 ((a + 1 : ℕ) : ℤ))
  | a, h :: j :: hs => sumset (C.firstPoints h) (Icc 1 ((a + 1 : ℕ) : ℤ)) ∪
      printedExceptions (a + 1) (j :: hs)

lemma printedExceptions_bounds (a : ℕ) (hs : List ℕ) :
    C.exceptions a hs ⊆ C.printedExceptions a hs ∧
      C.printedExceptions a hs ⊆ C.exceptions a hs ∪ C.points := by
  induction hs generalizing a with
  | nil => simp [exceptions, printedExceptions]
  | cons h hs ih =>
    cases hs with
    | nil =>
      simp only [exceptions, printedExceptions, union_empty, C.zeroBlock_sumset]
      refine ⟨subset_union_right, ?_⟩
      rintro x (hx | hx)
      · obtain ⟨i, hi, rfl⟩ := hx
        exact Or.inr ⟨i, rfl⟩
      · exact Or.inl hx
    | cons j hs =>
      simp only [exceptions, printedExceptions, ← C.finiteBlock_sumset]
      obtain ⟨hf, hb⟩ := ih (a + 1)
      constructor
      · rintro x (hx | hx)
        · exact Or.inl hx
        · exact Or.inr (hf hx)
      · rintro x (hx | hx)
        · exact Or.inl (Or.inl hx)
        · rcases hb hx with hx | hx
          · exact Or.inl (Or.inr hx)
          · exact Or.inr hx

def printedLanguage (ell a : ℕ) (hs : List ℕ) : Set ℤ :=
  {x | 0 ≤ x ∧ x < (ell : ℤ)} ∪ sumset C.points (Icc 0 (a : ℤ)) ∪
    C.printedExceptions a hs

/-- No language was added or lost by normalizing the final offset-zero term. -/
theorem printedLanguage_eq (ell a : ℕ) (hs : List ℕ) :
    C.printedLanguage ell a hs = C.language ell a hs := by
  obtain ⟨hf, hb⟩ := C.printedExceptions_bounds a hs
  ext x
  simp only [printedLanguage, language, ← C.thick_sumset, mem_union]
  constructor
  · rintro (hx | hx)
    · exact Or.inl hx
    · rcases hb hx with hx | hx
      · exact Or.inr hx
      · obtain ⟨i, rfl⟩ := hx
        dsimp only
        exact Or.inl (Or.inr ⟨i, le_rfl, by omega⟩)
  · rintro (hx | hx)
    · exact Or.inl hx
    · exact Or.inr (hf hx)

def printedFamily : Set (Set ℤ) :=
  {L | L = K0 ∨ ∃ ell a hs, Ordered hs ∧ L = C.printedLanguage ell a hs}

theorem printedFamily_eq : C.printedFamily = C.X0 := by
  ext L
  simp only [printedFamily, X0, C.printedLanguage_eq]

end BanachDensity1D.PriorZero.Construction

namespace BanachDensity1D.PriorZero

/-- The earlier paper's finitely blocked interval choices, flattened in endpoint
order. `stageStart s` begins block s; blocks have at least two intervals. Lengths
are nondecreasing globally and strictly increase between successive blocks.
The window bound involving f is irrelevant to Appendix B.1 and is not assumed
as a zero-value claim. -/
structure PreviousPaperIntervals where
  endpoint : ℕ → ℕ
  length : ℕ → ℕ
  stageStart : ℕ → ℕ
  first_stage : stageStart 0 = 0
  stage_size : ∀ s, stageStart s + 2 ≤ stageStart (s + 1)
  length_mono : Monotone length
  stage_growth : ∀ s, length (stageStart s) < length (stageStart (s + 1))
  separated : ∀ i, endpoint i + length i < endpoint (i + 1)

namespace PreviousPaperIntervals

/-- Unbounded lengths are derived from the infinitely many strictly growing
finite stages, rather than assumed as a literature theorem. -/
def toConstruction (D : PreviousPaperIntervals) : Construction where
  endpoint := D.endpoint
  length := D.length
  length_mono := D.length_mono
  length_unbounded := by
    have hg : StrictMono (fun s => D.length (D.stageStart s)) :=
      strictMono_nat_of_lt_succ D.stage_growth
    intro N
    exact ⟨D.stageStart N, hg.le_apply⟩
  separated := D.separated

/-- Successive pairs of the explicit quadratic intervals are legal finite stages. -/
def quadraticStages : PreviousPaperIntervals where
  endpoint := Construction.quadratic.endpoint
  length := Construction.quadratic.length
  stageStart s := 2 * s
  first_stage := rfl
  stage_size := by intro s; omega
  length_mono := Construction.quadratic.length_mono
  stage_growth := by intro s; change 2 * s + 1 < 2 * (s + 1) + 1; omega
  separated := Construction.quadratic.separated

end PreviousPaperIntervals
end BanachDensity1D.PriorZero
