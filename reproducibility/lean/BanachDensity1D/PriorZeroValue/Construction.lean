import BanachDensity1D.Chains

/-!
# The previous paper's zero-density family

The current target is Proposition `prop:prior-zero-value` of the Oct 31
manuscript. The earlier paper supplies only the interval/end-point construction.
No earlier theorem or perfect-tower fact is assumed as a literature axiom.
-/

namespace BanachDensity1D.PriorZero

open Set Filter

/-- Flattened interval data from the earlier construction: ordered left endpoints,
nondecreasing unbounded interval lengths, and separated consecutive intervals.
The earlier finite-stage conditions imply these properties. A proof-filled concrete
instance is supplied below; the results hold for every legal choice of these data. -/
structure Construction where
  endpoint : ℕ → ℕ
  length : ℕ → ℕ
  length_mono : Monotone length
  length_unbounded : ∀ N, ∃ i, N ≤ length i
  separated : ∀ i, endpoint i + length i < endpoint (i + 1)

namespace Construction

variable (C : Construction)

theorem endpoint_strictMono : StrictMono C.endpoint := by
  apply strictMono_nat_of_lt_succ
  intro i
  have := C.separated i
  omega

theorem index_le_endpoint (i : ℕ) : i ≤ C.endpoint i := by
  exact C.endpoint_strictMono.le_apply

/-- One endpoint's whole width-n block is separated from all other such blocks. -/
def Isolated (n r : ℕ) : Prop :=
  ∀ i, i ≠ r → C.endpoint i + n < C.endpoint r ∨ C.endpoint r + n < C.endpoint i

theorem isolated_eventually (n : ℕ) : ∃ B, ∀ r ≥ B, C.Isolated n r := by
  obtain ⟨B, hB⟩ := C.length_unbounded n
  refine ⟨B + 1, ?_⟩
  intro r hr i hir
  by_cases hi : i < r
  · left
    have hBr : B ≤ r - 1 := by omega
    have hlen : n ≤ C.length (r - 1) := hB.trans (C.length_mono hBr)
    have hsep := C.separated (r - 1)
    have heq : r - 1 + 1 = r := by omega
    rw [heq] at hsep
    have hp : C.endpoint i ≤ C.endpoint (r - 1) :=
      C.endpoint_strictMono.monotone (by omega)
    omega
  · right
    have hBr : B ≤ r := by omega
    have hlen : n ≤ C.length r := hB.trans (C.length_mono hBr)
    have hsep := C.separated r
    have hp : C.endpoint (r + 1) ≤ C.endpoint i :=
      C.endpoint_strictMono.monotone (by omega)
    omega

/-- A concrete permitted choice: stages may group successive pairs of these
intervals; f(k)=(k+1)^2 supplies the earlier paper's window bound. -/
def quadratic : Construction where
  endpoint i := (i + 2) ^ 2
  length i := i + 1
  length_mono := by intro i j hij; dsimp; omega
  length_unbounded := by intro N; exact ⟨N, by omega⟩
  separated := by intro i; nlinarith

/-- N as a subset of Z, in nonnegative coordinates. -/
def K0 : Set ℤ := Ici 0

/-- The endpoint set P, embedded in Z. -/
def points : Set ℤ := range fun i => (C.endpoint i : ℤ)

/-- P+[0,a], written as integer blocks. -/
def thick (a : ℕ) : Set ℤ :=
  {x | ∃ i, (C.endpoint i : ℤ) ≤ x ∧ x ≤ (C.endpoint i : ℤ) + a}

/-- P[k]+[1,a], where P[k] is exactly the first k increasing endpoints. -/
def finiteBlock (k a : ℕ) : Set ℤ :=
  {x | ∃ i < k, (C.endpoint i : ℤ) + 1 ≤ x ∧ x ≤ (C.endpoint i : ℤ) + a}

/-- The finite exceptional terms, indexed by the nonincreasing tuple. Offset-zero
terms in the final printed interval are already contained in the base term P+[0,a]. -/
def exceptions : ℕ → List ℕ → Set ℤ
  | _, [] => ∅
  | a, h :: hs => C.finiteBlock h (a + 1) ∪ exceptions (a + 1) hs

/-- The earlier L_{ell,a,d,h}, with d=length(h); [ell]={0,...,ell-1}.
If the earlier paper's naturals start at 1, this is its translation by -1. -/
def language (ell a : ℕ) (hs : List ℕ) : Set ℤ :=
  {x | 0 ≤ x ∧ x < (ell : ℤ)} ∪ C.thick a ∪ C.exceptions a hs

/-- Largest exceptional-prefix index on a finite tuple. -/
def bound : List ℕ → ℕ
  | [] => 0
  | h :: hs => max h (bound hs)

/-- Exactly the nonincreasing tuples allowed in the previous construction. -/
def Ordered (hs : List ℕ) : Prop := hs.Pairwise (fun i j => j ≤ i)

/-- The previous family, with no additional languages from unordered tuples. -/
def X0 : Set (Set ℤ) :=
  {L | L = K0 ∨ ∃ ell a hs, Ordered hs ∧ L = C.language ell a hs}

theorem K0_mem : K0 ∈ C.X0 := Or.inl rfl

theorem language_mem (ell a : ℕ) {hs : List ℕ} (hhs : Ordered hs) :
    C.language ell a hs ∈ C.X0 := Or.inr ⟨ell, a, hs, hhs, rfl⟩

theorem isolated_index {n r i a : ℕ} (h : C.Isolated n r) (ha : a ≤ n) {x : ℤ}
    (hx : x ∈ Icc (C.endpoint r : ℤ) ((C.endpoint r : ℤ) + n))
    (hi : (C.endpoint i : ℤ) ≤ x ∧ x ≤ (C.endpoint i : ℤ) + a) : i = r := by
  by_contra hir
  rcases h i hir with hl | hr
  · have hl' : (C.endpoint i : ℤ) + n < C.endpoint r := by exact_mod_cast hl
    have ha' : (a : ℤ) ≤ n := by exact_mod_cast ha
    rcases hx with ⟨hx0, hx1⟩
    omega
  · have hr' : (C.endpoint r : ℤ) + n < C.endpoint i := by exact_mod_cast hr
    rcases hx with ⟨hx0, hx1⟩
    omega

theorem exceptions_miss {a n r : ℕ} {hs : List ℕ} (hiso : C.Isolated n r)
    (hsize : a + hs.length ≤ n) (hr : bound hs < r) :
    C.exceptions a hs ∩ Icc (C.endpoint r : ℤ) ((C.endpoint r : ℤ) + n) = ∅ := by
  induction hs generalizing a with
  | nil => simp [exceptions]
  | cons h hs ih =>
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    rcases hx with ⟨hx, hJ⟩
    rcases hx with hx | hx
    · obtain ⟨i, hi, hlo, hup⟩ := hx
      have hwidth : a + 1 ≤ n := by simp only [List.length_cons] at hsize; omega
      have heq := C.isolated_index hiso hwidth hJ ⟨by omega, hup⟩
      have hhr : h < r := lt_of_le_of_lt (le_max_left _ _) hr
      omega
    · have hwidth : (a + 1) + hs.length ≤ n := by
        simp only [List.length_cons] at hsize; omega
      have htail : bound hs < r := lt_of_le_of_lt (le_max_right _ _) hr
      have he := ih hwidth htail
      have : x ∈ C.exceptions (a + 1) hs ∩
          Icc (C.endpoint r : ℤ) ((C.endpoint r : ℤ) + n) := ⟨hx, hJ⟩
      rw [he] at this
      exact this

/-- The exact remote-window identity used in current Appendix B.1. -/
theorem language_trace {ell a n r : ℕ} {hs : List ℕ} (hiso : C.Isolated n r)
    (hsize : a + hs.length ≤ n) (hell : ell ≤ r) (hr : bound hs < r) :
    C.language ell a hs ∩ Icc (C.endpoint r : ℤ) ((C.endpoint r : ℤ) + n) =
      Icc (C.endpoint r : ℤ) ((C.endpoint r : ℤ) + a) := by
  have ha : a ≤ n := by omega
  have hp : ell ≤ C.endpoint r := hell.trans (C.index_le_endpoint r)
  have hp' : (ell : ℤ) ≤ C.endpoint r := by exact_mod_cast hp
  have hexc := C.exceptions_miss hiso hsize hr
  ext x
  constructor
  · rintro ⟨(hx | hx) | hx, hJ⟩
    · rcases hx with ⟨hx0, hxell⟩
      rcases hJ with ⟨hlo, hup⟩
      omega
    · obtain ⟨i, hlo, hup⟩ := hx
      have hi := C.isolated_index hiso ha hJ ⟨hlo, hup⟩
      subst i
      exact ⟨hlo, hup⟩
    · have : x ∈ C.exceptions a hs ∩
          Icc (C.endpoint r : ℤ) ((C.endpoint r : ℤ) + n) := ⟨hx, hJ⟩
      rw [hexc] at this
      exact False.elim this
  · intro hx
    refine ⟨Or.inl (Or.inr ⟨r, hx.1, hx.2⟩), hx.1, ?_⟩
    have ha' : (a : ℤ) ≤ n := by exact_mod_cast ha
    have hxup := hx.2
    omega

end Construction

end BanachDensity1D.PriorZero
