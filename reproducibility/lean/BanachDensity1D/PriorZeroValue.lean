import BanachDensity1D.PriorZeroValue.Scores
import BanachDensity1D.PriorZeroValue.Correspondence

/-!
# Current Appendix B.1: the previous construction has b(K0)=0

Authority: the Oct 31 manuscript, Proposition `prop:prior-zero-value`.
The previous paper supplies the explicitly reconstructed family, not an axiom
about its value. All existing definitions of b_n, b, scores, and admissibility
are used unchanged.
-/

namespace BanachDensity1D.PriorZero.Construction
open Set Filter
open scoped Topology
variable (C : BanachDensity1D.PriorZero.Construction)

lemma points_infinite : C.points.Infinite := by
  apply Set.infinite_range_of_injective
  intro i j hij
  exact C.endpoint_strictMono.injective (Nat.cast_injective hij)

lemma points_subset_language (ell a : ℕ) (hs : List ℕ) :
    C.points ⊆ C.language ell a hs := by
  rintro x ⟨i, rfl⟩
  dsimp only
  exact Or.inl (Or.inr ⟨i, le_rfl, by omega⟩)

lemma K0_infinite : K0.Infinite := by
  have hinj : Function.Injective (fun n : ℕ => (n : ℤ)) := Nat.cast_injective
  apply (Set.infinite_range_of_injective hinj).mono
  rintro x ⟨i, rfl⟩
  change (0 : ℤ) ≤ i
  positivity

/-- This is a nonempty countable family of infinite languages, as required by the
standing hypotheses of the current manuscript. -/
theorem langClass : LangClass C.X0 := by
  refine ⟨⟨K0, C.K0_mem⟩, ?_, ?_⟩
  · let f : ℕ × ℕ × List ℕ → Set ℤ := fun t => C.language t.1 t.2.1 t.2.2
    apply (Set.Countable.union (Set.countable_singleton K0) (Set.countable_range f)).mono
    rintro L (rfl | ⟨ell, a, hs, hhs, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨(ell, a, hs), rfl⟩
  · rintro L (rfl | ⟨ell, a, hs, hhs, rfl⟩)
    · exact K0_infinite
    · exact C.points_infinite.mono (C.points_subset_language ell a hs)

/-- The finite-n assertion in current Proposition `prop:prior-zero-value`.
The proof actually includes n=0; in particular it covers every n≥1. -/
theorem bn_zero (n : ℕ) : bn C.X0 K0 n = 0 := by
  apply le_antisymm _ (ChainsAux.bn_bounds (X := C.X0) K0_infinite n).1
  refine (ciInf_le (ChainsAux.bn_bddBelow (X := C.X0) K0_infinite n)
    ⟨C.obstruction n, C.obstruction_admissible n⟩).trans ?_
  have : Nonempty (C.obstruction n).paths :=
    (ChainsAux.paths_nonempty (C.obstruction n)).to_subtype
  apply ciSup_le
  intro H
  exact le_of_eq (C.obstruction_cn_zero n H.2)

/-- The limiting assertion in current Proposition `prop:prior-zero-value`. -/
theorem bK_zero : bK C.X0 K0 = 0 := by
  have heq : (fun n => bn C.X0 K0 n) = fun _ => (0 : ℝ) := funext C.bn_zero
  change limUnder atTop (fun n => bn C.X0 K0 n) = 0
  rw [heq]
  exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).limUnder_eq

/-- **Proposition B.1** (`prop:prior-zero-value`) in the current Oct 31 manuscript:
the reconstructed earlier family contains K0=N, all its b_n(K0) vanish for n≥1,
and consequently b(K0)=0. The construction data are arbitrary certified choices,
not a hypothesis asserting the desired zero score. -/
theorem prop_prior_zero_value :
    LangClass C.X0 ∧ K0 ∈ C.X0 ∧
      (∀ n : ℕ, 1 ≤ n → bn C.X0 K0 n = 0) ∧ bK C.X0 K0 = 0 :=
  ⟨C.langClass, C.K0_mem, fun n _ => C.bn_zero n, C.bK_zero⟩

/-- A fully explicit, proof-filled instance of the previous interval construction;
thus the proposition's construction hypotheses are jointly satisfiable. -/
theorem quadratic_prior_zero_value :
    LangClass quadratic.X0 ∧ K0 ∈ quadratic.X0 ∧
      (∀ n : ℕ, 1 ≤ n → bn quadratic.X0 K0 n = 0) ∧ bK quadratic.X0 K0 = 0 :=
  quadratic.prop_prior_zero_value

end BanachDensity1D.PriorZero.Construction

namespace BanachDensity1D.PriorZero

/-- Current Proposition B.1 for the previous paper's exact printed language
family. The input records the earlier finite-stage interval choices; increasing
gaps are derived, and the printed offset-zero term is preserved by equality. -/
theorem prop_prior_zero_value (D : PreviousPaperIntervals) :
    LangClass D.toConstruction.printedFamily ∧
    Construction.K0 ∈ D.toConstruction.printedFamily ∧
    (∀ n : ℕ, 1 ≤ n → bn D.toConstruction.printedFamily Construction.K0 n = 0) ∧
    bK D.toConstruction.printedFamily Construction.K0 = 0 := by
  simpa only [Construction.printedFamily_eq] using D.toConstruction.prop_prior_zero_value

end BanachDensity1D.PriorZero
