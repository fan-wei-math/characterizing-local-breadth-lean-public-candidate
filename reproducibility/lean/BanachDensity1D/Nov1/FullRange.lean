import BanachDensity1D.Nov1.Scores
import BanachDensity1D.Nov1.Upper
import BanachDensity1D.Theorems

/-! # Every scalar optimal value in [0,1/2] occurs.

Authority: `Nov 1.tex`, `cor:full-range`. The B.1 family is reused and
relabelled by a common mechanical core; no previously verified proof is changed.
-/

namespace BanachDensity1D.FullRangeAux
open Set Filter ChainsAux PriorZero.Construction
open scoped Topology

lemma family_bK (C : PriorZero.Construction) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    bK (family C ρ) K0 = ρ / 2 := by
  have ht := (bK_tendsto (X := family C ρ) K0_infinite).1
  apply le_antisymm
  · exact le_of_tendsto ht (Eventually.of_forall (bn_upper C h0 h1))
  · have hl : Tendsto (fun n : ℕ => ρ / 2 - 1 / (n : ℝ)) atTop (𝓝 (ρ / 2)) := by
      simpa using tendsto_const_nhds.sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact le_of_tendsto_of_tendsto hl ht
      (eventually_atTop.2 ⟨1, fun n hn => bn_core_lower C h0 h1 (by omega)⟩)

lemma singleton_langClass : LangClass ({K0} : Set (Set ℤ)) := by
  refine ⟨singleton_nonempty _, countable_singleton _, ?_⟩
  intro L hL
  have : L = K0 := mem_singleton_iff.mp hL
  simpa [this] using K0_infinite

lemma singleton_rank : CBrank ({K0} : Set (Set ℤ)) K0 0 := by
  letI := evidenceTopology ({K0} : Set (Set ℤ))
  refine ⟨by simp, by simp [cbDerived], ?_⟩
  intro h
  apply h.2
  refine ⟨univ, isOpen_univ, ?_⟩
  ext x
  simp only [cbDerived, inter_univ, mem_univ, mem_singleton_iff, true_iff]
  apply Subtype.ext
  exact mem_singleton_iff.mp x.property

end FullRangeAux

open Set

/-- Every alpha in [0,1/2] is exactly the structural optimum of an infinite
language in a nonempty countable class: `cor:full-range` in `Nov 1.tex`. -/
theorem cor_full_range {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2) :
    ∃ X : Set (Set ℤ), LangClass X ∧ ∃ K ∈ X, bK X K = α := by
  by_cases hhalf : α = 1 / 2
  · refine ⟨{PriorZero.Construction.K0}, FullRangeAux.singleton_langClass,
      PriorZero.Construction.K0, by simp, ?_⟩
    rw [TheoremsAux.bK_eq_half_of_rank FullRangeAux.singleton_langClass
      FullRangeAux.singleton_rank, hhalf]
  · have hρ0 : 0 ≤ 2 * α := by positivity
    have hρ1 : 2 * α < 1 := by
      have hlt := lt_of_le_of_ne hα1 hhalf
      linarith
    refine ⟨FullRangeAux.family PriorZero.Construction.quadratic (2 * α),
      FullRangeAux.family_langClass _ hρ0 hρ1, PriorZero.Construction.K0,
      FullRangeAux.family_K0 _ hρ0 hρ1, ?_⟩
    rw [FullRangeAux.family_bK _ hρ0 hρ1]
    ring

end BanachDensity1D
