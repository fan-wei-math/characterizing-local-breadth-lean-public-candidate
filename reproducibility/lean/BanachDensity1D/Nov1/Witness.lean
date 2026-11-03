import BanachDensity1D.Nov1.Intervals
import BanachDensity1D.Nov1.Relabel

/-! # Relabelled witness intervals and their exact layer counts. -/

namespace BanachDensity1D.FullRangeAux
open Set Filter ChainsAux PriorZero.Construction

lemma image_interval {f : ℤ → ℤ} (hf : StrictMono f) (L : Set ℤ) (a b : ℤ) :
    (f '' L) ∩ Icc (f a) (f b) = f '' (L ∩ Icc a b) := by
  ext x
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hlo, hup⟩
    exact ⟨y, ⟨hy, hf.le_iff_le.mp hlo, hf.le_iff_le.mp hup⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hlo, hup⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, hf.monotone hlo, hf.monotone hup⟩

lemma lift_interval {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (L : Set ℤ) (a b : ℤ) :
    lift ρ L ∩ Icc (embed ρ a) (embed ρ b) =
      (core ρ ∩ Icc (embed ρ a) (embed ρ b)) ∪ embed ρ '' (L ∩ Icc a b) := by
  rw [lift, union_inter_distrib_right, image_interval (embed_strictMono h0 h1)]

lemma lift_diff {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (L M : Set ℤ) :
    lift ρ L \ lift ρ M = embed ρ '' (L \ M) := by
  ext x
  constructor
  · rintro ⟨hc | ⟨y, hy, rfl⟩, hx⟩
    · exact False.elim (hx (Or.inl hc))
    · exact ⟨y, ⟨hy, fun hm => hx (Or.inr ⟨y, hm, rfl⟩)⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hm⟩, rfl⟩
    refine ⟨Or.inr ⟨y, hy, rfl⟩, ?_⟩
    rintro (hc | ⟨z, hz, heq⟩)
    · exact embed_not_core h0 h1 y hc
    · exact hm (by simpa [(embed_strictMono h0 h1).injective heq] using hz)

lemma core_union_singleton_card {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1)
    (a b : ℤ) (hc : a ≤ b) :
    ((core ρ ∩ Icc (embed ρ a) (embed ρ b)) ∪ {embed ρ a}).ncard =
      (core ρ ∩ Icc (embed ρ a) (embed ρ b)).ncard + 1 := by
  rw [union_comm]
  change (insert (embed ρ a) (core ρ ∩ Icc (embed ρ a) (embed ρ b))).ncard = _
  exact ncard_insert_of_notMem (fun hx => embed_not_core h0 h1 a hx.1)
    ((finite_Icc _ _).subset inter_subset_right)

lemma trace_layerSum {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1)
    {p : ℤ} {n a : ℕ} {H : List (Set ℤ)}
    (h : PrefixTrace p (Icc p (p + n)) a H) :
    layerSum (H.map (lift ρ)) (Icc (embed ρ p) (embed ρ (p + n))) =
      ((core ρ ∩ Icc (embed ρ p) (embed ρ (p + n))).ncard + 1) / 2 := by
  induction h with
  | @single L he =>
    rw [show [L].map (lift ρ) = [lift ρ L] from rfl]
    simp only [layerSum, layers, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [lift_interval h0 h1, he, Icc_self, image_singleton,
      core_union_singleton_card h0 h1 p (p + n) (by omega)]
  | @step a L H he ht ih =>
    cases H with
    | nil => exact False.elim (ht.nonempty rfl)
    | cons M H =>
      have hm : M ∩ Icc p (p + n) = Icc p (p + a) := ht.head
      have hd : (L \ M) ∩ Icc p (p + n) = {p + (a + 1 : ℕ)} := by
        rw [diff_trace, he, hm]
        ext x
        simp only [Set.mem_sdiff, mem_Icc, mem_singleton_iff]
        push_cast
        omega
      change ((lift ρ L \ lift ρ M) ∩ _).ncard / 2 + layerSum ((M :: H).map (lift ρ)) _ = _
      rw [lift_diff h0 h1, image_interval (embed_strictMono h0 h1), hd, image_singleton, ncard_singleton, ih]
      simp

lemma root_trace_layerSum {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1)
    {p : ℕ} {n : ℕ} {H : List (Set ℤ)}
    (h : PrefixTrace (p : ℤ) (Icc (p : ℤ) ((p : ℤ) + n)) n H) :
    layerSum ((K0 :: H).map (lift ρ)) (Icc (embed ρ p) (embed ρ ((p : ℤ) + n))) =
      ((core ρ ∩ Icc (embed ρ p) (embed ρ ((p : ℤ) + n))).ncard + 1) / 2 := by
  cases H with
  | nil => exact False.elim (h.nonempty rfl)
  | cons M H =>
    have hm := h.head
    have hd : (K0 \ M) ∩ Icc (p : ℤ) ((p : ℤ) + n) = ∅ := by
      rw [diff_trace, K0_trace, show M ∩ _ = _ from hm, sdiff_self]
    change ((lift ρ K0 \ lift ρ M) ∩ _).ncard / 2 + layerSum ((M :: H).map (lift ρ)) _ = _
    rw [lift_diff h0 h1, image_interval (embed_strictMono h0 h1), hd, image_empty, ncard_empty,
      trace_layerSum h0 h1 h]
    simp

end BanachDensity1D.FullRangeAux
