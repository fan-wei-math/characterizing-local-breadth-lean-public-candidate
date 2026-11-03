import BanachDensity1D.PriorZeroValue.Trees

/-! # Remote path traces and zero pairing scores. -/

namespace BanachDensity1D.PriorZero.Construction
open Set Filter
open scoped Topology
variable (C : BanachDensity1D.PriorZero.Construction)

/-- The successive initial-interval traces along one terminal tower path. -/
inductive PrefixTrace (p : ℤ) (J : Set ℤ) : ℕ → List (Set ℤ) → Prop
  | single {L} : L ∩ J = Icc p p → PrefixTrace p J 0 [L]
  | step {a L H} : L ∩ J = Icc p (p + (a + 1 : ℕ)) →
      PrefixTrace p J a H → PrefixTrace p J (a + 1) (L :: H)

lemma PrefixTrace.nonempty {p : ℤ} {J : Set ℤ} {a : ℕ} {H : List (Set ℤ)}
    (h : PrefixTrace p J a H) : H ≠ [] := by cases h <;> simp

lemma PrefixTrace.head {p : ℤ} {J : Set ℤ} {a : ℕ} {H : List (Set ℤ)}
    (h : PrefixTrace p J a H) : start H ∩ J = Icc p (p + a) := by
  cases h with
  | single he => simpa [start] using he
  | step he _ => exact he

lemma diff_trace (L M J : Set ℤ) : (L \ M) ∩ J = (L ∩ J) \ (M ∩ J) := by
  ext x; simp only [mem_inter_iff, Set.mem_sdiff]; tauto

lemma PrefixTrace.layerSum_zero {p : ℤ} {J : Set ℤ} {a : ℕ} {H : List (Set ℤ)}
    (h : PrefixTrace p J a H) : ChainsAux.layerSum H J = 0 := by
  induction h with
  | single he => simp [ChainsAux.layerSum, layers, he, Icc_self]
  | @step a L H he ht ih =>
    cases H with
    | nil => exact False.elim (ht.nonempty rfl)
    | cons M H =>
      have hm : M ∩ J = Icc p (p + a) := ht.head
      have hd : (L \ M) ∩ J = {p + (a + 1 : ℕ)} := by
        rw [diff_trace, he, hm]
        ext x
        simp only [Set.mem_sdiff, mem_Icc, mem_singleton_iff]
        push_cast
        omega
      change ((L \ M) ∩ J).ncard / 2 + ChainsAux.layerSum (M :: H) J = 0
      rw [hd, ih]
      simp

lemma tower_trace (ell a : ℕ) (hs : List ℕ) {H : List (Set ℤ)}
    (hH : H ∈ (C.tower ell a hs).paths) (n : ℕ) (hsize : a + hs.length ≤ n) :
    ∃ B, ∀ r ≥ B, C.Isolated n r →
      PrefixTrace (C.endpoint r : ℤ)
        (Icc (C.endpoint r : ℤ) ((C.endpoint r : ℤ) + n)) a H := by
  induction a generalizing hs H with
  | zero =>
    have heq : H = [C.language ell 0 hs] := hH
    subst H
    refine ⟨ell + bound hs + 1, ?_⟩
    intro r hr hiso
    apply PrefixTrace.single
    simpa using C.language_trace hiso hsize (by omega) (by omega)
  | succ a ih =>
    obtain ⟨k, Q, hQ, rfl⟩ := hH
    obtain ⟨B, hB⟩ := ih (max k (bound hs) :: hs) hQ (by simp; omega)
    refine ⟨B + ell + bound hs + 1, ?_⟩
    intro r hr hiso
    exact PrefixTrace.step (C.language_trace hiso hsize (by omega) (by omega))
      (hB r (by omega) hiso)

lemma K0_trace (p : ℕ) (n : ℕ) :
    K0 ∩ Icc (p : ℤ) ((p : ℤ) + n) = Icc (p : ℤ) ((p : ℤ) + n) := by
  apply inter_eq_right.mpr
  intro x hx
  exact le_trans (by positivity : (0 : ℤ) ≤ p) hx.1

lemma root_layerSum_zero {n r : ℕ} {H : List (Set ℤ)}
    (h : PrefixTrace (C.endpoint r : ℤ)
      (Icc (C.endpoint r : ℤ) ((C.endpoint r : ℤ) + n)) n H) :
    ChainsAux.layerSum (K0 :: H)
      (Icc (C.endpoint r : ℤ) ((C.endpoint r : ℤ) + n)) = 0 := by
  cases H with
  | nil => exact False.elim (h.nonempty rfl)
  | cons M H =>
    have hm := h.head
    have hd : (K0 \ M) ∩ Icc (C.endpoint r : ℤ) ((C.endpoint r : ℤ) + n) = ∅ := by
      rw [diff_trace, K0_trace, show M ∩ _ = _ from hm, sdiff_self]
    change ((K0 \ M) ∩ _).ncard / 2 + ChainsAux.layerSum (M :: H) _ = 0
    rw [hd, h.layerSum_zero]
    simp

lemma window_far (n R r : ℕ) (hr : R < C.endpoint r) {H : List (Set ℤ)} :
    Icc (C.endpoint r : ℤ) ((C.endpoint r : ℤ) + n) ∈ farIntervals (K0 :: H) n R := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨C.endpoint r, (C.endpoint r : ℤ) + n, ?_⟩
    exact (K0_trace _ _).symm
  · rw [Set.ncard_Icc, Int.card_Icc]
    omega
  · apply disjoint_left.mpr
    intro x hx hy
    have hr' : (R : ℤ) < C.endpoint r := by exact_mod_cast hr
    have := hx.1
    have := hy.2
    omega

/-- Every root-to-leaf path has exactly zero pairing score, for the prescribed n. -/
lemma obstruction_cn_zero (n : ℕ) {H : List (Set ℤ)}
    (hH : H ∈ (C.obstruction n).paths) : cn H n = 0 := by
  obtain ⟨ell, Q, hQ, rfl⟩ := hH
  obtain ⟨B, hB⟩ := C.tower_trace ell n [] hQ n (by simp)
  obtain ⟨D, hD⟩ := C.isolated_eventually n
  have hseq : ∀ R, ChainsAux.cnSeq (K0 :: Q) n R = 0 := by
    intro R
    let r := B + D + R + 1
    have ht := hB r (by dsimp [r]; omega) (hD r (by dsimp [r]; omega))
    have hf := C.window_far n R r (lt_of_lt_of_le (by dsimp [r]; omega)
      (C.index_le_endpoint r)) (H := Q)
    have hz : def_raw_pairing_score (K0 :: Q)
        (Icc (C.endpoint r : ℤ) ((C.endpoint r : ℤ) + n)) = 0 := by
      rw [ChainsAux.score_eq, C.root_layerSum_zero ht]
      simp
    apply le_antisymm _ (ChainsAux.cnSeq_nonneg _ _ _)
    exact (ciInf_le (ChainsAux.cnSeq_bddBelow _ _ _) ⟨_, hf⟩).trans_eq hz
  have heq : (fun R => ChainsAux.cnSeq (K0 :: Q) n R) = fun _ => (0 : ℝ) :=
    funext hseq
  change limUnder atTop (fun R => ChainsAux.cnSeq (K0 :: Q) n R) = 0
  rw [heq]
  exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).limUnder_eq

end BanachDensity1D.PriorZero.Construction
