import BanachDensity1D.Nov1.Profile.StageSurplus
import BanachDensity1D.Nov1.Profile.Counting
import BanachDensity1D.Nov1.Profile.Packing

/-! # From atom surplus to pairing bounds on every integer relative interval.

We discard the two endpoint atoms in their entirety, losing at most four
points. This harmless uniform finite error avoids any endpoint-pair convention;
it does not alter the limiting density or strengthen a theorem hypothesis.
-/

namespace BanachDensity1D.ProfileAux
open Set Filter Finset

lemma language_nonneg (A : ℕ → Atom) (q : Cut) : language A q ⊆ Ici (0 : ℤ) := by
  rintro x ⟨n, hx, _⟩
  exact le_trans (by positivity : (0 : ℤ) ≤ position A n) hx.1

open Classical in
lemma pair_surplus_identity (A : ℕ → Atom) (q : Cut) (c : ℝ) {a b : ℕ} (hab : a ≤ b) :
    let P := (Finset.Ico a b).filter (fun n => (A n).pair = true ∧ (A n).label < q)
    (P.card : ℝ) - c * (language A q ∩ Set.Ico (position A a : ℤ) (position A b : ℤ)).ncard =
      intervalSum (fun n => atomSurplus c q (A n)) a b := by
  dsimp
  rw [language_slice_count A q hab]
  have hterm (n : ℕ) : atomSurplus c q (A n) =
      (if (A n).pair = true ∧ (A n).label < q then (1 : ℝ) else 0) -
      c * (if (A n).label < q then ((A n).size : ℝ) else 0) := by
    cases hp : (A n).pair <;> by_cases hq : (A n).label < q <;> simp [atomSurplus, hp, hq]
  unfold intervalSum
  simp_rw [hterm]
  rw [sum_sub_distrib, ← mul_sum]
  simp only [sum_boole, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]

lemma atom_subset_index_interval (A : ℕ → Atom) {a b n : ℕ} (ha : a ≤ n) (hb : n < b) :
    atomPoints A n ⊆ Set.Ico (position A a : ℤ) (position A b : ℤ) := by
  have hlo : (position A a : ℤ) ≤ position A n := by exact_mod_cast (position_strictMono A).monotone ha
  have hup : (position A (n + 1) : ℤ) ≤ position A b := by
    exact_mod_cast (position_strictMono A).monotone (Nat.succ_le_of_lt hb)
  rintro x ⟨hx0, hx1⟩
  exact ⟨hlo.trans hx0, hx1.trans_le hup⟩

/-- At most four points are lost by removing the endpoint atoms. -/
lemma interval_middle_atoms (A : ℕ → Atom) (q : Cut) {u v : ℤ}
    (hpos : 0 < (language A q ∩ Set.Icc u v).ncard) :
    ∃ i j : ℕ,
      (language A q ∩ Set.Ico (position A (i + 1) : ℤ) (position A j : ℤ) ⊆
        language A q ∩ Set.Icc u v) ∧
      (language A q ∩ Set.Icc u v).ncard ≤
        (language A q ∩ Set.Ico (position A (i + 1) : ℤ) (position A j : ℤ)).ncard + 4 ∧
      (¬ i < j → (language A q ∩ Set.Icc u v).ncard ≤ 4) := by
  obtain ⟨z, hzL, hzu, hzv⟩ := Set.nonempty_of_ncard_ne_zero (Nat.ne_zero_of_lt hpos)
  have hz0 := language_nonneg A q hzL
  have hv0 : 0 ≤ v := hz0.trans hzv
  have hu : max u 0 ≤ v := max_le (hzu.trans hzv) hv0
  obtain ⟨i, hi, _⟩ := atom_partition A (show 0 ≤ max u 0 from le_max_right _ _)
  obtain ⟨j, hj, _⟩ := atom_partition A hv0
  let M := language A q ∩ Set.Ico (position A (i + 1) : ℤ) (position A j : ℤ)
  have hMsub : M ⊆ language A q ∩ Set.Icc u v := by
    rintro x ⟨hxL, hlo, hup⟩
    have hiu := hi.2
    have hjv := hj.1
    have hux := le_max_left u 0
    exact ⟨hxL, by omega, by omega⟩
  have hcov : language A q ∩ Set.Icc u v ⊆ M ∪ (atomPoints A i ∪ atomPoints A j) := by
    rintro x ⟨hxL, hxlo, hxhi⟩
    have hx0 := language_nonneg A q hxL
    have hmx : max u 0 ≤ x := max_le hxlo hx0
    have hix := hi.1
    have hjx := hj.2
    by_cases hfirst : x < (position A (i + 1) : ℤ)
    · exact Or.inr (Or.inl ⟨by have := le_max_left u 0; have := le_max_right u 0; omega, hfirst⟩)
    · by_cases hlast : (position A j : ℤ) ≤ x
      · exact Or.inr (Or.inr ⟨hlast, by omega⟩)
      · exact Or.inl ⟨hxL, by omega, by omega⟩
  have hMfin : M.Finite := (finite_Ico _ _).subset inter_subset_right
  have hifin : (atomPoints A i).Finite := finite_Ico _ _
  have hjfin : (atomPoints A j).Finite := finite_Ico _ _
  have hc := ncard_le_ncard hcov (hMfin.union (hifin.union hjfin))
  have h1 := ncard_union_le M (atomPoints A i ∪ atomPoints A j)
  have h2 := ncard_union_le (atomPoints A i) (atomPoints A j)
  rw [atomPoints_card, atomPoints_card] at h2
  have hisize := (A i).size_bounds.2
  have hjsize := (A j).size_bounds.2
  have hbound : (language A q ∩ Set.Icc u v).ncard ≤ M.ncard + 4 := by omega
  refine ⟨i, j, hMsub, hbound, ?_⟩
  intro hnot
  have hji : j ≤ i + 1 := by omega
  have hp : (position A j : ℤ) ≤ position A (i + 1) := by exact_mod_cast (position_strictMono A).monotone hji
  have he : M = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    rintro x ⟨_, hlo, hup⟩
    omega
  simpa only [he, Set.ncard_empty, Nat.zero_add] using hbound

/-- The uniform lower pairing bound is independent of the length of H. -/
lemma raw_from_atom_surplus (A : ℕ → Atom) (q : Cut) {c D : ℝ}
    (hc : 0 ≤ c) (hD : 0 ≤ D)
    (hsur : ∀ a b : ℕ, a ≤ b → -D ≤ intervalSum (fun n => atomSurplus c q (A n)) a b)
    {H : List (Set ℤ)} (hH : IsChain (Set.range (language A)) H)
    (hstart : start H = language A q) {J : Set ℤ}
    (hJ : IsRelInterval (language A q) J) (hpos : 0 < J.ncard) :
    c - (D + 4 * c) / (J.ncard : ℝ) ≤ def_raw_pairing_score H J := by
  classical
  obtain ⟨u, v, rfl⟩ := hJ
  let J := language A q ∩ Set.Icc u v
  have hJfin : J.Finite := (finite_Icc u v).subset inter_subset_right
  have hp : (0 : ℝ) < J.ncard := by exact_mod_cast hpos
  obtain ⟨i, j, hsub, hcard, hsmall⟩ := interval_middle_atoms A q hpos
  have hnum : c * (J.ncard : ℝ) - (D + 4 * c) ≤ (ChainsAux.layerSum H J : ℝ) := by
    by_cases hij : i < j
    · let P := (Finset.Ico (i + 1) j).filter (fun n => (A n).pair = true ∧ (A n).label < q)
      have hpair : ∀ n ∈ P, (A n).pair = true := fun n hn => (mem_filter.mp hn).2.1
      have hPS : ∀ n ∈ P, atomPoints A n ⊆ start H ∩ J := by
        intro n hn x hx
        have hnI := mem_Ico.mp (mem_filter.mp hn).1
        have hxM : x ∈ language A q ∩ Set.Ico (position A (i + 1) : ℤ) (position A j : ℤ) :=
          ⟨(atom_language_iff A q hx).mpr (mem_filter.mp hn).2.2, atom_subset_index_interval A hnI.1 hnI.2 hx⟩
        rw [hstart]
        exact ⟨hxM.1, hsub hxM⟩
      have hrespect : ∀ L ∈ H, ∀ n, atomPoints A n ⊆ L ∨ Disjoint (atomPoints A n) L := by
        intro L hL n
        obtain ⟨p, rfl⟩ := hH.2.1 L hL
        exact languages_do_not_split A p n
      have hpack := pairs_le_layerSum A P hH.1 hJfin hpair hPS hrespect
      have hsur' := hsur (i + 1) j (by omega)
      rw [← pair_surplus_identity A q c (by omega)] at hsur'
      have hpackR : (P.card : ℝ) ≤ ChainsAux.layerSum H J := by exact_mod_cast hpack
      have hcardR : (J.ncard : ℝ) ≤
          (language A q ∩ Set.Ico (position A (i + 1) : ℤ) (position A j : ℤ)).ncard + 4 := by exact_mod_cast hcard
      have hmul := mul_le_mul_of_nonneg_left hcardR hc
      change -D ≤ (P.card : ℝ) - c * _ at hsur'
      nlinarith
    · have hsmallR : (J.ncard : ℝ) ≤ 4 := by exact_mod_cast hsmall hij
      have hmul := mul_le_mul_of_nonneg_left hsmallR hc
      have hsum0 : (0 : ℝ) ≤ ChainsAux.layerSum H J := Nat.cast_nonneg _
      nlinarith
  change c - (D + 4 * c) / (J.ncard : ℝ) ≤ def_raw_pairing_score H J
  rw [ChainsAux.score_eq, one_div_mul_eq_div]
  apply (le_div_iff₀ hp).mpr
  have he : (c - (D + 4 * c) / (J.ncard : ℝ)) * J.ncard = c * J.ncard - (D + 4 * c) := by field_simp
  rw [he]
  exact hnum

end BanachDensity1D.ProfileAux
