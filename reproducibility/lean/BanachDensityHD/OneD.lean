import BanachDensityHD.Endpoint
import BanachDensity1D

/-!
# One-dimensional helpers from the BanachDensity1D library

Kleinberg–Wei, *Characterizing Local Breadth in Language Generation*.
Historical source numbering is retained; current mappings are in the release registry.

-/

namespace BanachDensityHD

open Set Filter
open scoped Classical



/-! Helpers for the one-dimensional sentence of §8.3.1.
They use the verified definitions of `BanachDensity1D` (source commit
`55486776e93d07f71dba4bb629a63c68ec66cb6a`), not copies. -/

namespace OneDAux

open BanachDensity1D BanachDensity1D.ChainsAux

/-- Discrete intermediate values: a function `ℕ → ℕ` starting at `0` and growing by at most `1`
per step takes every value up to `f m` at or before `m`. -/
theorem exists_eq_of_step (f : ℕ → ℕ) (h0 : f 0 = 0) (hstep : ∀ k, f (k + 1) ≤ f k + 1)
    (n : ℕ) : ∀ m, n ≤ f m → ∃ k ≤ m, f k = n := by
  intro m
  induction m with
  | zero => intro h; exact ⟨0, le_rfl, by omega⟩
  | succ m ih =>
    intro h
    by_cases he : f (m + 1) = n
    · exact ⟨m + 1, le_rfl, he⟩
    · obtain ⟨k, hk, hfk⟩ := ih (by have := hstep m; omega)
      exact ⟨k, by omega, hfk⟩

/-- A relative interval with at least `n ≥ 1` points has an initial piece with exactly `n`
points. -/
theorem exists_initial_piece (A : Set ℤ) (a b : ℤ) (n : ℕ) (hn : 1 ≤ n)
    (hN : n ≤ (A ∩ Icc a b).ncard) :
    ∃ c, a - 1 ≤ c ∧ c ≤ b ∧ (A ∩ Icc a c).ncard = n := by
  have hab : a ≤ b := by
    by_contra hab
    rw [Icc_eq_empty (by omega), inter_empty, ncard_empty] at hN
    omega
  set f : ℕ → ℕ := fun k => (A ∩ Icc a (a - 1 + k)).ncard with hf
  have h0 : f 0 = 0 := by
    simp only [hf, Nat.cast_zero, add_zero]
    rw [Icc_eq_empty (by omega), inter_empty, ncard_empty]
  have hstep : ∀ k, f (k + 1) ≤ f k + 1 := by
    intro k
    simp only [hf]
    have hsub : A ∩ Icc a (a - 1 + ((k + 1 : ℕ) : ℤ)) ⊆
        insert (a + k) (A ∩ Icc a (a - 1 + (k : ℤ))) := by
      rintro x ⟨hxA, hx1, hx2⟩
      by_cases hx : x = a + k
      · exact Or.inl hx
      · exact Or.inr ⟨hxA, hx1, by push_cast at hx2; omega⟩
    refine (ncard_le_ncard hsub ((finite_Icc _ _).inter_of_right _ |>.insert _)).trans ?_
    exact ncard_insert_le _ _
  have hm : f (b - a + 1).toNat = (A ∩ Icc a b).ncard := by
    simp only [hf]
    congr 3
    omega
  obtain ⟨k, hk, hfk⟩ := exists_eq_of_step f h0 hstep n _ (hm ▸ hN)
  refine ⟨a - 1 + k, by omega, by omega, hfk⟩

/-- Splitting a relative interval at `c`. -/
theorem split_interval (A : Set ℤ) (a b c : ℤ) (h1 : a - 1 ≤ c) (h2 : c ≤ b) :
    A ∩ Icc a b = (A ∩ Icc a c) ∪ (A ∩ Icc (c + 1) b) ∧
      Disjoint (A ∩ Icc a c) (A ∩ Icc (c + 1) b) := by
  refine ⟨?_, Set.disjoint_left.2 fun x hx hx' => by
    have h3 : x ≤ c := hx.2.2
    have h4 : c + 1 ≤ x := hx'.2.1
    omega⟩
  ext x
  simp only [mem_inter_iff, mem_union, mem_Icc]
  by_cases hxA : x ∈ A
  · simp only [hxA, true_and]; omega
  · simp [hxA]

/-- A helper for sums over lists. -/
theorem sum_map_add_le (l : List (Set ℤ)) (f g h : Set ℤ → ℕ) (hle : ∀ E, f E + g E ≤ h E) :
    (l.map f).sum + (l.map g).sum ≤ (l.map h).sum := by
  induction l with
  | nil => simp
  | cons E t ih => simp only [List.map_cons, List.sum_cons]; have := hle E; omega

/-- The rounded-half numerator is superadditive over disjoint finite pieces. -/
theorem layerSum_union_ge (H : List (Set ℤ)) (J₁ J₂ : Set ℤ) (h₁ : J₁.Finite) (h₂ : J₂.Finite)
    (hd : Disjoint J₁ J₂) : layerSum H J₁ + layerSum H J₂ ≤ layerSum H (J₁ ∪ J₂) := by
  unfold layerSum
  refine sum_map_add_le _ _ _ _ fun E => ?_
  have : (E ∩ (J₁ ∪ J₂)).ncard = (E ∩ J₁).ncard + (E ∩ J₂).ncard := by
    rw [inter_union_distrib_left]
    exact ncard_union_eq (hd.mono inter_subset_right inter_subset_right)
      (h₁.inter_of_right E) (h₂.inter_of_right E)
  rw [this]
  omega

/-- `p(H, J) · |J| = ` layer sum, for nonempty finite `J`. -/
theorem score_mul (H : List (Set ℤ)) (J : Set ℤ) (hJ : 0 < J.ncard) :
    def_raw_pairing_score H J * J.ncard = layerSum H J := by
  rw [score_eq]
  have : (J.ncard : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  field_simp

/-- Mediant: the score of a disjoint union of two nonempty finite pieces is at least the score of
one of the pieces. -/
theorem score_piece_le (H : List (Set ℤ)) (J₁ J₂ : Set ℤ) (h₁ : J₁.Finite) (h₂ : J₂.Finite)
    (hd : Disjoint J₁ J₂) (hp₁ : 0 < J₁.ncard) (hp₂ : 0 < J₂.ncard) :
    def_raw_pairing_score H J₁ ≤ def_raw_pairing_score H (J₁ ∪ J₂) ∨
      def_raw_pairing_score H J₂ ≤ def_raw_pairing_score H (J₁ ∪ J₂) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hc1, hc2⟩ := hcon
  have hN : (J₁ ∪ J₂).ncard = J₁.ncard + J₂.ncard := ncard_union_eq hd h₁ h₂
  have hpos : 0 < (J₁ ∪ J₂).ncard := by omega
  have e := score_mul H (J₁ ∪ J₂) hpos
  have e1 := score_mul H J₁ hp₁
  have e2 := score_mul H J₂ hp₂
  have hs : ((layerSum H J₁ + layerSum H J₂ : ℕ) : ℝ) ≤ layerSum H (J₁ ∪ J₂) := by
    exact_mod_cast layerSum_union_ge H J₁ J₂ h₁ h₂ hd
  have hN' : ((J₁ ∪ J₂).ncard : ℝ) = J₁.ncard + J₂.ncard := by exact_mod_cast hN
  have hq1 : (0 : ℝ) < J₁.ncard := by exact_mod_cast hp₁
  have hq2 : (0 : ℝ) < J₂.ncard := by exact_mod_cast hp₂
  push_cast at hs
  rw [hN'] at e
  have i1 := mul_lt_mul_of_pos_right hc1 hq1
  have i2 := mul_lt_mul_of_pos_right hc2 hq2
  nlinarith

/-- Every relative interval with at least `n ≥ 1` points contains a relative interval with between
`n` and `2n - 1` points and no larger score. -/
theorem exists_short_le (H : List (Set ℤ)) (A : Set ℤ) (n : ℕ) (hn : 1 ≤ n) :
    ∀ N, ∀ a b : ℤ, (A ∩ Icc a b).ncard = N → n ≤ N →
      ∃ a' b' : ℤ, A ∩ Icc a' b' ⊆ A ∩ Icc a b ∧ n ≤ (A ∩ Icc a' b').ncard ∧
        (A ∩ Icc a' b').ncard ≤ 2 * n - 1 ∧
        def_raw_pairing_score H (A ∩ Icc a' b') ≤ def_raw_pairing_score H (A ∩ Icc a b) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro a b hN hnN
    by_cases hsmall : N ≤ 2 * n - 1
    · exact ⟨a, b, subset_rfl, hN ▸ hnN, hN ▸ hsmall, le_rfl⟩
    · obtain ⟨c, hc1, hc2, hcn⟩ := exists_initial_piece A a b n hn (hN ▸ hnN)
      obtain ⟨hU, hD⟩ := split_interval A a b c hc1 hc2
      have hf1 : (A ∩ Icc a c).Finite := (finite_Icc _ _).inter_of_right _
      have hf2 : (A ∩ Icc (c + 1) b).Finite := (finite_Icc _ _).inter_of_right _
      have hcard : (A ∩ Icc (c + 1) b).ncard = N - n := by
        have := ncard_union_eq hD hf1 hf2
        rw [← hU, hN, hcn] at this
        omega
      rcases score_piece_le H _ _ hf1 hf2 hD (by omega) (by omega) with h | h
      · refine ⟨a, c, ?_, by omega, by omega, hU ▸ h⟩
        rw [hU]; exact subset_union_left
      · obtain ⟨a', b', hsub, h1, h2, h3⟩ := ih (N - n) (by omega) (c + 1) b hcard (by omega)
        refine ⟨a', b', hsub.trans (hU ▸ subset_union_right), h1, h2, h3.trans (hU ▸ h)⟩

/-- The finite set of possible values at scale `n`: `k / m` with `n ≤ m ≤ 2n - 1`, `k < 2n`. -/
noncomputable def values (n : ℕ) : Finset ℝ :=
  ((Finset.Icc n (2 * n - 1)) ×ˢ (Finset.range (2 * n))).image
    (fun p : ℕ × ℕ => (1 / (p.1 : ℝ)) * p.2)

/-- The score of a short interval of a chain is one of the `values n`. -/
theorem score_mem_values {H : List (Set ℤ)} (hne : H ≠ []) (hc : H.IsChain (fun L M => M ⊂ L))
    (n : ℕ) (J : Set ℤ) (h1 : n ≤ J.ncard) (h2 : J.ncard ≤ 2 * n - 1) (hn : 1 ≤ n) :
    def_raw_pairing_score H J ∈ values n := by
  have hle := raw_score_le_half hne hc J
  have hpos : (0 : ℝ) < J.ncard := by exact_mod_cast (show 0 < J.ncard by omega)
  have hls : layerSum H J ≤ J.ncard := by
    have e := score_mul H J (by omega)
    have : (layerSum H J : ℝ) ≤ J.ncard := by
      rw [← e]; nlinarith
    exact_mod_cast this
  refine Finset.mem_image.2 ⟨(J.ncard, layerSum H J), ?_, (score_eq H J).symm⟩
  simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
  omega

/-- At scale `n ≥ 1`, every inner infimum of (8) for a chain with infinite start belongs to the
finite numerical set `values n`. -/
theorem cnSeq_mem_values {H : List (Set ℤ)} (hne : H ≠ []) (hc : H.IsChain (fun L M => M ⊂ L))
    (hA : (start H).Infinite) (n : ℕ) (hn : 1 ≤ n) (R : ℕ) : cnSeq H n R ∈ values n := by
  set V : Set ℝ := {v | ∃ J ∈ farIntervals H n R, J.ncard ≤ 2 * n - 1 ∧
    v = def_raw_pairing_score H J}
  have hVsub : V ⊆ values n := by
    rintro _ ⟨J, hJ, hJ2, rfl⟩
    exact score_mem_values hne hc n J hJ.2.1 hJ2 hn
  -- every far interval dominates a short far interval
  have hdom : ∀ J ∈ farIntervals H n R, ∃ v ∈ V, v ≤ def_raw_pairing_score H J := by
    rintro J ⟨⟨a, b, rfl⟩, hJn, hJd⟩
    obtain ⟨a', b', hsub, h1, h2, h3⟩ := exists_short_le H (start H) n hn _ a b rfl hJn
    exact ⟨_, ⟨_, ⟨⟨a', b', rfl⟩, h1, hJd.mono_left hsub⟩, h2, rfl⟩, h3⟩
  obtain ⟨J₀, hJ₀⟩ := farIntervals_nonempty hA n R
  obtain ⟨v₀, hv₀, -⟩ := hdom J₀ hJ₀
  obtain ⟨v, hvV, hvmin⟩ := Set.exists_min_image V id
    ((values n).finite_toSet.subset hVsub) ⟨v₀, hv₀⟩
  have heq : cnSeq H n R = v := by
    have : Nonempty (farIntervals H n R) := ⟨⟨J₀, hJ₀⟩⟩
    apply le_antisymm
    · obtain ⟨J, hJ, -, rfl⟩ := hvV
      exact ciInf_le (cnSeq_bddBelow H n R) ⟨J, hJ⟩
    · refine le_ciInf fun J => ?_
      obtain ⟨w, hw, hwle⟩ := hdom J.1 J.2
      exact (hvmin w hw).trans hwle
  rw [heq]
  exact hVsub hvV

end OneDAux

/-- At a fixed scale `n ≥ 1`, the chain scores `c_n(H)` of all histories take values in one finite
set: every relative interval with at least `n` points splits into consecutive pieces with between
`n` and `2n - 1` points, and the rounded-half numerator is superadditive. -/
theorem cn_finite_range {X : Set (Set ℤ)} (hX : BanachDensity1D.LangClass X) (n : ℕ) (hn : 1 ≤ n) :
    ∃ F : Finset ℝ, ∀ H : BanachDensity1D.History X, BanachDensity1D.cn H.1 n ∈ F := by
  refine ⟨OneDAux.values n, fun H => ?_⟩
  have hA := BanachDensity1D.ChainsAux.start_infinite hX H.2
  have ht := (BanachDensity1D.ChainsAux.cn_tendsto H.2.1 H.2.2.2 hA n).1
  have hcl : IsClosed ((OneDAux.values n : Set ℝ)) := (OneDAux.values n).finite_toSet.isClosed
  exact hcl.mem_of_tendsto ht (Eventually.of_forall fun R =>
    OneDAux.cnSeq_mem_values H.2.1 H.2.2.2 hA n hn R)

/-- §8.3.1, the one-dimensional open-neighborhood equivalence (the pointwise form is
`cor_bn_open_iff_pointwise`): `q < b_n(K)` iff `(K)` has an open
neighbourhood `𝒰 ⊆ 𝓗_K` with `q < inf_{H ∈ 𝒰} c_n(H)`. -/
theorem cor_bn_open_iff {X : Set (Set ℤ)} (hX : BanachDensity1D.LangClass X) {K : Set ℤ}
    (hK : K ∈ X) {n : ℕ} (hn : 1 ≤ n) (q : ℝ) :
    q < BanachDensity1D.bn X K n ↔
      ∃ U : Set (BanachDensity1D.History X), IsOpen U ∧ U ⊆ BanachDensity1D.historiesFrom X K ∧
        BanachDensity1D.History.single K hK ∈ U ∧
        q < ⨅ H : U, BanachDensity1D.cn H.1.1 n := by
  open BanachDensity1D BanachDensity1D.HistoryTopologyAux in
  constructor
  · intro hq
    set q' := (q + bn X K n) / 2 with hq'
    have hq'b : q' < bn X K n := by linarith
    have hint := (cor_safety_interior hX hK hn hq'b (single_mem_historiesFrom hK)).2.1
      (single_safe (hX.infinite K hK) hq'b)
    refine ⟨_, isOpen_interior, fun G hG => (interior_subset hG).1, hint, ?_⟩
    have : Nonempty (interior {G : BanachDensity1D.History X |
        G ∈ BanachDensity1D.historiesFrom X K ∧ q' < cn G.1 n}) :=
      ⟨⟨_, hint⟩⟩
    refine lt_of_lt_of_le (by linarith : q < q') (le_ciInf fun H => ?_)
    exact (interior_subset H.2).2.le
  · rintro ⟨U, hU, hsub, hs, hlt⟩
    rw [thm_topological_bn hX hK hn]
    have hbdd : BddAbove (range fun U : {U : Set (BanachDensity1D.History X) // IsOpen U ∧
        U ⊆ BanachDensity1D.historiesFrom X K ∧
          ∃ hA : K ∈ X, BanachDensity1D.History.single K hA ∈ U} =>
        ⨅ H : U.1, cn H.1.1 n) :=
      ⟨1 / 2, by rintro _ ⟨U, rfl⟩; exact (inner_bounds hX n U).2.2⟩
    exact lt_of_lt_of_le hlt (le_ciSup hbdd ⟨U, hU, hsub, hK, hs⟩)

/-- §8.3.1, the one-dimensional equivalence as the manuscript first stated it (pointwise strict
inequalities); equivalent to `cor_bn_open_iff` because of `cn_finite_range`. -/
theorem cor_bn_open_iff_pointwise {X : Set (Set ℤ)} (hX : BanachDensity1D.LangClass X)
    {K : Set ℤ} (hK : K ∈ X) {n : ℕ} (hn : 1 ≤ n) (q : ℝ) :
    q < BanachDensity1D.bn X K n ↔
      ∃ U : Set (BanachDensity1D.History X), IsOpen U ∧ U ⊆ BanachDensity1D.historiesFrom X K ∧
        BanachDensity1D.History.single K hK ∈ U ∧ ∀ H ∈ U, q < BanachDensity1D.cn H.1 n := by
  open BanachDensity1D BanachDensity1D.HistoryTopologyAux in
  constructor
  · intro hq
    have hint := (cor_safety_interior hX hK hn hq (single_mem_historiesFrom hK)).2.1
      (single_safe (hX.infinite K hK) hq)
    exact ⟨_, isOpen_interior, fun G hG => (interior_subset hG).1, hint,
      fun H hH => (interior_subset hH).2⟩
  · rintro ⟨U, hU, hsub, hs, hpt⟩
    obtain ⟨F, hF⟩ := cn_finite_range hX n hn
    have hfin : (range fun H : U => cn H.1.1 n).Finite :=
      F.finite_toSet.subset (by rintro _ ⟨H, rfl⟩; exact hF H.1)
    obtain ⟨v, ⟨H₀, rfl⟩, hvmin⟩ := Set.exists_min_image _ id hfin ⟨_, ⟨⟨_, hs⟩, rfl⟩⟩
    have : Nonempty U := ⟨⟨_, hs⟩⟩
    refine (cor_bn_open_iff hX hK hn q).2 ⟨U, hU, hsub, hs, ?_⟩
    exact lt_of_lt_of_le (hpt _ H₀.2) (le_ciInf fun H => hvmin _ ⟨H, rfl⟩)


end BanachDensityHD
