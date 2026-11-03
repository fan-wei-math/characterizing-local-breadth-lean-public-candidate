import BanachDensity1D.Nov1.Profile.FilteredRace

/-! # Repeated filter-eligible sealed witnesses on a full adversarial enumeration. -/

namespace BanachDensity1D.ProfileAux
open Set Filter ChainsAux UpperAux
open scoped Topology

/-- Window eligibility is stated using ambient length, not target population. -/
def FilterWindow (h : ℕ → ℝ) (K : Set ℤ) (s : ℕ) (α : ℝ)
    (H : List (Set ℤ)) (a b : ℤ) : Prop :=
  0 < (K ∩ Icc a b).ncard ∧
  (s : ℝ) * h (Icc a b).ncard ≤ (K ∩ Icc a b).ncard ∧
  def_raw_pairing_score H (K ∩ Icc a b) ≤ α

lemma filtered_stage {X : Set (Set ℤ)} (hX : LangClass X) {G : Generator}
    (hGa : G.Admissible) (hG : G.EventuallyValidOn X) {K : Set ℤ} (hK : K ∈ X)
    {h : ℕ → ℝ} {s : ℕ} {α : ℝ} {T : LTree} (hT : def_aot X K T)
    (hfuture : FilteredRace.Future K (FilterWindow h K s α) [] T)
    (x : ℤ) (hx : x ∈ K) (l : List ℤ) :
    ∃ r, (∀ y ∈ r, y ∈ K) ∧ ((∀ y ∈ l, y ∈ K) → ∃ a b : ℤ,
      0 < (K ∩ Icc a b).ncard ∧
      (s : ℝ) * h (Icc a b).ncard ≤ (K ∩ Icc a b).ncard ∧
      K ∩ Icc a b ⊆ used G (l ++ x :: r) ∧
      ((outs G (l ++ x :: r) ∩ (K ∩ Icc a b)).ncard : ℝ) ≤ α * (K ∩ Icc a b).ncard) := by
  by_cases hl : ∀ y ∈ l, y ∈ K
  swap
  · exact ⟨[], by simp, fun h' => absurd h' hl⟩
  have hstart : ∀ y ∈ l ++ [x], y ∈ T.label := by
    intro y hy
    rw [hT.1]
    rcases List.mem_append.mp hy with hy | hy
    · exact hl y hy
    · have := List.mem_singleton.mp hy
      simpa only [this] using hx
  obtain ⟨r, hr, P, hP, a, b, hwin, _, hJu, _, hcount⟩ :=
    FilteredRace.mega hX hGa hG T hT.2 (hT.1 ▸ hK) [] (l ++ [x]) hstart hfuture
  obtain ⟨hpos, hlevel, hscore⟩ := hwin
  refine ⟨r, fun y hy => hT.1 ▸ hr y hy, fun _ => ⟨a, b, hpos, hlevel, ?_, ?_⟩⟩
  · intro y hy
    have hmem : y ∈ K ∩ Icc a b ∩ T.label := ⟨hy, hT.1 ▸ hy.1⟩
    simpa using hJu hmem
  · simp only [List.nil_append] at hscore
    simp only [List.append_assoc, List.singleton_append] at hcount
    have hJpos : (0 : ℝ) < (K ∩ Icc a b).ncard := by exact_mod_cast hpos
    have hp : def_raw_pairing_score P (K ∩ Icc a b) * (K ∩ Icc a b).ncard =
        (layerSum P (K ∩ Icc a b) : ℝ) := by
      rw [score_eq]
      field_simp
    exact hcount.trans (hp.symm.le.trans (mul_le_mul_of_nonneg_right hscore hJpos.le))

/-- The output windows remain permanently sealed by freshness, while the refill
steps ensure a full enumeration of K. This statement retains the full h-filter level. -/
theorem adversarial_filtered_witnesses {X : Set (Set ℤ)} (hX : LangClass X)
    {K : Set ℤ} (hK : K ∈ X) (h : ℕ → ℝ) (α : ℝ)
    (htrees : ∀ s : ℕ, ∃ T : LTree, def_aot X K T ∧
      FilteredRace.Future K (FilterWindow h K s α) [] T)
    (G : Generator) (hGa : G.Admissible) (hG : G.EventuallyValidOn X) :
    ∃ w, IsFullEnumeration w K ∧ ∀ s : ℕ, ∃ a b : ℤ,
      0 < (K ∩ Icc a b).ncard ∧
      (s : ℝ) * h (Icc a b).ncard ≤ (K ∩ Icc a b).ncard ∧
      (((G.outputSet w ∩ K) ∩ Icc a b).ncard : ℝ) ≤ α * (K ∩ Icc a b).ncard := by
  choose T hT hfuture using htrees
  obtain ⟨e, he⟩ := enum_of_mem hX hK
  have heK : ∀ s, e s ∈ K := fun s => he ▸ mem_range_self s
  choose r hrK hr using fun s l => filtered_stage hX hGa hG hK (hT s) (hfuture s) (e s) (heK s) l
  let hs : ℕ → List ℤ := fun s => Nat.rec [] (fun s l => l ++ e s :: r s l) s
  have hs_succ : ∀ s, hs (s + 1) = hs s ++ e s :: r s (hs s) := fun s => rfl
  have hsK : ∀ s, ∀ y ∈ hs s, y ∈ K := by
    intro s
    induction s with
    | zero => simp [hs]
    | succ s ih =>
      intro y hy
      rw [hs_succ] at hy
      rcases List.mem_append.mp hy with hy | hy
      · exact ih y hy
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact heK s
        · exact hrK s _ y hy
  have hlen : ∀ s, s ≤ (hs s).length := by
    intro s
    induction s with
    | zero => simp
    | succ s ih => rw [hs_succ]; simp only [List.length_append, List.length_cons]; omega
  obtain ⟨w, hw, hrange⟩ := limit_exists hs (fun s => ⟨_, hs_succ s⟩) hlen
  refine ⟨w, ?_, ?_⟩
  · ext y
    rw [hrange]
    constructor
    · rintro ⟨k, hk⟩
      exact hsK k y hk
    · intro hy
      rw [← he] at hy
      obtain ⟨s, rfl⟩ := hy
      exact ⟨s + 1, by rw [hs_succ]; simp⟩
  · intro s
    obtain ⟨a, b, hpos, hlevel, hJu, hcount⟩ := hr s (hs s) (hsK s)
    refine ⟨a, b, hpos, hlevel, ?_⟩
    have hJfin : (K ∩ Icc a b).Finite := (finite_Icc a b).subset inter_subset_right
    have hsub : (G.outputSet w ∩ K) ∩ Icc a b ⊆
        outs G (hs s ++ e s :: r s (hs s)) ∩ (K ∩ Icc a b) := by
      rintro y ⟨⟨hyO, hyK⟩, hyI⟩
      exact ⟨sealed hGa (hw (s + 1)) hyO (hJu ⟨hyK, hyI⟩), hyK, hyI⟩
    exact (show (((G.outputSet w ∩ K) ∩ Icc a b).ncard : ℝ) ≤
      (outs G (hs s ++ e s :: r s (hs s)) ∩ (K ∩ Icc a b)).ncard by
      exact_mod_cast ncard_le_ncard hsub (hJfin.subset inter_subset_right)).trans hcount

end BanachDensity1D.ProfileAux
