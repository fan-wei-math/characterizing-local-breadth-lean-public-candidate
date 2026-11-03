import BanachDensity1D.Nov1.Profile.WordStatistics
import BanachDensity1D.Nov1.Profile.Layers

/-! # Exact pairing scores of scheduled witness histories. -/

namespace BanachDensity1D.ProfileAux
open Set

namespace Requirement
variable {m : ℕ → ℕ} {hm : ∀ s, 0 < m s}

lemma base_pair_sum (α : Cut → ℝ) (R : Requirement m hm)
    (h0 : 0 ≤ α R.root) (h1 : α R.root ≤ 1 / 2) :
    ((List.ofFn (R.baseAtom α)).map (fun B => B.size / 2)).sum = pairs (α R.root) (m R.s) := by
  classical
  have hs (r : Fin (m R.s)) : (R.baseAtom α r).size / 2 =
      if isPair (α R.root) r.val then 1 else 0 := by
    by_cases hr : isPair (α R.root) r.val <;> simp [baseAtom, Atom.size, hr]
  rw [List.map_ofFn, List.sum_ofFn]
  simp_rw [Function.comp_apply, hs]
  rw [← Finset.sum_range (fun r : ℕ => if isPair (α R.root) r then (1 : ℕ) else 0)]
  simpa [Finset.sum_boole] using pairs_count h0 h1 (m R.s)

lemma layerAt_subset_root (R : Requirement m hm) (A : ℕ → Atom) (t : Fin (m R.s)) :
    layerAt (fun r => language A (R.cuts r)) t ⊆ language A R.root := by
  intro x hx
  unfold layerAt at hx
  split_ifs at hx with h
  · exact language_mono A (R.cuts_le_root t) hx.1
  · exact language_mono A (R.cuts_le_root t) hx

end Requirement

namespace Staged
variable {m : ℕ → ℕ} {hm : ∀ s, 0 < m s}

lemma witness_layer_card (α : Cut → ℝ) (f : ℕ → Requirement m hm) (k : ℕ)
    (t : Fin (m (f k).s)) :
    (layerAt (fun r => language (atoms α f) ((f k).cuts r)) t ∩
      (language (atoms α f) (f k).root ∩ witnessWindow α f k)).ncard =
      ((f k).baseAtom α t).size := by
  classical
  let E := layerAt (fun r => language (atoms α f) ((f k).cuts r)) t
  have hsub : E ⊆ language (atoms α f) (f k).root := (f k).layerAt_subset_root _ t
  have he : E ∩ (language (atoms α f) (f k).root ∩ witnessWindow α f k) = E ∩ witnessWindow α f k := by
    ext x
    constructor
    · rintro ⟨hx, _, hw⟩; exact ⟨hx, hw⟩
    · rintro ⟨hx, hw⟩; exact ⟨hx, hsub hx, hw⟩
  change (E ∩ (language (atoms α f) (f k).root ∩ witnessWindow α f k)).ncard = _
  rw [he]
  have hcount := witness_slice_count α f k E ((f k).layerPredicate t)
    (fun n x hx => (f k).atom_layer_membership (atoms α f) t hx)
  change (E ∩ witnessWindow α f k).ncard = _ at hcount
  rw [hcount, weighted_filter, (f k).witness_layer_filter α t]
  simp

lemma witness_layerSum (α : Cut → ℝ) (f : ℕ → Requirement m hm) (k : ℕ)
    (h0 : 0 ≤ α (f k).root) (h1 : α (f k).root ≤ 1 / 2) :
    ChainsAux.layerSum (List.ofFn (fun r => language (atoms α f) ((f k).cuts r)))
      (language (atoms α f) (f k).root ∩ witnessWindow α f k) =
      pairs (α (f k).root) (m (f k).s) := by
  unfold ChainsAux.layerSum
  rw [layers_ofFn, List.map_ofFn, List.sum_ofFn]
  calc
    _ = ∑ t : Fin (m (f k).s), ((f k).baseAtom α t).size / 2 := by
      apply Finset.sum_congr rfl
      intro t _
      simp only [Function.comp_apply, witness_layer_card α f k t]
    _ = _ := by
      simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply] using (f k).base_pair_sum α h0 h1

/-- The actual pairing score is p/(m+p), including the endpoint values alpha=0
and alpha=1/2. Local and stage-ending padding do not enter its numerator. -/
lemma witness_score_upper (α : Cut → ℝ) (f : ℕ → Requirement m hm) (k : ℕ)
    (h0 : 0 ≤ α (f k).root) (h1 : α (f k).root ≤ 1 / 2) :
    def_raw_pairing_score (List.ofFn (fun r => language (atoms α f) ((f k).cuts r)))
      (language (atoms α f) (f k).root ∩ witnessWindow α f k) ≤ α (f k).root := by
  rw [ChainsAux.score_eq, witness_layerSum α f k h0 h1, witnessWindow_mass α f k h0 h1,
    one_div_mul_eq_div]
  exact whole_ratio_le h0 h1 (hm (f k).s)

end Staged
end BanachDensity1D.ProfileAux
