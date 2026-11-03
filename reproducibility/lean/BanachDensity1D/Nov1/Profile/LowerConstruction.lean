import BanachDensity1D.Nov1.Profile.IntegerLower
import BanachDensity1D.Theorems

/-! # All-history atom bounds yield the scalar structural lower bounds and ONE common generator. -/

namespace BanachDensity1D.ProfileAux
open Set Filter ChainsAux
open scoped Topology

lemma cn_lower_uniform (A : ℕ → Atom) (q : Cut) {c D : ℝ}
    (hc : 0 ≤ c) (hD : 0 ≤ D)
    (hsur : ∀ a b : ℕ, a ≤ b → -D ≤ intervalSum (fun n => atomSurplus c q (A n)) a b)
    (hK : (language A q).Infinite) {H : List (Set ℤ)}
    (hH : IsChain (range (language A)) H) (hstart : start H = language A q)
    {n : ℕ} (hn : 0 < n) : c - (D + 4 * c) / (n : ℝ) ≤ cn H n := by
  have hA : (start H).Infinite := hstart ▸ hK
  have ht := (cn_tendsto hH.1 hH.2.2 hA n).1
  have he : 0 ≤ D + 4 * c := by positivity
  have hbound : ∀ R, c - (D + 4 * c) / (n : ℝ) ≤ cnSeq H n R := by
    intro R
    have : Nonempty (farIntervals H n R) := (farIntervals_nonempty hA n R).to_subtype
    apply le_ciInf
    intro J
    have hpos : 0 < J.val.ncard := hn.trans_le J.property.2.1
    have hrel : IsRelInterval (language A q) J.val := by simpa only [hstart] using J.property.1
    have hraw := raw_from_atom_surplus A q hc hD hsur hH hstart hrel hpos
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    have hnm : (n : ℝ) ≤ J.val.ncard := by exact_mod_cast J.property.2.1
    have hfrac := div_le_div_of_nonneg_left he hnreal hnm
    exact (by linarith : c - (D + 4 * c) / (n : ℝ) ≤ c - (D + 4 * c) / (J.val.ncard : ℝ)).trans hraw
  exact ge_of_tendsto ht (Eventually.of_forall hbound)

lemma bn_lower_uniform (A : ℕ → Atom) (q : Cut) {c D : ℝ}
    (hc : 0 ≤ c) (hD : 0 ≤ D)
    (hsur : ∀ a b : ℕ, a ≤ b → -D ≤ intervalSum (fun n => atomSurplus c q (A n)) a b)
    (hK : (language A q).Infinite) {n : ℕ} (hn : 0 < n) :
    c - (D + 4 * c) / (n : ℝ) ≤ bn (range (language A)) (language A q) n := by
  have : Nonempty {T : LTree // def_aot (range (language A)) (language A q) T} :=
    ⟨⟨.leaf _, rfl, trivial⟩⟩
  apply le_ciInf
  intro T
  obtain ⟨H, hH⟩ := paths_nonempty T.val
  have hp := path_isChain (mem_range_self q) T.property hH
  have hroot : T.val.label.Infinite := by rw [T.property.1]; exact hK
  exact (cn_lower_uniform A q hc hD hsur hK hp.1 hp.2 hn).trans
    (le_ciSup (pathSup_bdd T.property.2 hroot n) ⟨H, hH⟩)

lemma bK_lower_uniform (A : ℕ → Atom) (q : Cut) {c D : ℝ}
    (hc : 0 ≤ c) (hD : 0 ≤ D)
    (hsur : ∀ a b : ℕ, a ≤ b → -D ≤ intervalSum (fun n => atomSurplus c q (A n)) a b)
    (hK : (language A q).Infinite) : c ≤ bK (range (language A)) (language A q) := by
  have ht := (bK_tendsto (X := range (language A)) hK).1
  have hl : Tendsto (fun n : ℕ => c - (D + 4 * c) / (n : ℝ)) atTop (𝓝 c) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (D + 4 * c))
  exact le_of_tendsto_of_tendsto hl ht
    (eventually_atTop.2 ⟨1, fun n hn => bn_lower_uniform A q hc hD hsur hK (by omega)⟩)

namespace Staged
variable {m : ℕ → ℕ} {hm : ∀ s, 0 < m s}

/-- The lower b-value is proved uniformly in the complete obstruction history. -/
theorem bK_lower (α : Cut → ℝ) (hα : ∀ q, 0 ≤ α q ∧ α q ≤ 1 / 2)
    (f : ℕ → Requirement m hm) (hf : ∀ R, ∀ B : ℕ, ∃ k ≥ B, f k = R) (i : ℕ) :
    α (cutEnumeration i) ≤ bK (range (language (atoms α f))) (language (atoms α f) (cutEnumeration i)) := by
  have hK := language_infinite α f hf (cutEnumeration i)
  apply le_of_forall_lt_imp_le_of_dense
  intro c hc
  by_cases hc0 : 0 ≤ c
  · obtain ⟨D, hD, hsur⟩ := global_atom_surplus α hα f i hc0 hc
    exact bK_lower_uniform _ _ hc0 hD hsur hK
  · exact (le_of_lt (lt_of_not_ge hc0)).trans (bK_tendsto (X := range (language (atoms α f))) hK).2.1

/-- Reuse the existing 1D characterization to obtain one universally valid
strategy before quantifying over any target or enumeration. -/
theorem common_ordinary_generator (α : Cut → ℝ) (hα : ∀ q, 0 ≤ α q ∧ α q ≤ 1 / 2)
    (f : ℕ → Requirement m hm) (hf : ∀ R, ∀ B : ℕ, ∃ k ≥ B, f k = R) :
    ∃ G : Generator, G.Admissible ∧ G.EventuallyValidOn (range (language (atoms α f))) ∧
      ∀ i : ℕ, ∀ w, IsFullEnumeration w (language (atoms α f) (cutEnumeration i)) →
        α (cutEnumeration i) ≤ outputDensity (G.outputSet w) (language (atoms α f) (cutEnumeration i)) := by
  obtain ⟨G, hGa, hGv, hGd⟩ := thm_oneD_lower_conclusion (family_langClass α f hf)
  refine ⟨G, hGa, hGv, ?_⟩
  intro i w hw
  exact (bK_lower α hα f hf i).trans (hGd _ (mem_range_self _) w hw)

end Staged
end BanachDensity1D.ProfileAux
