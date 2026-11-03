import BanachDensity1D.Nov1.Profile.Trees

/-! # Every terminal obstruction history is one scheduled requirement. -/

namespace BanachDensity1D.ProfileAux
open Set

lemma path_requirement {m : ℕ → ℕ} (hm : ∀ s, 0 < m s) (A : ℕ → Atom)
    (q : Cut) (s : ℕ) {H : List (Set ℤ)}
    (hH : H ∈ (cutTree A (lowerCut q (s + 1)) (lowerCut_nonneg q (s + 1))
      (m s - 1) q (lowerCut_lt q (s + 1))).paths) :
    ∃ R : Requirement m hm, R.s = s ∧ R.root = q ∧
      H = List.ofFn (fun r => language A (R.cuts r)) := by
  obtain ⟨C, hlen, hhead, hpair, hbounds, hH⟩ := cutTree_path A _ _ _ _ _ hH
  have hlen' : C.length = m s := by have := hm s; omega
  let cuts : Fin (m s) → Cut := fun r => C.get ⟨r.val, by omega⟩
  have hroot : cuts ⟨0, hm s⟩ = q := by
    cases C with
    | nil => simp at hhead
    | cons p C =>
      have hp : p = q := by simpa using hhead
      simpa [cuts] using hp
  have hanti : StrictAnti cuts := by
    intro r t hrt
    exact hpair.rel_get_of_lt (show (⟨r.val, by omega⟩ : Fin C.length) < ⟨t.val, by omega⟩ from hrt)
  have habove : ∀ r, lowerCut (cuts ⟨0, hm s⟩) (s + 1) < (cuts r : ℚ) := by
    intro r
    rw [hroot]
    exact (hbounds _ (List.get_mem _ _)).1
  let R : Requirement m hm := ⟨s, cuts, hanti, habove⟩
  refine ⟨R, rfl, hroot, ?_⟩
  have he : List.ofFn cuts = C := by
    apply List.ext_getElem
    · simp [hlen']
    · intro i hi hi'
      simp [cuts]
  rw [hH]
  change C.map (language A) = List.ofFn ((language A) ∘ cuts)
  rw [← List.map_ofFn, he]

end BanachDensity1D.ProfileAux
