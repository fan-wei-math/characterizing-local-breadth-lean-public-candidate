import BanachDensityHD.TreeCorrespondence.Occurrence

/-! # The explicit duplicate-child pruning of Theorem 7.7. -/
namespace BanachDensityHD.TreeCorrespondence
open Set CharAux
open scoped Classical

variable {d : ℕ}

/-- Selecting the singleton root language selects the actual root occurrence. -/
theorem select_root (T : DTree d) : sel T [T.root.L] = [T.root] := by
  have hex : ∃ w : Deco d, w.L = T.root.L ∧ sel T [] ++ [w] ∈ T.paths :=
    ⟨T.root, rfl, by simpa only [sel_nil, List.nil_append] using TreesAux.dtree_root_mem T⟩
  have hw : hex.choose = T.root := by
    have ee : sel T [] ++ [hex.choose] = [hex.choose] :=
      congrArg (fun p => p ++ [hex.choose]) (sel_nil T)
    have hp : [hex.choose] ∈ T.paths := ee ▸ hex.choose_spec.2
    exact Option.some.inj (TreesAux.dtree_head T _ hp)
  have hs := sel_snoc T [] T.root.L
  rw [dite_eq_left hex] at hs
  calc
    sel T [T.root.L] = sel T [] ++ [hex.choose] := hs
    _ = [hex.choose] := congrArg (fun p => p ++ [hex.choose]) (sel_nil T)
    _ = [T.root] := congrArg List.singleton hw

/-- Duplicate-child pruning exists as an actual protected subtree, not merely a
selection of terminal labels. Every path is an unchanged path of the original
and there is at most one child per language at each retained occurrence. -/
theorem pruned_tree_exists {X : Set (Set (Pt d))} {h : ℕ → ℝ}
    {q : Set (Pt d) → ℝ} {K : Set (Pt d)} {T : DTree d}
    (hT : IsProtectedTree X h q K T) :
    ∃ S : DTree d, IsProtectedTree X h q K S ∧ S.root = T.root ∧ S.paths ⊆ T.paths ∧
      ∀ (p : List (Deco d)) (v w : Deco d),
        p ++ [v] ∈ S.paths → p ++ [w] ∈ S.paths → v.L = w.L → v = w := by
  let paths : Set (List (Deco d)) := {p | ∃ H, SelGood T H ∧ p = sel T H}
  have hsub : paths ⊆ T.paths := by
    rintro p ⟨H, hg, rfl⟩; exact hg.2.1
  have hroot : [T.root] ∈ paths := by
    refine ⟨[T.root.L], ?_, (select_root T).symm⟩
    refine ⟨by simp, ?_, ?_⟩
    · rw [select_root]; exact TreesAux.dtree_root_mem T
    · rw [select_root]; rfl
  have hpre : ∀ p ∈ paths, ∀ n, 1 ≤ n → p.take n ∈ paths := by
    rintro p ⟨H, hg, rfl⟩ n hn
    exact ⟨H.take n, (selGood_take T hg hn).1, (selGood_take T hg hn).2.symm⟩
  let S : DTree d := .mk paths T.root hroot
    (fun p hp => TreesAux.dtree_head T p (hsub hp)) hpre
    ((TreesAux.dtree_countable T).mono hsub)
  have hS : IsProtectedTree X h q K S := by
    refine ⟨hT.1, ?_, ?_, ?_, ?_⟩
    · intro p hp; exact hT.2.1 p (hsub hp)
    · intro p v w hp; exact hT.2.2.1 p v w (hsub hp)
    · rintro p ⟨H, hg, rfl⟩ hp M hM hPM hML
      obtain ⟨w, hw, hwp⟩ := hT.2.2.2.1 _ hg.2.1 hp M hM hPM hML
      have hex : ∃ w : Deco d, w.L = M ∧ sel T H ++ [w] ∈ T.paths := ⟨w, hw, hwp⟩
      have hs : sel T (H ++ [M]) = sel T H ++ [hex.choose] := by
        rw [sel_snoc, dite_eq_left hex]
      refine ⟨hex.choose, hex.choose_spec.1, H ++ [M], ?_, hs.symm⟩
      refine ⟨by simp, hs ▸ hex.choose_spec.2, ?_⟩
      rw [hs, List.map_append, hg.2.2]
      simp only [List.map_singleton, hex.choose_spec.1]
    · intro p hp; exact hT.2.2.2.2 p (hsub hp)
  refine ⟨S, hS, rfl, hsub, ?_⟩
  rintro p v w ⟨H, hH, eH⟩ ⟨J, hJ, eJ⟩ hvw
  have hHv : H = p.map Deco.L ++ [v.L] := by
    rw [← hH.2.2, ← eH, List.map_append, List.map_singleton]
  have hJw : J = p.map Deco.L ++ [w.L] := by
    rw [← hJ.2.2, ← eJ, List.map_append, List.map_singleton]
  have hHJ : H = J := by rw [hHv, hJw, hvw]
  have hep : p ++ [v] = p ++ [w] := by rw [eH, eJ, hHJ]
  simpa using hep
end BanachDensityHD.TreeCorrespondence
