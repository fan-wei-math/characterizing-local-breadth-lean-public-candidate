import BanachDensityHD.TreeCorrespondence.Basic

/-! # The fixed-assignment closure/negation step of Corollary 7.8. -/
namespace BanachDensityHD.TreeCorrespondence
open Set Topology
open scoped Classical

/-- For an arbitrary set of good histories, every obstruction tree hits it iff
it contains an open root neighborhood. No compactness or finite branching is
used; this is exactly the negation of the obstruction/closure lemma. -/
theorem obstruction_hits_iff_neighborhood {d : ℕ}
    {X : Set (Set (Pt d))} {K : Set (Pt d)} (hK : K ∈ X) (Good : Set (History X)) :
    (∀ T : PaperObstruction (Pt d), T.label = K → T.admissible X →
      ∃ P ∈ T.paths, ∃ G ∈ Good, G.val = P) ↔
    ∃ U : Set (History X), IsOpen U ∧ History.single K hK ∈ U ∧ U ⊆ Good := by
  rw [all_obstructions_iff]
  have key :
      (∀ T : LTree (Pt d), def_aot X K T → ∃ P ∈ T.paths, ∃ G ∈ Good, G.val = P) ↔
      History.single K hK ∉ closure Goodᶜ := by
    constructor
    · intro ht hcl
      obtain ⟨T, hT, hbad⟩ := (HistoriesAux.lem_obstruction_closure_gen Goodᶜ
        (History.single K hK)).1 hcl
      have hTK : def_aot X K T := hT
      obtain ⟨P, hp, G, hG, hGP⟩ := ht T hTK
      obtain ⟨B, hB, hBP⟩ := hbad P hp
      obtain ⟨Q, rfl⟩ := HistoriesAux.paths_head hp
      have hBG : B = G := by
        apply Subtype.ext
        calc
          B.val = [K] ++ Q := hBP
          _ = T.label :: Q := by rw [hTK.1]; rfl
          _ = G.val := hGP.symm
      exact hB (hBG ▸ hG)
    · intro hn T hT
      have hn' := hn
      rw [HistoriesAux.lem_obstruction_closure_gen] at hn'
      push Not at hn'
      obtain ⟨P, hp, hbad⟩ := hn' T hT
      have hc := CharAux.aot_paths_chain T hT.2 (hT.1 ▸ hK) P hp
      obtain ⟨Q, rfl⟩ := HistoriesAux.paths_head hp
      let G : History X := ⟨T.label :: Q, hc⟩
      have hG : G ∈ Good := by
        by_contra hg
        apply hbad G hg
        change T.label :: Q = [K] ++ Q
        rw [hT.1]; rfl
      exact ⟨_, hp, G, hG, rfl⟩
  rw [key]
  constructor
  · intro hn
    refine ⟨(closure Goodᶜ)ᶜ, isClosed_closure.isOpen_compl, hn, ?_⟩
    intro H hH
    by_contra hng
    exact hH (subset_closure hng)
  · rintro ⟨U, ho, hr, hUG⟩ hcl
    have hsub : closure Goodᶜ ⊆ Uᶜ := closure_minimal
      (fun H hH hHU => hH (hUG hHU)) ho.isClosed_compl
    exact hsub hcl hr
end BanachDensityHD.TreeCorrespondence
