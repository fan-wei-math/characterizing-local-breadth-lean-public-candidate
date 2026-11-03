import BanachDensityHD.ExactStatements.PositiveThreshold

namespace BanachDensityHD.ExactStatements
open Set
open scoped Classical

/-- Lemma 7.13 with positive u, and explicitly including the output answering
the final committing input. The new committing prefix is nonempty. -/
theorem commitments_including_final_reply {d : ℕ} (hd : 2 ≤ d)
    {X : Set (Set (Pt d))} (hX : LangClass X) {u : ℝ → ℝ}
    (hu : ∀ x, 1 ≤ x → 0 < u x) (hum : MonotoneOn u (Ici 1))
    (G : Generator (Pt d)) (hG : G ∈ ValidGen X) {L : Set (Pt d)} (hL : L ∈ X)
    {αL q : ℝ} (hach : Guarantees (dH (hLog u)) G L αL)
    (hq : q = 0 ∨ (0 ≤ q ∧ q < αL)) (xs : List (Pt d)) (hxL : ∀ x ∈ xs, x ∈ L) :
    ∃ ext : List (Pt d), ∃ s : ℝ, 1 ≤ s ∧ (xs ++ ext ≠ []) ∧
      (∀ x ∈ ext, x ∈ L) ∧
      ∀ cont : List (Pt d), (∀ x ∈ cont, x ∈ L) →
        (∀ j < cont.length + 1,
          G ((xs ++ ext ++ cont).take ((xs ++ ext).length + j)) ∈ L) ∧
        ∀ R : Rect d, s * hLog u R.vol ≤ mass L R →
          (L ∩ R.pts ⊆ {x | x ∈ xs ++ ext ++ cont} ∪ outsOf G (xs ++ ext ++ cont)) →
          q * (mass L R : ℝ) ≤ ((outsOf G (xs ++ ext ++ cont) ∩ L ∩ R.pts).ncard : ℝ) := by
  obtain ⟨c, g, hc, hc1, hg, hgm, he, hden⟩ := normalization_data u hu hum
  have hach' : Guarantees (dH (hLog g)) G L αL := by
    intro w hw
    simpa only [dH, hden d] using hach w hw
  obtain ⟨ext, s, hs, hext, hcont⟩ := lem_hd_commitments hd hX hg hgm G hG hL hach' hq xs hxL
  obtain ⟨x, hx⟩ := (hX.infinite L hL).nonempty
  refine ⟨ext ++ [x], s / c, (one_le_div hc).2 (hc1.trans hs), by simp, ?_, ?_⟩
  · intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact hext y hy
    · rw [List.mem_singleton.1 hy]; exact hx
  · intro cont hcl
    have hold := hcont ([x] ++ cont) (by
      intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · rw [List.mem_singleton.1 hy]; exact hx
      · exact hcl y hy)
    constructor
    · intro j hj
      have hv := hold.1 j (by simpa using hj)
      simpa only [List.append_assoc, List.length_append, List.length_singleton,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hv
    · intro R hR hocc
      have hel : s * hLog g R.vol = s / c * hLog u R.vol := by rw [he]; ring
      have hocc' : L ∩ R.pts ⊆ {z | z ∈ xs ++ ext ++ ([x] ++ cont)} ∪
          outsOf G (xs ++ ext ++ ([x] ++ cont)) := by
        simpa only [List.append_assoc] using hocc
      simpa only [List.append_assoc] using hold.2 R (hel ▸ hR) hocc'

end BanachDensityHD.ExactStatements
