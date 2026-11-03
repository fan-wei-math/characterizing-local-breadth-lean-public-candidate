import BanachDensity1D.Nov1.Profile.Atoms

/-! # Whole pairs contribute to the pairing score of every descending history. -/

namespace BanachDensity1D.ProfileAux
open Set

lemma pair_pack (A : ℕ → Atom) (P : Finset ℕ) {E : Set ℤ} (hE : E.Finite)
    (hpair : ∀ n ∈ P, (A n).pair = true) (hsub : ∀ n ∈ P, atomPoints A n ⊆ E) :
    2 * P.card ≤ E.ncard := by
  induction P using Finset.induction_on generalizing E with
  | empty => simp
  | @insert n P hn ih =>
    have hpairn := hpair n (by simp)
    have hsubn := hsub n (by simp)
    have hcard : (atomPoints A n).ncard = 2 := by
      rw [atomPoints_card]
      simp [Atom.size, hpairn]
    have hsubP : ∀ j ∈ P, atomPoints A j ⊆ E \ atomPoints A n := by
      intro j hj x hx
      refine ⟨hsub j (by simp [hj]) hx, ?_⟩
      exact fun hxn => disjoint_left.mp (atomPoints_disjoint A (show j ≠ n by rintro rfl; exact hn hj)) hx hxn
    have hp := ih (hE.sdiff) (fun j hj => hpair j (by simp [hj])) hsubP
    have hsplit := ncard_sdiff_add_ncard_of_subset hsubn hE
    rw [hcard] at hsplit
    rw [Finset.card_insert_of_notMem hn]
    omega

/-- A finite collection of whole pair atoms is never split by the languages of H. -/
lemma pairs_le_layerSum (A : ℕ → Atom) (P : Finset ℕ) {H : List (Set ℤ)}
    (hne : H ≠ []) {J : Set ℤ} (hJ : J.Finite)
    (hpair : ∀ n ∈ P, (A n).pair = true)
    (hsub : ∀ n ∈ P, atomPoints A n ⊆ start H ∩ J)
    (hrespect : ∀ L ∈ H, ∀ n, atomPoints A n ⊆ L ∨ Disjoint (atomPoints A n) L) :
    P.card ≤ ChainsAux.layerSum H J := by
  classical
  induction H generalizing P with
  | nil => contradiction
  | cons L t ih =>
    cases t with
    | nil =>
      have hp := pair_pack A P (hJ.subset inter_subset_right) hpair hsub
      change 2 * P.card ≤ (L ∩ J).ncard at hp
      change P.card ≤ (L ∩ J).ncard / 2
      omega
    | cons M t =>
      let Q := P.filter (fun n => atomPoints A n ⊆ M)
      let D := P \ Q
      have hQP : Q ⊆ P := Finset.filter_subset _ _
      have hDP : D ⊆ P := Finset.sdiff_subset
      have hMsub : ∀ n ∈ Q, atomPoints A n ⊆ start (M :: t) ∩ J := by
        intro n hn x hx
        have hm := (Finset.mem_filter.mp hn).2 hx
        exact ⟨hm, (hsub n (hQP hn) hx).2⟩
      have hDsub : ∀ n ∈ D, atomPoints A n ⊆ (L \ M) ∩ J := by
        intro n hn x hx
        have hp := hsub n (hDP hn) hx
        have hr := hrespect M (by simp) n
        have hnot : ¬ atomPoints A n ⊆ M := by
          intro h
          exact (Finset.mem_sdiff.mp hn).2 (Finset.mem_filter.mpr ⟨hDP hn, h⟩)
        have hd := hr.resolve_left hnot
        exact ⟨⟨hp.1, fun hxm => disjoint_left.mp hd hx hxm⟩, hp.2⟩
      have hDpack := pair_pack A D (hJ.subset inter_subset_right) (fun n hn => hpair n (hDP hn)) hDsub
      have htail := ih (by simp) (P := Q) (fun n hn => hpair n (hQP hn)) hMsub
        (fun N hN n => hrespect N (List.mem_cons_of_mem L hN) n)
      have hsplit : D.card + Q.card = P.card := by
        exact Finset.card_sdiff_add_card_eq_card hQP
      change P.card ≤ ((L \ M) ∩ J).ncard / 2 + ChainsAux.layerSum (M :: t) J
      omega

end BanachDensity1D.ProfileAux
