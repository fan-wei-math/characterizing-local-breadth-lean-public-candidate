import BanachDensityHD.TreeCorrespondence.Basic

namespace BanachDensityHD.TreeCorrespondence
open Set Topology
open scoped Classical

variable {d : ℕ} {X : Set (Set (Pt d))}

/-- A manuscript decoration: values exist ONLY on the neighborhood. Openness is
relative to H_K; each prefix has its own cutoff, and radius belongs to the final
history. No value is identified merely because endpoint languages agree. -/
structure PaperDecoration (X : Set (Set (Pt d))) (h : ℕ → ℝ)
    (q : Set (Pt d) → ℝ) (K : Set (Pt d)) (hK : K ∈ X) where
  carrier : Set (History X)
  component : carrier ⊆ historiesFrom X K
  open_relative : IsOpen (Subtype.val ⁻¹' carrier : Set (historiesFrom X K))
  root_mem : History.single K hK ∈ carrier
  prefixes : ∀ H ∈ carrier, ∀ n, 1 ≤ n →
    ∀ hc : IsChain X (H.val.take n), (⟨H.val.take n, hc⟩ : History X) ∈ carrier
  cutoff : carrier → ℝ
  radius : carrier → ℝ
  bounds : ∀ H, 1 ≤ cutoff H ∧ 0 ≤ radius H
  increasing : ∀ (H Γ : carrier) M, History.IsSnoc H.val Γ.val M → radius H < radius Γ
  feasible : ∀ H : carrier,
    GeomFeasible h (listFn H.val.val H.val.property.1)
      (fun i => q (listFn H.val.val H.val.property.1 i))
      (fun i => cutoff ⟨⟨H.val.val.take (i.val + 1),
        CharAux.isChain_take H.val.property (by omega)⟩,
        prefixes H.val H.property _ (by omega) _⟩) (radius H)

namespace PaperDecoration
variable {h : ℕ → ℝ} {q : Set (Pt d) → ℝ} {K : Set (Pt d)} {hK : K ∈ X}
variable (D : PaperDecoration X h q K hK)

/-- Total list extension used only to match the existing interface. Off-carrier
values impose no condition on the partial manuscript decoration. -/
noncomputable def total (f : D.carrier → ℝ) (fallback : ℝ)
    (l : List (Set (Pt d))) : ℝ :=
  if hl : CharAux.InU X D.carrier l then f ⟨⟨l, hl.1⟩, hl.2⟩ else fallback

@[simp] theorem total_on (f : D.carrier → ℝ) (fallback : ℝ) (H : D.carrier) :
    D.total f fallback H.val.val = f H := by
  have hi : CharAux.InU X D.carrier H.val.val := ⟨H.val.property, H.property⟩
  simp only [total, dite_eq_left hi]
  congr 1

/-- Partial values, root-relative openness, and occurrence-prefix geometry give
exactly the existing globally typed interface. -/
theorem toLean :
    IsQGoodDecoration X h q K hK D.carrier (D.total D.cutoff 1) (D.total D.radius 0) := by
  refine ⟨D.component, (relative_open_iff D.component).1 D.open_relative,
    D.root_mem, D.prefixes, ?_, ?_, ?_⟩
  · intro H hH
    simpa only [D.total_on D.cutoff 1 ⟨H, hH⟩, D.total_on D.radius 0 ⟨H, hH⟩]
      using D.bounds ⟨H, hH⟩
  · intro H hH Γ hΓ M hsn
    simpa only [D.total_on D.radius 0 ⟨H, hH⟩, D.total_on D.radius 0 ⟨Γ, hΓ⟩]
      using D.increasing ⟨H, hH⟩ ⟨Γ, hΓ⟩ M hsn
  · intro H hH
    unfold DecoratedGood
    rw [D.total_on D.radius 0 ⟨H, hH⟩]
    have hs : (fun i : Fin (H.val.length - 1 + 1) =>
        D.total D.cutoff 1 (H.val.take (i.val + 1))) =
        (fun i => D.cutoff ⟨⟨H.val.take (i.val + 1),
          CharAux.isChain_take H.property (by omega)⟩,
          D.prefixes H hH _ (by omega) _⟩) := by
      funext i
      exact D.total_on D.cutoff 1 ⟨⟨H.val.take (i.val + 1),
        CharAux.isChain_take H.property (by omega)⟩, D.prefixes H hH _ (by omega) _⟩
    rw [hs]
    exact D.feasible ⟨H, hH⟩

/-- Restrict any existing Lean decoration to genuine partial functions on U. -/
noncomputable def ofLean {U : Set (History X)} {s a : List (Set (Pt d)) → ℝ}
    (hU : IsQGoodDecoration X h q K hK U s a) : PaperDecoration X h q K hK where
  carrier := U
  component := hU.1
  open_relative := (relative_open_iff hU.1).2 hU.2.1
  root_mem := hU.2.2.1
  prefixes := hU.2.2.2.1
  cutoff H := s H.val.val
  radius H := a H.val.val
  bounds H := hU.2.2.2.2.1 H.val H.property
  increasing H Γ M hs := hU.2.2.2.2.2.1 H.val H.property Γ.val Γ.property M hs
  feasible H := hU.2.2.2.2.2.2 H.val H.property

/-- Finite protection at each whole history, with an explicitly valid snoc. -/
theorem finite_protection (H : History X) (hH : H ∈ D.carrier) :
    ∃ P : Set (Pt d), P.Finite ∧ P ⊆ H.last ∧
      ∀ M (hM : M ∈ X), P ⊆ M → ∀ hlt : M ⊂ H.last,
        HistoriesAux.snoc H M hM hlt ∈ D.carrier := by
  obtain ⟨P, hPf, hPL, he⟩ := (HistoriesAux.isOpen_iff D.carrier).1 D.toLean.2.1 H hH
  exact ⟨P, hPf, hPL, fun M hM hPM hlt =>
    he _ M (HistoriesAux.snoc_isSnoc H M hM hlt) hPM⟩
end PaperDecoration

/-- Two-way existence correspondence for Definition 7.6, without equating
partial functions with arbitrary values outside their domain. -/
theorem paperGoodDecoration_iff {h : ℕ → ℝ} {q : Set (Pt d) → ℝ}
    {K : Set (Pt d)} (hK : K ∈ X) :
    Nonempty (PaperDecoration X h q K hK) ↔
    ∃ U s a, IsQGoodDecoration X h q K hK U s a := by
  constructor
  · rintro ⟨D⟩; exact ⟨_, _, _, D.toLean⟩
  · rintro ⟨U, s, a, hU⟩; exact ⟨PaperDecoration.ofLean hU⟩

end BanachDensityHD.TreeCorrespondence
