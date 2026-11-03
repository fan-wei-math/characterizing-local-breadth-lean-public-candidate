import BanachDensityHD.ExactStatements.VertexRealization
import BanachDensityHD.TreeCorrespondence.ProofRoute

namespace BanachDensityHD.TreeCorrespondence
open Set

/-- The reverse realization and the forward unfolding give the full equivalence
for every property of terminal histories, without finite branching or height bounds. -/
theorem all_vertex_obstructions_iff {α : Type} (X : Set (Set α)) (K : Set α)
    (hK : K ∈ X) (Good : List (Set α) → Prop) :
    (∀ (V : Type) [Countable V] (T : VertexObstruction V α),
      T.label T.root = K → T.Admissible X → ∃ P, T.Terminal T.root P ∧ Good P) ↔
    (∀ T : PaperObstruction α, T.label = K → T.admissible X → ∃ P ∈ T.paths, Good P) := by
  constructor
  · intro hv T he ha
    let S := PaperObstruction.Address.vertexTree T
    have hs : S.label S.root = K := by
      simpa [S, PaperObstruction.Address.vertexTree] using he
    obtain ⟨P, hp, hg⟩ := hv (PaperObstruction.Address T) S hs
      (PaperObstruction.Address.admissible (he ▸ hK) ha)
    exact ⟨P, (PaperObstruction.Address.terminal_root T P).1 hp, hg⟩
  · intro hp V _ T he ha
    exact T.transfer_terminal ha (fun S hs hsa => hp S (hs.trans he) hsa)

/-- Corollary 7.8: one global assignment, then all countable well-founded
vertex presentations with their actual terminal occurrences. -/
theorem exact_vertex_obstruction_characterization {d : ℕ} {X : Set (Set (Pt d))}
    {h : ℕ → ℝ} {q : Set (Pt d) → ℝ} {K : Set (Pt d)}
    (hX : X.Countable) (hK : K ∈ X) :
    (∃ (ι : Type) (T : OccurrenceTree ι d), T.Protected X h q K) ↔
      ∃ s a : List (Set (Pt d)) → ℝ,
        (∀ H, IsChain X H → H.headD ∅ = K → 1 ≤ s H ∧ 0 ≤ a H) ∧
        (∀ H M, IsChain X (H ++ [M]) → H ≠ [] → H.headD ∅ = K → a H < a (H ++ [M])) ∧
        ∀ (V : Type) [Countable V] (T : VertexObstruction V (Pt d)),
          T.label T.root = K → T.Admissible X →
            ∃ P, T.Terminal T.root P ∧ ∃ hP : P ≠ [], DecoratedGood h q s a P hP := by
  rw [paper_obstruction_characterization hX hK]
  simp_rw [all_vertex_obstructions_iff X K hK]

end BanachDensityHD.TreeCorrespondence
