import BanachDensityHD.ExactStatements.CopyNormalization
import BanachDensityHD.ExactStatements.CopyOccurrences
import BanachDensityHD.ExactStatements.VertexCharacterization
import BanachDensityHD.ExactStatements.BlockForcing
import BanachDensityHD.ExactStatements.Commitments
import BanachDensityHD.ExactStatements.OnPlayRectangle
import BanachDensityHD.ExactStatements.ProfileInternal
import BanachDensityHD.Oct31Bridges
import BanachDensityHD.ExactStatements.SewingPositive
import BanachDensityHD.ExactStatements.CopyEnumeration

/-! Exact Nov. 1 manuscript exports, retaining ordinary copy occurrences. -/
namespace BanachDensityHD.ExactStatements
open Set

/-- Theorem 7.2: literal dyadic certificates on arbitrary countable occurrence
trees. Equal labels/data on distinct occurrences are not identified in the input.
The kernel bridges certify existence, not a false occurrence isomorphism. -/
theorem exact_profile_occurrences_positive {d : ℕ} (hd : 2 ≤ d)
    {X : Set (Set (Pt d))} (hX : LangClass X) {u : ℝ → ℝ}
    (hu : ∀ x, 1 ≤ x → 0 < u x) (hum : MonotoneOn u (Ici 1))
    (α : Set (Pt d) → ℝ) (hα : ∀ K ∈ X, α K ∈ Icc (0 : ℝ) 1) :
    Achievable (hLog u) X α ↔
      ∀ K ∈ X, ∀ k : ℕ, 1 ≤ k →
        ∃ (ι : Type) (T : CopyOccurrenceTree ι d), T.Protected X (hLog u) (dyadicQuota α) K k := by
  rw [exact_profile_positive_dyadic hd hX hu hum α hα]
  simp_rw [copyOccurrenceTree_iff]
  rfl

end BanachDensityHD.ExactStatements
