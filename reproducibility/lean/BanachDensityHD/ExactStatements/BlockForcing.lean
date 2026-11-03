import BanachDensityHD.Separation

namespace BanachDensityHD.ExactStatements
open Set

/-- Lemma 6.4 for the distinct initial inputs of the Nov. 1 manuscript.
The continuation remains permitted to repeat inputs, as in its statement.
`CellForced` spells out all three manuscript conclusions. -/
theorem distinct_input_block_forcing {d : ℕ} (hd : 2 ≤ d)
    (G : Generator (Pt d)) (hG : G ∈ ValidGen (family7d d))
    {k ℓ : ℕ} (hk : 1 ≤ k) (hkℓ : k ≤ ℓ) (xs : List (Pt d)) (_hxs : xs.Nodup)
    (hxV : ∀ x ∈ xs, x ∈ emb2 d '' cappedStrip k ℓ)
    (n m : ℕ) (hn : 1 ≤ n) (hnk : n ≤ k) (hm : 1 ≤ m) :
    ∃ ext : List (Pt d), (∀ x ∈ ext, x ∈ emb2 d '' cappedStrip k ℓ) ∧
      ∃ T : ℕ, ∀ i, 1 ≤ i → i ≤ n → ∀ j < m,
        CellForced G (xs ++ ext) i (T + j) :=
  lem_block hd G hG hk hkℓ xs hxV n m hn hnk hm

end BanachDensityHD.ExactStatements
