import BanachDensityHD.Basic

/-! # Transport of the online model through a bijection of ambient spaces. -/

namespace BanachDensityHD.Nov1
open Set

variable {α β : Type*}

/-- Bijections are applied to the entire input history, including invalid inputs. -/
def transportGenerator (e : α ≃ β) (G : Generator α) : Generator β :=
  fun l => e (G (l.map e.symm))

lemma mapped_inputs (e : α ≃ β) (w : ℕ → β) (t : ℕ) :
    (inputsUpTo w t).map e.symm = inputsUpTo (e.symm ∘ w) t := by
  simp [inputsUpTo, List.map_ofFn, Function.comp_def]

lemma transported_out (e : α ≃ β) (G : Generator α) (w : ℕ → β) (t : ℕ) :
    (transportGenerator e G).out w t = e (G.out (e.symm ∘ w) t) := by
  simp only [Generator.out, transportGenerator, mapped_inputs]

lemma equiv_image_mem (e : α ≃ β) (K : Set α) (x : α) : e x ∈ e '' K ↔ x ∈ K := by
  constructor
  · rintro ⟨y, hy, he⟩
    simpa only [e.injective he] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

lemma enumeration_pullback (e : α ≃ β) {K : Set α} {w : ℕ → β}
    (hw : IsFullEnumeration w (e '' K)) : IsFullEnumeration (e.symm ∘ w) K := by
  change range (e.symm ∘ w) = K
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    have hmem : w t ∈ e '' K := hw ▸ mem_range_self t
    obtain ⟨y, hy, he⟩ := hmem
    simpa only [Function.comp_apply, ← he, e.symm_apply_apply] using hy
  · intro hx
    have hmem : e x ∈ range w := hw.symm ▸ ⟨x, hx, rfl⟩
    obtain ⟨t, ht⟩ := hmem
    exact ⟨t, by simp [Function.comp_def, ht]⟩

lemma transported_fresh (e : α ≃ β) {G : Generator α} (hG : G.Fresh) :
    (transportGenerator e G).Fresh := by
  intro w t
  obtain ⟨hinput, houtput⟩ := hG (e.symm ∘ w) t
  constructor
  · intro i hi he
    apply hinput i hi
    have h := congrArg e.symm he
    simpa only [transported_out, e.symm_apply_apply, Function.comp_apply] using h
  · intro s hs he
    apply houtput s hs
    have h := congrArg e.symm he
    simpa only [transported_out, e.symm_apply_apply] using h

lemma transported_valid (e : α ≃ β) {G : Generator α} {X : Set (Set α)}
    (hG : G.EventuallyValidOn X) :
    (transportGenerator e G).EventuallyValidOn ((fun K => e '' K) '' X) := by
  rintro L ⟨K, hK, rfl⟩ w hw
  have hbad := hG K hK (e.symm ∘ w) (enumeration_pullback e hw)
  change {t | (transportGenerator e G).out w t ∉ e '' K}.Finite
  have he : {t | (transportGenerator e G).out w t ∉ e '' K} =
      {t | G.out (e.symm ∘ w) t ∉ K} := by
    ext t
    simp only [mem_setOf_eq, transported_out, equiv_image_mem]
  rw [he]
  exact hbad

lemma transport_validGen (e : α ≃ β) {G : Generator α} {X : Set (Set α)}
    (hG : G ∈ ValidGen X) : transportGenerator e G ∈ ValidGen ((fun K => e '' K) '' X) :=
  ⟨transported_fresh e hG.1, transported_valid e hG.2⟩

end BanachDensityHD.Nov1
