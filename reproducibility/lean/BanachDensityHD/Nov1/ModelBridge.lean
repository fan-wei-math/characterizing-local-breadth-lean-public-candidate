import BanachDensityHD.Nov1.OrdinaryFiltered
import BanachDensityHD.Oct31Bridges

/-! # Compatibility of the existing 1D and HD online models under ambient bijections. -/

namespace BanachDensityHD.Nov1
open Set

lemma oned_fresh_iff (G : BanachDensity1D.Generator) : G.Admissible ↔ Generator.Fresh G := Iff.rfl
lemma oned_outputSet_eq (G : BanachDensity1D.Generator) (w : ℕ → ℤ) :
    BanachDensity1D.Generator.outputSet G w = Generator.outputSet G w := rfl

lemma oned_valid_to_hd {G : BanachDensity1D.Generator} {X : Set (Set ℤ)}
    (hG : G.EventuallyValidOn X) : Generator.EventuallyValidOn G X := by
  intro K hK w hw
  obtain ⟨T, hT⟩ := hG K hK w hw
  apply (Set.finite_Iio T).subset
  intro t ht
  by_contra hnot
  have hge : T ≤ t := Nat.le_of_not_gt hnot
  have hgood := (hT t hge).1
  exact ht hgood

lemma hd_valid_to_oned {G : Generator ℤ} {X : Set (Set ℤ)}
    (hf : G.Fresh) (hv : G.EventuallyValidOn X) : BanachDensity1D.Generator.EventuallyValidOn G X := by
  intro K hK w hw
  obtain ⟨T, hT⟩ := (hv K hK w hw).bddAbove
  refine ⟨T + 1, ?_⟩
  intro t ht
  refine ⟨?_, hf w t⟩
  by_contra hbad
  have hb := hT hbad
  omega

lemma transported_outputSet {α β : Type*} (e : α ≃ β) (G : Generator α) (w : ℕ → β) :
    (transportGenerator e G).outputSet w = e '' G.outputSet (e.symm ∘ w) := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨G.out (e.symm ∘ w) t, mem_range_self t, (transported_out e G w t).symm⟩
  · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, transported_out e G w t⟩

lemma image_inverse {α β : Type*} (e : α ≃ β) (K : Set α) : e.symm '' (e '' K) = K := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa only [Equiv.symm_apply_apply] using hz
  · intro hx
    exact ⟨e x, ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩

lemma pullback_outputSet {α β : Type*} (e : α ≃ β) (G : Generator β) (w : ℕ → α) :
    G.outputSet (e ∘ w) = e '' (transportGenerator e.symm G).outputSet w := by
  rw [transported_outputSet]
  simp only [Set.image_image, Equiv.symm_symm, Equiv.apply_symm_apply]
  exact (Set.image_id _).symm

lemma image_family_inverse {α β : Type*} (e : α ≃ β) (X : Set (Set α)) :
    (fun L => e.symm '' L) '' ((fun K => e '' K) '' X) = X := by
  ext L
  constructor
  · rintro ⟨M, ⟨K, hK, rfl⟩, rfl⟩
    simpa only [image_inverse] using hK
  · intro hL
    exact ⟨e '' L, ⟨L, hL, rfl⟩, image_inverse e L⟩

lemma indexed_image_range {α β : Type*} (e : α ≃ β) (K : ℕ → Set α) :
    range (fun i => e '' K i) = (fun L => e '' L) '' range K := by
  ext L
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨K i, mem_range_self i, rfl⟩
  · rintro ⟨M, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩

lemma enumeration_pushforward {α β : Type*} (e : α ≃ β) {K : Set α} {w : ℕ → α}
    (hw : IsFullEnumeration w K) : IsFullEnumeration (e ∘ w) (e '' K) := by
  change range (e ∘ w) = e '' K
  rw [Set.range_comp, hw]

lemma image_eq_ray {d : ℕ} (e : ℤ ≃ Pt d) (he : ∀ z : ℤ, 0 ≤ z → e z = ray d z)
    (L : Set ℤ) (hL : L ⊆ Ici (0 : ℤ)) : e '' L = ray d '' L := by
  apply Set.image_congr
  intro z hz
  exact he z (hL hz)

lemma equiv_images_inter {α β : Type*} (e : α ≃ β) (O L : Set α) :
    e '' O ∩ e '' L = e '' (O ∩ L) := by
  ext x
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, y, hy, he⟩
    exact ⟨z, ⟨hz, by simpa only [e.injective he] using hy⟩, rfl⟩
  · rintro ⟨z, ⟨hz, hzL⟩, rfl⟩
    exact ⟨⟨z, hz, rfl⟩, ⟨z, hzL, rfl⟩⟩

/-- Off-ray invalid outputs do not contribute to the valid-target numerator.
No assumption says that a competing generator always stays on the ray. -/
lemma equiv_filtered_density {d : ℕ} (hd : 1 ≤ d)
    (e : ℤ ≃ Pt d) (he : ∀ z : ℤ, 0 ≤ z → e z = ray d z)
    (h : ℕ → ℝ) (hp : ∀ n, 1 ≤ n → 0 < h n) (hm : MonotoneOn h (Ici 1))
    (O L : Set ℤ) (hL : L ⊆ Ici (0 : ℤ)) :
    deltaH h (e '' O) (e '' L) = intervalDensity h O L := by
  have hLi := image_eq_ray e he L hL
  have hOi : e '' O ∩ e '' L = ray d '' O ∩ ray d '' L := by
    rw [equiv_images_inter, ray_images_inter hd]
    exact image_eq_ray e he (O ∩ L) (fun z hz => hL hz.2)
  calc
    _ = deltaH h (e '' O ∩ e '' L) (e '' L) := (Oct31.deltaH_inter_target h _ _).symm
    _ = deltaH h (ray d '' O ∩ ray d '' L) (ray d '' L) := by rw [hOi, hLi]
    _ = deltaH h (ray d '' O) (ray d '' L) := Oct31.deltaH_inter_target h _ _
    _ = _ := ray_filtered_density_eq hd h hp hm O L

end BanachDensityHD.Nov1
