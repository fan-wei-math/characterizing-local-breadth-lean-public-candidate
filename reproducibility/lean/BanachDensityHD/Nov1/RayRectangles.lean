import BanachDensityHD.Nov1.RayEquivalence

/-! # Thin rectangles preserve coordinate-ray populations and reduce volume. -/

namespace BanachDensityHD.Nov1
open Set

/-- Thin rectangle corresponding to an integer interval. Singleton transverse
sides are permitted by the existing rectangle definition. -/
def rayRectangle (d : ℕ) (a b : ℤ) (hab : a ≤ b) : Rect d :=
  .mk (ray d a) (ray d b) (by intro i; by_cases hi : i.val = 0 <;> simp [ray, hi, hab])

lemma rayRectangle_pts {d : ℕ} (hd : 1 ≤ d) (a b : ℤ) (hab : a ≤ b) :
    (rayRectangle d a b hab).pts = ray d '' Icc a b := by
  ext x
  constructor
  · intro hx
    change ray d a ≤ x ∧ x ≤ ray d b at hx
    let i0 : Fin d := ⟨0, by omega⟩
    have hlo := hx.1 i0
    have hup := hx.2 i0
    have hz : x i0 ∈ Icc a b := by simpa [rayRectangle, Rect.pts, Rect.lo, Rect.hi, ray, i0] using And.intro hlo hup
    refine ⟨x i0, hz, ?_⟩
    funext i
    by_cases hi : i.val = 0
    · have he : i = i0 := Fin.ext hi
      simp [ray, hi, he, i0]
    · have hl := hx.1 i
      have hu := hx.2 i
      simp only [ray, ite_eq_right hi] at hl hu ⊢
      omega
  · rintro ⟨z, hz, rfl⟩
    change ray d a ≤ ray d z ∧ ray d z ≤ ray d b
    constructor <;> intro i <;> by_cases hi : i.val = 0 <;> simp [rayRectangle, ray, hi, hz.1, hz.2]

lemma rayRectangle_volume {d : ℕ} (hd : 1 ≤ d) (a b : ℤ) (hab : a ≤ b) :
    (rayRectangle d a b hab).vol = (Icc a b).ncard := by
  rw [Rect.vol, rayRectangle_pts hd, ncard_image_of_injective _ (ray_injective hd)]

lemma ray_image_inter {d : ℕ} (hd : 1 ≤ d) (L : Set ℤ) (a b : ℤ) (hab : a ≤ b) :
    ray d '' L ∩ (rayRectangle d a b hab).pts = ray d '' (L ∩ Icc a b) := by
  rw [rayRectangle_pts hd]
  ext x
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, ⟨w, hw, he⟩⟩
    have hzw := ray_injective hd he
    exact ⟨z, ⟨hz, by simpa only [hzw] using hw⟩, rfl⟩
  · rintro ⟨z, ⟨hz, hab'⟩, rfl⟩
    exact ⟨⟨z, hz, rfl⟩, ⟨z, hab', rfl⟩⟩

/-- A rectangle meeting the ray has a thin replacement with exactly its ray
intersection, hence exactly its valid-target numerator and denominator. -/
lemma thin_replacement {d : ℕ} (hd : 1 ≤ d) (R : Rect d)
    (hmeet : (R.pts ∩ range (ray d)).Nonempty) :
    ∃ a b : ℤ, ∃ hab : a ≤ b,
      (rayRectangle d a b hab).pts ⊆ R.pts ∧
      R.pts ∩ range (ray d) = (rayRectangle d a b hab).pts ∧
      (rayRectangle d a b hab).vol ≤ R.vol := by
  obtain ⟨_, hx, z, rfl⟩ := hmeet
  let i0 : Fin d := ⟨0, by omega⟩
  let a := R.lo i0
  let b := R.hi i0
  have hab : a ≤ b := R.le i0
  have hsub : (rayRectangle d a b hab).pts ⊆ R.pts := by
    rw [rayRectangle_pts hd]
    rintro x ⟨y, hy, rfl⟩
    constructor <;> intro i
    · by_cases hi : i.val = 0
      · have he : i = i0 := Fin.ext hi
        simpa [ray, hi, he, a, i0] using hy.1
      · simpa [ray, hi] using hx.1 i
    · by_cases hi : i.val = 0
      · have he : i = i0 := Fin.ext hi
        simpa [ray, hi, he, b, i0] using hy.2
      · simpa [ray, hi] using hx.2 i
  refine ⟨a, b, hab, hsub, ?_, ncard_le_ncard hsub (BasicAux.rect_pts_finite R)⟩
  rw [rayRectangle_pts hd]
  ext x
  constructor
  · rintro ⟨hx, y, rfl⟩
    refine ⟨y, ?_, rfl⟩
    exact ⟨by simpa [ray, i0, a] using hx.1 i0, by simpa [ray, i0, b] using hx.2 i0⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨hsub ?_, mem_range_self y⟩
    rw [rayRectangle_pts hd]
    exact ⟨y, hy, rfl⟩

end BanachDensityHD.Nov1
