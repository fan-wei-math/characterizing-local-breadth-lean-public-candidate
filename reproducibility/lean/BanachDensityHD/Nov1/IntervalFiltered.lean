import BanachDensityHD.Nov1.RayRectangles
import BanachDensityHD.Nov1.ThresholdTransport

/-! # Exact preservation of filtered density on the coordinate ray. -/

namespace BanachDensityHD.Nov1
open Set Filter
open scoped Topology

def intervalTests (h : ℕ → ℝ) (O L : Set ℤ) (s : ℝ) : Set ℝ :=
  {r | ∃ a b : ℤ, a ≤ b ∧ s * h (Icc a b).ncard ≤ (L ∩ Icc a b).ncard ∧
    r = (((O ∩ L) ∩ Icc a b).ncard : ℝ) / (L ∩ Icc a b).ncard}

noncomputable def intervalTestInf (h : ℕ → ℝ) (O L : Set ℤ) (s : ℝ) : ℝ := by
  classical
  exact if (intervalTests h O L s).Nonempty then sInf (intervalTests h O L s) else 1

noncomputable def intervalDensity (h : ℕ → ℝ) (O L : Set ℤ) : ℝ :=
  limUnder atTop (intervalTestInf h O L)

lemma ray_images_inter {d : ℕ} (hd : 1 ≤ d) (O L : Set ℤ) :
    ray d '' O ∩ ray d '' L = ray d '' (O ∩ L) := by
  ext x
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, w, hw, he⟩
    have hzw := ray_injective hd he
    exact ⟨z, ⟨hz, by simpa only [hzw] using hw⟩, rfl⟩
  · rintro ⟨z, ⟨hz, hzL⟩, rfl⟩
    exact ⟨⟨z, hz, rfl⟩, ⟨z, hzL, rfl⟩⟩

lemma ray_mass {d : ℕ} (hd : 1 ≤ d) (L : Set ℤ) (a b : ℤ) (hab : a ≤ b) :
    mass (ray d '' L) (rayRectangle d a b hab) = (L ∩ Icc a b).ncard := by
  rw [mass, ray_image_inter hd, ncard_image_of_injective _ (ray_injective hd)]

lemma ray_numerator {d : ℕ} (hd : 1 ≤ d) (O L : Set ℤ) (a b : ℤ) (hab : a ≤ b) :
    (ray d '' O ∩ ray d '' L ∩ (rayRectangle d a b hab).pts).ncard =
      ((O ∩ L) ∩ Icc a b).ncard := by
  rw [ray_images_inter hd, ray_image_inter hd, ncard_image_of_injective _ (ray_injective hd)]

lemma subset_range_thin {d : ℕ} {M : Set (Pt d)} (hM : M ⊆ range (ray d))
    {R T : Rect d} (he : R.pts ∩ range (ray d) = T.pts) :
    M ∩ R.pts = M ∩ T.pts := by
  ext x
  constructor
  · rintro ⟨hx, hR⟩
    exact ⟨hx, he ▸ ⟨hR, hM hx⟩⟩
  · rintro ⟨hx, hT⟩
    have hh : x ∈ R.pts ∩ range (ray d) := he.symm ▸ hT
    exact ⟨hx, hh.1⟩

lemma tests_ray_eq {d : ℕ} (hd : 1 ≤ d) (h : ℕ → ℝ)
    (hp : ∀ n, 1 ≤ n → 0 < h n) (hm : MonotoneOn h (Ici 1))
    (O L : Set ℤ) {s : ℝ} (hs : 0 < s) :
    BasicAux.tests h (ray d '' O) (ray d '' L) s = intervalTests h O L s := by
  ext r
  constructor
  · rintro ⟨R, hlevel, hr⟩
    have hmass : 0 < mass (ray d '' L) R := by
      have hpos := mul_pos hs (hp R.vol (BasicAux.rect_vol_pos R))
      have hreal := hpos.trans_le hlevel
      exact_mod_cast hreal
    obtain ⟨x, hxL, hxR⟩ := nonempty_of_ncard_ne_zero (Nat.ne_zero_of_lt hmass)
    have hmeet : (R.pts ∩ range (ray d)).Nonempty :=
      ⟨x, hxR, by obtain ⟨z, _, rfl⟩ := hxL; exact mem_range_self z⟩
    obtain ⟨a, b, hab, _, he, hvol⟩ := thin_replacement hd R hmeet
    have hmEq : mass (ray d '' L) R = mass (ray d '' L) (rayRectangle d a b hab) := by
      exact congrArg ncard (subset_range_thin (fun _ hx => by obtain ⟨z, _, rfl⟩ := hx; exact mem_range_self z) he)
    have hnEq : (ray d '' O ∩ ray d '' L ∩ R.pts).ncard =
        (ray d '' O ∩ ray d '' L ∩ (rayRectangle d a b hab).pts).ncard := by
      exact congrArg ncard (subset_range_thin (fun _ hx => by obtain ⟨z, _, rfl⟩ := hx.1; exact mem_range_self z) he)
    refine ⟨a, b, hab, ?_, ?_⟩
    · have hcomp := mul_le_mul_of_nonneg_left (hm (BasicAux.rect_vol_pos _) (BasicAux.rect_vol_pos R) hvol) hs.le
      have hlev := hcomp.trans hlevel
      rw [hmEq, ray_mass hd, rayRectangle_volume hd] at hlev
      exact hlev
    · rw [hmEq, hnEq, ray_mass hd, ray_numerator hd] at hr
      exact hr
  · rintro ⟨a, b, hab, hlevel, hr⟩
    refine ⟨rayRectangle d a b hab, ?_, ?_⟩
    · simpa only [rayRectangle_volume hd, ray_mass hd] using hlevel
    · simpa only [ray_mass hd, ray_numerator hd] using hr

lemma testInf_ray_eq {d : ℕ} (hd : 1 ≤ d) (h : ℕ → ℝ)
    (hp : ∀ n, 1 ≤ n → 0 < h n) (hm : MonotoneOn h (Ici 1))
    (O L : Set ℤ) {s : ℝ} (hs : 0 < s) :
    testInf h (ray d '' O) (ray d '' L) s = intervalTestInf h O L s := by
  classical
  exact congrArg (fun S : Set ℝ => if S.Nonempty then sInf S else 1) (tests_ray_eq hd h hp hm O L hs)

/-- Equality holds for the full filtered density, not merely for ordinary density
or for a selected sequence of thin tests. -/
lemma ray_filtered_density_eq {d : ℕ} (hd : 1 ≤ d) (h : ℕ → ℝ)
    (hp : ∀ n, 1 ≤ n → 0 < h n) (hm : MonotoneOn h (Ici 1)) (O L : Set ℤ) :
    deltaH h (ray d '' O) (ray d '' L) = intervalDensity h O L := by
  have ht := (deltaH_tendsto h hp (ray d '' O) (ray d '' L)).1
  have hi : Tendsto (intervalTestInf h O L) atTop (𝓝 (deltaH h (ray d '' O) (ray d '' L))) := by
    apply ht.congr'
    exact eventually_atTop.2 ⟨1, fun s hs => testInf_ray_eq hd h hp hm O L (lt_of_lt_of_le zero_lt_one hs)⟩
  exact hi.limUnder_eq.symm

end BanachDensityHD.Nov1
