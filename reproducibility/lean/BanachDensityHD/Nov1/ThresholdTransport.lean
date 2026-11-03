import BanachDensityHD.Basic

/-! # Cofinal threshold rescaling and ordinary-to-filtered lower guarantees.

All density definitions are the existing ones. Only the indexing of eligible
tests changes; no ordinary density upper bound is substituted for a filtered one.
-/

namespace BanachDensityHD.Nov1
open Set Filter
open scoped Topology

lemma testInf_scale {d : ℕ} (h : ℕ → ℝ) (O L : Set (Pt d)) (c s : ℝ) :
    testInf (fun v => c * h v) O L s = testInf h O L (s * c) := by
  classical
  have he : BasicAux.tests (fun v => c * h v) O L s = BasicAux.tests h O L (s * c) := by
    ext r
    simp only [BasicAux.tests, mem_ofPred_eq, mul_assoc]
  exact congrArg (fun S : Set ℝ => if S.Nonempty then sInf S else 1) he

/-- Positive constant scaling does not change the filtered limit. -/
lemma deltaH_scale {d : ℕ} (h : ℕ → ℝ) (hp : ∀ n, 1 ≤ n → 0 < h n)
    (O L : Set (Pt d)) {c : ℝ} (hc : 0 < c) :
    deltaH (fun v => c * h v) O L = deltaH h O L := by
  have hscaled := (deltaH_tendsto (fun v => c * h v) (fun n hn => mul_pos hc (hp n hn)) O L).1
  have hcofinal : Tendsto (fun s : ℝ => s * c) atTop atTop :=
    (tendsto_mul_const_atTop_of_pos hc).mpr tendsto_id
  have hcomp := (deltaH_tendsto h hp O L).1.comp hcofinal
  have heq : (fun s => testInf (fun v => c * h v) O L s) = fun s => testInf h O L (s * c) :=
    funext (testInf_scale h O L c)
  change Tendsto (fun s => testInf (fun v => c * h v) O L s) atTop
    (𝓝 (deltaH (fun v => c * h v) O L)) at hscaled
  rw [heq] at hscaled
  exact tendsto_nhds_unique hscaled hcomp

lemma testInf_threshold_mono {d : ℕ} (h g : ℕ → ℝ)
    (hle : ∀ n, 1 ≤ n → h n ≤ g n) (O L : Set (Pt d)) {s : ℝ} (hs : 0 ≤ s) :
    testInf h O L s ≤ testInf g O L s := by
  have hsub : BasicAux.tests g O L s ⊆ BasicAux.tests h O L s := by
    rintro r ⟨R, hR, rfl⟩
    exact ⟨R, le_trans (mul_le_mul_of_nonneg_left (hle R.vol (BasicAux.rect_vol_pos R)) hs) hR, rfl⟩
  by_cases hne : (BasicAux.tests g O L s).Nonempty
  · rw [BasicAux.testInf_eq, BasicAux.testInf_eq, ite_eq_left hne, ite_eq_left (hne.mono hsub)]
    exact csInf_le_csInf (BasicAux.tests_bdd h O L s) hne hsub
  · rw [BasicAux.testInf_eq g O L s, ite_eq_right hne]
    exact (BasicAux.testInf_mem h O L s).2

lemma deltaH_threshold_mono {d : ℕ} (h g : ℕ → ℝ)
    (hp : ∀ n, 1 ≤ n → 0 < h n) (gp : ∀ n, 1 ≤ n → 0 < g n)
    (hle : ∀ n, 1 ≤ n → h n ≤ g n) (O L : Set (Pt d)) :
    deltaH h O L ≤ deltaH g O L := by
  exact le_of_tendsto_of_tendsto (deltaH_tendsto h hp O L).1 (deltaH_tendsto g gp O L).1
    (eventually_atTop.2 ⟨0, fun s hs => testInf_threshold_mono h g hle O L hs⟩)

/-- One ordinary-density lower guarantee transfers to every positive monotone
filter, using the same output set and hence the same simultaneous generator. -/
lemma ordinary_le_filtered {d : ℕ} (h : ℕ → ℝ)
    (hp : ∀ n, 1 ≤ n → 0 < h n) (hm : MonotoneOn h (Ici 1)) (O L : Set (Pt d)) :
    deltaH (fun _ => 1) O L ≤ deltaH h O L := by
  have hscale := deltaH_scale (fun _ => 1) (fun _ _ => one_pos) O L (hp 1 le_rfl)
  simp only [mul_one] at hscale
  rw [← hscale]
  exact deltaH_threshold_mono (fun _ => h 1) h (fun _ _ => hp 1 le_rfl) hp
    (fun n hn => hm (by simp) (by exact hn) hn) O L

end BanachDensityHD.Nov1
