import BanachDensityHD.Nov1.GeneratorTransport

/-! # Extending the nonnegative coordinate ray to a bijection of ambient spaces. -/

namespace BanachDensityHD.Nov1
open Set

/-- The coordinate ray map, defined on all integers for counting and restricted
to nonnegative integers when defining the constructed languages. -/
def ray (d : ℕ) (z : ℤ) : Pt d := fun i => if i.val = 0 then z else 0

lemma ray_injective {d : ℕ} (hd : 1 ≤ d) : Function.Injective (ray d) := by
  intro x y he
  have h := congrFun he (⟨0, by omega⟩ : Fin d)
  simpa [ray] using h

def nonnegativeRay (d : ℕ) : Set (Pt d) := ray d '' Ici 0

/-- The complement equivalence matters: a map N -> Z^d alone would not transport
global freshness on arbitrary, possibly invalid, input histories. -/
theorem ray_extension {d : ℕ} (hd : 2 ≤ d) :
    ∃ e : ℤ ≃ Pt d, ∀ z : ℤ, 0 ≤ z → e z = ray d z := by
  classical
  let neg : ℕ → ((Ici (0 : ℤ))ᶜ : Set ℤ) := fun n => ⟨-((n : ℤ) + 1), by
    change ¬ (0 : ℤ) ≤ -((n : ℤ) + 1)
    omega⟩
  have hneg : Function.Injective neg := by
    intro n m he
    have := congrArg Subtype.val he
    dsimp [neg] at this
    omega
  letI : Infinite ((Ici (0 : ℤ))ᶜ : Set ℤ) := Infinite.of_injective neg hneg
  let off : ℕ → ((nonnegativeRay d)ᶜ : Set (Pt d)) := fun n =>
    ⟨(fun i => if i.val = 1 then (n : ℤ) + 1 else 0), by
      rintro ⟨z, _, he⟩
      have h := congrFun he (⟨1, hd⟩ : Fin d)
      simp only [ray, ↓reduceIte, Fin.val_mk, one_ne_zero] at h
      omega⟩
  have hoff : Function.Injective off := by
    intro n m he
    have h := congrFun (congrArg Subtype.val he) (⟨1, hd⟩ : Fin d)
    change (n : ℤ) + 1 = (m : ℤ) + 1 at h
    omega
  letI : Infinite ((nonnegativeRay d)ᶜ : Set (Pt d)) := Infinite.of_injective off hoff
  let e0 : (Ici (0 : ℤ)) ≃ nonnegativeRay d :=
    Equiv.Set.imageOfInjOn (ray d) (Ici 0) (ray_injective (by omega)).injOn
  let ec : ((Ici (0 : ℤ))ᶜ : Set ℤ) ≃ ((nonnegativeRay d)ᶜ : Set (Pt d)) :=
    Classical.choice inferInstance
  let ee := (Equiv.Set.compl e0).symm ec
  refine ⟨ee.val, ?_⟩
  intro z hz
  have h := ee.property (⟨z, hz⟩ : Ici (0 : ℤ))
  exact h

end BanachDensityHD.Nov1
