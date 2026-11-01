import ProductMixedMultiIndexWordFamily_v1

/-! Local uniqueness across independently selected finite weak derivative
families. Only equality of the zero-word representatives almost everywhere
and genuine weak chains are assumed. The conclusion is local AE equality,
not pointwise equality or equality outside the open domain. This allows
previous finite derivative budgets to be transferred to a later selected
family of the same raw function.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ ι : Type} [Fintype κ] [DecidableEq κ]

theorem product_local_weak_word_families_unique
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω) (dirs : ι → Space κ) {m : ℕ}
    (D E : List ι → Space κ → ℂ)
    (h0 : ∀ᵐ p ∂volume, p ∈ Ω → D [] p = E [] p)
    (hD : ∀ w i, w.length < m → ProductLocalWeakDirectional Ω (D w) (D (i :: w)) (dirs i))
    (hE : ∀ w i, w.length < m → ProductLocalWeakDirectional Ω (E w) (E (i :: w)) (dirs i)) :
    ∀ w, w.length ≤ m → ∀ᵐ p ∂volume, p ∈ Ω → D w p = E w p := by
  intro w
  induction w with
  | nil => exact fun _ => h0
  | cons i w ih =>
    intro hw
    have hw' : w.length < m := by simp only [List.length_cons] at hw; omega
    have hReplace := (hD w i hw').congr_ae_local (ih (by omega))
      (Eventually.of_forall (fun p _ => rfl))
    exact ProductLocalWeakDirectional.unique hΩ hReplace (hE w i hw')

theorem product_mixed_multiIndex_weak_families_unique
    {Ω : Set (Space (Fin 3))} (hΩ : IsOpen Ω) {m : ℕ}
    (F G : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ)
    (h0 : ∀ᵐ p ∂volume, p ∈ Ω → F 0 0 p = G 0 0 p)
    (hFY : ∀ α β i, (∑ k,α k)+(∑ j,β j) < m →
      ProductLocalWeakDirectional Ω (F α β) (F (α+Pi.single i 1) β) (yDir i))
    (hFT : ∀ α β j, (∑ i,α i)+(∑ k,β k) < m →
      ProductLocalWeakDirectional Ω (F α β) (F α (β+Pi.single j 1)) (tDir j))
    (hGY : ∀ α β i, (∑ k,α k)+(∑ j,β j) < m →
      ProductLocalWeakDirectional Ω (G α β) (G (α+Pi.single i 1) β) (yDir i))
    (hGT : ∀ α β j, (∑ i,α i)+(∑ k,β k) < m →
      ProductLocalWeakDirectional Ω (G α β) (G α (β+Pi.single j 1)) (tDir j))
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (hab : (∑ i,α i)+(∑ j,β j) ≤ m) :
    ∀ᵐ p ∂volume, p ∈ Ω → F α β p = G α β p := by
  have h := product_local_weak_word_families_unique hΩ productCoordinateDirection
    (mixedMultiIndexWordFamily F) (mixedMultiIndexWordFamily G)
    (by simpa only [mixedMultiIndexWordFamily_nil] using h0)
    (mixedMultiIndexWordFamily_localD F hFY hFT) (mixedMultiIndexWordFamily_localD G hGY hGT)
    (mixedMultiIndexWord α β) (by rwa [mixedMultiIndexWord_length])
  simpa only [mixedMultiIndexWordFamily_canonical] using h

theorem RegionL2Budget.congr_ae
    {Ω : Set (Space κ)} {f g : Space κ → ℂ} {W : ℝ}
    (hf : RegionL2Budget f Ω W) (hfg : f =ᵐ[volume.restrict Ω] g) :
    RegionL2Budget g Ω W := by
  refine ⟨(memLp_congr_ae hfg).mp hf.1,?_⟩
  calc
    (∫ p in Ω, ‖g p‖^2) = ∫ p in Ω, ‖f p‖^2 := by
      apply integral_congr_ae
      filter_upwards [hfg] with p hp
      rw [hp]
    _ ≤ W := hf.2

#print axioms product_local_weak_word_families_unique
#print axioms product_mixed_multiIndex_weak_families_unique
#print axioms RegionL2Budget.congr_ae
end TheoremT.Continuum.WeakGrushin
