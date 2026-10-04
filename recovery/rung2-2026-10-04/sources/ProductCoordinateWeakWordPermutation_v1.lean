import ProductCoordinateWeakWordTests_v1
import LocalProductDirectionalWeakUnique_v1

/-! Permuting actual coordinate derivative words preserves their local weak
representatives almost everywhere on an open domain. The proof first commutes
ordinary smooth compact tests, then applies distributional uniqueness. It does
not identify arbitrary representatives pointwise or assume mixed compatibility.
-/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem productCoordinateTestWord_perm
    {u v : List (Fin 4 ⊕ κ)} (huv : u.Perm v)
    {φ : Space κ → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    productCoordinateTestWord u φ = productCoordinateTestWord v φ := by
  induction huv generalizing φ with
  | nil => rfl
  | cons i h ih =>
    exact ih ((hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const)
  | swap i j w =>
    simp only [productCoordinateTestWord]
    congr 1
    funext p
    exact smooth_second_directional_commute hφ p _ _
  | trans h1 h2 ih1 ih2 => exact (ih1 hφ).trans (ih2 hφ)

set_option maxHeartbeats 800000 in
theorem product_coordinate_family_word_perm_ae
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω) {m : ℕ} {W : ℝ}
    (D : List (Fin 4 ⊕ κ) → Space κ → ℂ)
    (hBudget : ∀ w, w.length ≤ m → RegionL2Budget (D w) Ω W)
    (hChain : ∀ w i, w.length < m →
      ProductLocalWeakDirectional Ω (D w) (D (i :: w)) (productCoordinateDirection i))
    {u v : List (Fin 4 ⊕ κ)} (huv : u.Perm v) (hu : u.length ≤ m) :
    ∀ᵐ p ∂volume, p ∈ Ω → D u p = D v p := by
  have hv : v.length ≤ m := huv.length_eq ▸ hu
  have hloc : LocallyIntegrableOn (fun p => D u p-D v p) Ω volume :=
    (productLocallyL2On_locallyIntegrableOn hΩ (hBudget u hu).local).sub
      (productLocallyL2On_locallyIntegrableOn hΩ (hBudget v hv).local)
  have hz := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    (fun φ hφ hc hs => by
      have hi := (product_coordinate_family_tests_integrable D hBudget u hu hφ hc hs).1
      have hj := (product_coordinate_family_tests_integrable D hBudget v hv hφ hc hs).1
      simp only [smul_sub]
      rw [integral_sub hi hj,
        product_coordinate_family_test_identity D rfl hChain u hu hφ hc hs,
        product_coordinate_family_test_identity D rfl hChain v hv hφ hc hs,
        productCoordinateTestWord_perm huv hφ,huv.length_eq,sub_self])
  filter_upwards [hz] with p hp hmem
  exact sub_eq_zero.mp (hp hmem)

theorem product_coordinate_family_derivative_of_perm
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω) {m : ℕ} {W : ℝ}
    (D : List (Fin 4 ⊕ κ) → Space κ → ℂ)
    (hBudget : ∀ w, w.length ≤ m → RegionL2Budget (D w) Ω W)
    (hChain : ∀ w i, w.length < m →
      ProductLocalWeakDirectional Ω (D w) (D (i :: w)) (productCoordinateDirection i))
    {u v : List (Fin 4 ⊕ κ)} (i : Fin 4 ⊕ κ)
    (huv : (i :: u).Perm v) (hu : u.length < m) :
    ProductLocalWeakDirectional Ω (D u) (D v) (productCoordinateDirection i) := by
  exact (hChain u i hu).congr_ae_local (Eventually.of_forall (fun p _ => rfl))
    (product_coordinate_family_word_perm_ae hΩ D hBudget hChain huv
      (by simp only [List.length_cons]; omega))

#print axioms productCoordinateTestWord_perm
#print axioms product_coordinate_family_word_perm_ae
#print axioms product_coordinate_family_derivative_of_perm
end TheoremT.Continuum.WeakGrushin
