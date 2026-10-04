import ProductCoordinateWeakHk_v1

/-! Iterated compact-test identities for the actual coordinate weak jets.
The recursive test order is the transpose order of the derivative word;
this keeps the integration-by-parts convention explicit. Both final test
integrals are proved integrable from region L2 membership.
-/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

def productCoordinateTestWord : List (Fin 4 ⊕ κ) → (Space κ → ℝ) → Space κ → ℝ
  | [], φ => φ
  | i :: w, φ => productCoordinateTestWord w (fun p => fderiv ℝ φ p (productCoordinateDirection i))

theorem productCoordinateTestWord_contDiff (w : List (Fin 4 ⊕ κ))
    {φ : Space κ → ℝ} (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (productCoordinateTestWord w φ) := by
  induction w generalizing φ with
  | nil => exact hφ
  | cons i w ih =>
    exact ih ((hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const)

theorem productCoordinateTestWord_compact (w : List (Fin 4 ⊕ κ))
    {φ : Space κ → ℝ} (hφ : HasCompactSupport φ) : HasCompactSupport (productCoordinateTestWord w φ) := by
  induction w generalizing φ with
  | nil => exact hφ
  | cons i w ih => exact ih (hφ.fderiv_apply ℝ (productCoordinateDirection i))

theorem productCoordinateTestWord_support (w : List (Fin 4 ⊕ κ)) (φ : Space κ → ℝ) :
    tsupport (productCoordinateTestWord w φ) ⊆ tsupport φ := by
  induction w generalizing φ with
  | nil => exact Set.Subset.refl _
  | cons i w ih => exact (ih _).trans (tsupport_fderiv_apply_subset ℝ (productCoordinateDirection i))

theorem product_coordinate_family_test_identity
    {Ω : Set (Space κ)} {m : ℕ} {f : Space κ → ℂ}
    (D : List (Fin 4 ⊕ κ) → Space κ → ℂ) (h0 : D [] = f)
    (hD : ∀ w i, w.length < m →
      ProductLocalWeakDirectional Ω (D w) (D (i :: w)) (productCoordinateDirection i))
    (w : List (Fin 4 ⊕ κ)) (hw : w.length ≤ m)
    {φ : Space κ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    (∫ p, φ p • D w p) = ((-1 : ℝ)^w.length) • (∫ p, productCoordinateTestWord w φ p • f p) := by
  induction w generalizing φ with
  | nil => simp only [productCoordinateTestWord,List.length_nil,pow_zero,one_smul,h0]
  | cons i w ih =>
    have hwm : w.length < m := by simp only [List.length_cons] at hw; omega
    have hDi : ContDiff ℝ ∞ (fun p => fderiv ℝ φ p (productCoordinateDirection i)) :=
      (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
    rw [(hD w i hwm).2.2 φ hφ hc hs,
      ih (by omega) hDi (hc.fderiv_apply ℝ (productCoordinateDirection i))
        ((tsupport_fderiv_apply_subset ℝ (productCoordinateDirection i)).trans hs)]
    simp only [productCoordinateTestWord,List.length_cons,pow_succ,mul_smul,
      neg_one_smul,smul_neg]

theorem product_coordinate_family_tests_integrable
    {Ω : Set (Space κ)} {m : ℕ} {W : ℝ}
    (D : List (Fin 4 ⊕ κ) → Space κ → ℂ)
    (hD : ∀ w, w.length ≤ m → RegionL2Budget (D w) Ω W)
    (w : List (Fin 4 ⊕ κ)) (hw : w.length ≤ m)
    {φ : Space κ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    Integrable (fun p => φ p • D w p) ∧
      Integrable (fun p => productCoordinateTestWord w φ p • D [] p) := by
  exact ⟨product_raw_locallyL2_compact_smul_integrable (hD w hw).local hφ.continuous hc hs,
    product_raw_locallyL2_compact_smul_integrable (hD [] (by simp)).local
      (productCoordinateTestWord_contDiff w hφ).continuous
      (productCoordinateTestWord_compact w hc) ((productCoordinateTestWord_support w φ).trans hs)⟩

#print axioms productCoordinateTestWord_contDiff
#print axioms productCoordinateTestWord_compact
#print axioms productCoordinateTestWord_support
#print axioms product_coordinate_family_test_identity
#print axioms product_coordinate_family_tests_integrable
end TheoremT.Continuum.WeakGrushin
