import ProductLocalWeakDirectionalLeibniz_v1
import CompactHessianCross_v1

/-! Actual local weak directional calculus for mixed finite derivative families.
The relation includes local L2 membership of both functions. Commuting two
directions constructs the missing weak derivative identity using symmetric
second derivatives of compact smooth tests; no mixed compatibility is assumed.
-/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff
namespace TheoremT.Continuum
variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

def ProductLocalWeakDirectional (Ω : Set (Y × T))
    (f d : Y × T → ℂ) (v : Y × T) : Prop :=
  ProductLocallyL2On f Ω ∧ ProductLocallyL2On d Ω ∧
    ∀ φ : Y × T → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, φ p • d p) = -(∫ p, fderiv ℝ φ p v • f p)

theorem ProductLocalWeakDirectional.of_global
    {f d : Lp ℂ 2 (volume : Measure (Y × T))} {v : Y × T}
    (hD : WeakProductL2Directional f d v) (Ω : Set (Y × T)) :
    ProductLocalWeakDirectional Ω f d v := by
  refine ⟨fun K _ _ => (Lp.memLp f).mono_measure Measure.restrict_le_self,
    fun K _ _ => (Lp.memLp d).mono_measure Measure.restrict_le_self,?_⟩
  intro φ hφ hcφ _
  exact hD φ hφ hcφ

theorem ProductLocalWeakDirectional.mono
    {Ω V : Set (Y × T)} {f d : Y × T → ℂ} {v : Y × T}
    (hD : ProductLocalWeakDirectional Ω f d v) (hV : V ⊆ Ω) :
    ProductLocalWeakDirectional V f d v :=
  ⟨fun K hK hs => hD.1 K hK (hs.trans hV),
    fun K hK hs => hD.2.1 K hK (hs.trans hV),
    fun φ hφ hcφ hsφ => hD.2.2 φ hφ hcφ (hsφ.trans hV)⟩

theorem ProductLocalWeakDirectional.test_integrable
    {Ω : Set (Y × T)} {f d : Y × T → ℂ} {v : Y × T}
    (hD : ProductLocalWeakDirectional Ω f d v)
    {φ : Y × T → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Ω) :
    Integrable (fun p => φ p • d p) ∧ Integrable (fun p => fderiv ℝ φ p v • f p) := by
  refine ⟨product_raw_locallyL2_compact_smul_integrable hD.2.1 hφ.continuous hcφ hsφ,?_⟩
  apply product_raw_locallyL2_compact_smul_integrable hD.1
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hcφ.fderiv_apply ℝ v)
  exact (tsupport_fderiv_apply_subset ℝ v).trans hsφ

theorem ProductLocalWeakDirectional.swap
    {Ω : Set (Y × T)} {f dv dw e : Y × T → ℂ} {v w : Y × T}
    (hv : ProductLocalWeakDirectional Ω f dv v)
    (hw : ProductLocalWeakDirectional Ω f dw w)
    (hvw : ProductLocalWeakDirectional Ω dv e w) :
    ProductLocalWeakDirectional Ω dw e v := by
  refine ⟨hw.2.1,hvw.2.1,?_⟩
  intro φ hφ hcφ hsφ
  have hD (a : Y × T) : ContDiff ℝ ∞ (fun p => fderiv ℝ φ p a) :=
    (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hcD (a : Y × T) := hcφ.fderiv_apply ℝ a
  have hsD (a : Y × T) := (tsupport_fderiv_apply_subset ℝ a).trans hsφ
  calc
    _ = ∫ p, fderiv ℝ (fun q => fderiv ℝ φ q w) p v • f p := by
      rw [hvw.2.2 φ hφ hcφ hsφ,hv.2.2 _ (hD w) (hcD w) (hsD w),neg_neg]
    _ = ∫ p, fderiv ℝ (fun q => fderiv ℝ φ q v) p w • f p := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun p => congrArg (fun a : ℝ => a • f p)
        (smooth_second_directional_commute hφ p w v))
    _ = _ := by
      rw [hw.2.2 _ (hD v) (hcD v) (hsD v),neg_neg]

theorem ProductLocalWeakDirectional.smooth_smul
    {Ω : Set (Y × T)} (hΩ : IsOpen Ω) {B : Y × T → ℝ}
    (hB : ContDiffOn ℝ ∞ B Ω) {f d : Y × T → ℂ} {v : Y × T}
    (hD : ProductLocalWeakDirectional Ω f d v) :
    ProductLocalWeakDirectional Ω (fun p => B p • f p)
      (fun p => B p • d p + fderiv ℝ B p v • f p) v := by
  obtain ⟨hf,hd,hEq⟩ := product_local_weak_directional_leibniz hΩ hB hD.1 hD.2.1 hD.2.2
  exact ⟨hf,hd,fun φ hφ hcφ hsφ => (hEq φ hφ hcφ hsφ).2.2⟩

#print axioms ProductLocalWeakDirectional.of_global
#print axioms ProductLocalWeakDirectional.mono
#print axioms ProductLocalWeakDirectional.test_integrable
#print axioms ProductLocalWeakDirectional.swap
#print axioms ProductLocalWeakDirectional.smooth_smul
end TheoremT.Continuum
