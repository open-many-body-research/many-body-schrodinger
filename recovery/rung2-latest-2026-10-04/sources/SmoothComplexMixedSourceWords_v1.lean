import LocalProductDirectionalWeakAlgebra_v1
import ProductContinuousLocalL2_v1
import LocalSecondDerivativeIBP_v1
import CompactSpectatorCutoffEnergy_v1
import WeakGrushinJetFields_v1

/-! Actual ordered mixed derivatives of a complex locally smooth source.
The complex source is unrestricted; it need not be a real function times
a fixed amplitude. Integration by parts proves the bundled weak chains
from local smoothness and establishes the needed test integrability.
This construction asserts no factorial or uniform-in-order norm estimate. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

def complexDirectionalWordDeriv {ι : Type} (dirs : ι → Space κ)
    (s : Space κ → ℂ) : List ι → Space κ → ℂ
  | [] => s
  | i :: w => fun p => fderiv ℝ (complexDirectionalWordDeriv dirs s w) p (dirs i)

theorem complexDirectionalWordDeriv_contDiffOn {ι : Type} (dirs : ι → Space κ)
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω) {s : Space κ → ℂ}
    (hs : ContDiffOn ℝ ∞ s Ω) (w : List ι) :
    ContDiffOn ℝ ∞ (complexDirectionalWordDeriv dirs s w) Ω := by
  induction w with
  | nil => exact hs
  | cons i w ih =>
    intro p hp
    exact (local_contDiffAt_directional_derivative
      (ih.contDiffAt (hΩ.mem_nhds hp)) (dirs i)).contDiffWithinAt

theorem complex_smooth_local_weak_directional
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω) {s : Space κ → ℂ}
    (hs : ContDiffOn ℝ ∞ s Ω) (v : Space κ) :
    ProductLocalWeakDirectional Ω s (fun p => fderiv ℝ s p v) v := by
  letI : (volume : Measure (Space κ)).IsAddHaarMeasure :=
    euclidean_product_volume_isAddHaar (ι := Fin 4) (κ := κ)
  have hDs : ContDiffOn ℝ ∞ (fun p => fderiv ℝ s p v) Ω := by
    intro p hp
    exact (local_contDiffAt_directional_derivative
      (hs.contDiffAt (hΩ.mem_nhds hp)) v).contDiffWithinAt
  refine ⟨product_continuousOn_locallyL2 hs.continuousOn,
    product_continuousOn_locallyL2 hDs.continuousOn,?_⟩
  intro φ hφ hc hφΩ
  have hDφ : ContDiff ℝ ∞ (fun p => fderiv ℝ φ p v) :=
    (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hiD : Integrable (fun p => fderiv ℝ φ p v • s p) volume :=
    local_smooth_test_smul_integrable hDφ (hc.fderiv_apply ℝ v)
      (fun p hp => hs.contDiffAt
        (hΩ.mem_nhds (hφΩ ((tsupport_fderiv_apply_subset ℝ v) hp))))
  have hiDs : Integrable (fun p => φ p • fderiv ℝ s p v) volume :=
    local_smooth_test_smul_integrable hφ hc
      (fun p hp => hDs.contDiffAt (hΩ.mem_nhds (hφΩ hp)))
  have hi : Integrable (fun p => φ p • s p) volume :=
    local_smooth_test_smul_integrable hφ hc
      (fun p hp => hs.contDiffAt (hΩ.mem_nhds (hφΩ hp)))
  exact integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (μ := volume) (f := φ) (g := s) (v := v) hiD hiDs hi
    (fun p _ => hφ.differentiable (by simp) p)
    (fun p hp => (hs.contDiffAt (hΩ.mem_nhds (hφΩ hp))).differentiableAt (by simp))

def complexMixedSourceWord (s : Space κ → ℂ)
    (ya : List (Fin 4)) (tb : List κ) : Space κ → ℂ :=
  complexDirectionalWordDeriv yDir (complexDirectionalWordDeriv tDir s tb) ya

theorem complexMixedSourceWord_nil (s : Space κ → ℂ) :
    complexMixedSourceWord s [] [] = s := rfl

theorem complexMixedSourceWord_contDiffOn
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω) {s : Space κ → ℂ}
    (hs : ContDiffOn ℝ ∞ s Ω) (ya : List (Fin 4)) (tb : List κ) :
    ContDiffOn ℝ ∞ (complexMixedSourceWord s ya tb) Ω :=
  complexDirectionalWordDeriv_contDiffOn yDir hΩ
    (complexDirectionalWordDeriv_contDiffOn tDir hΩ hs tb) ya

theorem complexMixedSourceWord_locallyL2
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω) {s : Space κ → ℂ}
    (hs : ContDiffOn ℝ ∞ s Ω) (ya : List (Fin 4)) (tb : List κ) :
    ProductLocallyL2On (complexMixedSourceWord s ya tb) Ω :=
  product_continuousOn_locallyL2 (complexMixedSourceWord_contDiffOn hΩ hs ya tb).continuousOn

theorem complexMixedSourceWord_localY
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω) {s : Space κ → ℂ}
    (hs : ContDiffOn ℝ ∞ s Ω) (ya : List (Fin 4)) (tb : List κ) (i : Fin 4) :
    ProductLocalWeakDirectional Ω (complexMixedSourceWord s ya tb)
      (complexMixedSourceWord s (i :: ya) tb) (yDir i) :=
  complex_smooth_local_weak_directional hΩ (complexMixedSourceWord_contDiffOn hΩ hs ya tb) (yDir i)

theorem complexMixedSourceWord_localT_zero
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω) {s : Space κ → ℂ}
    (hs : ContDiffOn ℝ ∞ s Ω) (tb : List κ) (j : κ) :
    ProductLocalWeakDirectional Ω (complexMixedSourceWord s [] tb)
      (complexMixedSourceWord s [] (j :: tb)) (tDir j) :=
  complex_smooth_local_weak_directional hΩ
    (complexDirectionalWordDeriv_contDiffOn tDir hΩ hs tb) (tDir j)

end TheoremT.Continuum.WeakGrushin
