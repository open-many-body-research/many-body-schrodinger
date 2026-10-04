import SpectatorSmoothSourceRegionBudget_v1
import ProductDirectionalWordLeibniz_v1

/-! Actual mixed Y/T words of a smooth real coefficient times a fixed complex
amplitude. Every needed weak derivative is proved by local integration by
parts and the genuine local product rule. No solution derivatives are inputs. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem productLocalWeakDirectional_constant
    (Ω : Set (Space κ)) (z : ℂ) (v : Space κ) :
    ProductLocalWeakDirectional Ω (fun _ => z) (fun _ => 0) v := by
  letI : (volume : Measure (Space κ)).IsAddHaarMeasure :=
    euclidean_product_volume_isAddHaar (ι := Fin 4) (κ := κ)
  refine ⟨product_continuousOn_locallyL2 continuous_const.continuousOn,
    product_continuousOn_locallyL2 continuous_const.continuousOn,?_⟩
  intro φ hφ hc _hs
  have hDφ : ContDiff ℝ ∞ (fun p => fderiv ℝ φ p v) :=
    (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hiD : Integrable (fun p => fderiv ℝ φ p v • z) volume :=
    local_smooth_test_smul_integrable hDφ (hc.fderiv_apply ℝ v)
      (fun _ _ => contDiffAt_const)
  have hi : Integrable (fun p => φ p • z) volume :=
    local_smooth_test_smul_integrable hφ hc (fun _ _ => contDiffAt_const)
  have hi0 : Integrable (fun p => φ p • fderiv ℝ (fun _ : Space κ => z) p v) volume := by simp
  have he := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (μ := volume) (f := φ) (g := fun _ : Space κ => z) (v := v)
    hiD hi0 hi (fun p _ => hφ.differentiable (by simp) p)
    (fun _ _ => differentiableAt_const z)
  simpa using he

theorem smooth_mixed_source_words {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {b : Space κ → ℝ} (hb : ContDiffOn ℝ ∞ b Ω) (z : ℂ) :
    (∀ a t, ProductLocallyL2On
      (fun p => directionalWordDeriv yDir (spectatorWordDeriv b t) a p • z) Ω) ∧
    (∀ a t i, ProductLocalWeakDirectional Ω
      (fun p => directionalWordDeriv yDir (spectatorWordDeriv b t) a p • z)
      (fun p => directionalWordDeriv yDir (spectatorWordDeriv b t) (i::a) p • z) (yDir i)) ∧
    ∀ t j, ProductLocalWeakDirectional Ω
      (fun p => directionalWordDeriv yDir (spectatorWordDeriv b t) [] p • z)
      (fun p => directionalWordDeriv yDir (spectatorWordDeriv b (j::t)) [] p • z) (tDir j) := by
  have hcoeff (a : List (Fin 4)) (t : List κ) :
      ContDiffOn ℝ ∞ (directionalWordDeriv yDir (spectatorWordDeriv b t) a) Ω :=
    directionalWordDeriv_contDiffOn yDir hΩ (spectatorWordDeriv_contDiffOn hΩ hb t) a
  refine ⟨?_,?_,?_⟩
  · intro a t
    exact product_smooth_coefficient_locallyL2_raw hΩ (hcoeff a t)
      (product_continuousOn_locallyL2 continuous_const.continuousOn)
  · intro a t i
    have hD := (productLocalWeakDirectional_constant Ω z (yDir i)).smooth_smul hΩ (hcoeff a t)
    simpa only [smul_zero,zero_add,directionalWordDeriv] using hD
  · intro t j
    have hD := (productLocalWeakDirectional_constant Ω z (tDir j)).smooth_smul hΩ
      (spectatorWordDeriv_contDiffOn hΩ hb t)
    simpa only [smul_zero,zero_add,directionalWordDeriv,spectatorWordDeriv] using hD

theorem smooth_mixed_source_region_budget {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {b : Space κ → ℝ} (hb : ContDiffOn ℝ ∞ b Ω) (z : ℂ)
    (a : List (Fin 4)) (t : List κ) {S : Set (Space κ)}
    (hS : MeasurableSet S) (hSΩ : S ⊆ Ω) (hfinite : volume S < ⊤)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ p ∈ S, |directionalWordDeriv yDir (spectatorWordDeriv b t) a p| ≤ C) :
    RegionL2Budget
      (fun p => directionalWordDeriv yDir (spectatorWordDeriv b t) a p • z) S
      (C^2*‖z‖^2*(volume S).toReal) := by
  have hcoeff := directionalWordDeriv_contDiffOn yDir hΩ
    (spectatorWordDeriv_contDiffOn hΩ hb t) a
  exact smooth_spectator_source_region_budget hΩ hcoeff z [] hS hSΩ hfinite hC hbound

#print axioms productLocalWeakDirectional_constant
#print axioms smooth_mixed_source_words
#print axioms smooth_mixed_source_region_budget
end TheoremT.Continuum.WeakGrushin
