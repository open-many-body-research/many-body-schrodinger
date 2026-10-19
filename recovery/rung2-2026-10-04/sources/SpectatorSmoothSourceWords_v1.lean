import SpectatorWordWeakLeibniz_v1
import ProductContinuousLocalL2_v1
import LocalSecondDerivativeIBP_v1
import CompactSpectatorCutoffEnergy_v1

/-! Actual weak spectator words of a smooth real coefficient times a fixed
complex amplitude. Local integration by parts supplies the constant weak
derivative; the raw local product rule then identifies every source word.
The amplitude has its displayed sign, with no change to the source formula. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem localSpectatorD_constant (Ω : Set (Space κ)) (z : ℂ) (j : κ) :
    LocalSpectatorD Ω (fun _ => z) (fun _ => 0) j := by
  letI : (volume : Measure (Space κ)).IsAddHaarMeasure :=
    euclidean_product_volume_isAddHaar (ι := Fin 4) (κ := κ)
  intro φ hφ hc _hs
  have hDφ : ContDiff ℝ ∞ (fun p => fderiv ℝ φ p (tDir j)) :=
    (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hiD : Integrable (fun p => fderiv ℝ φ p (tDir j) • z) volume :=
    local_smooth_test_smul_integrable hDφ (hc.fderiv_apply ℝ (tDir j))
      (fun _ _ => contDiffAt_const)
  have hi : Integrable (fun p => φ p • z) volume :=
    local_smooth_test_smul_integrable hφ hc (fun _ _ => contDiffAt_const)
  have hi0 : Integrable
      (fun p => φ p • fderiv ℝ (fun _ : Space κ => z) p (tDir j)) volume := by simp
  have he := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (μ := volume) (f := φ) (g := fun _ : Space κ => z) (v := tDir j)
    hiD hi0 hi (fun p _ => hφ.differentiable (by simp) p)
    (fun _ _ => differentiableAt_const z)
  simpa using he

theorem smooth_spectator_source_words
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω) {b : Space κ → ℝ}
    (hb : ContDiffOn ℝ ∞ b Ω) (z : ℂ) :
    (∀ w, ProductLocallyL2On (fun p => spectatorWordDeriv b w p • z) Ω) ∧
    ∀ w j, LocalSpectatorD Ω (fun p => spectatorWordDeriv b w p • z)
      (fun p => spectatorWordDeriv b (j :: w) p • z) j := by
  have hz : ProductLocallyL2On (fun _ : Space κ => z) Ω :=
    product_continuousOn_locallyL2 continuous_const.continuousOn
  have hzero : ProductLocallyL2On (fun _ : Space κ => (0 : ℂ)) Ω :=
    product_continuousOn_locallyL2 continuous_const.continuousOn
  refine ⟨fun w => product_smooth_coefficient_locallyL2_raw hΩ
    (spectatorWordDeriv_contDiffOn hΩ hb w) hz, ?_⟩
  intro w j
  have he := product_local_weak_directional_leibniz hΩ
    (spectatorWordDeriv_contDiffOn hΩ hb w) hz hzero (localSpectatorD_constant Ω z j)
  intro φ hφ hc hs
  simpa only [smul_zero,zero_add,spectatorWordDeriv] using (he.2.2 φ hφ hc hs).2.2

#print axioms localSpectatorD_constant
#print axioms smooth_spectator_source_words
end TheoremT.Continuum.WeakGrushin
