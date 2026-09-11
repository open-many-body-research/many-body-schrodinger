import PartialSpectatorKernelJets_v1
import CompactPartialIntegralSupport_v1
import ProductWeakEllipticGain_v1
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ContDiff
namespace TheoremT.Continuum
variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

theorem product_spectator_test_fderiv {φ : Y × T → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (y : Y) (t v : T) :
    fderiv ℝ (fun q => φ (y,q)) t v = fderiv ℝ φ (y,t) (0,v) := by
  have hh := (hφ.differentiable (by simp) (y,t)).hasFDerivAt.comp t
    ((hasFDerivAt_const y t).prodMk (hasFDerivAt_id t))
  change HasFDerivAt (fun q => φ (y,q)) _ t at hh
  rw [hh.fderiv]
  rfl

theorem spectatorFiberJet_fiber_contDiff {G : Y × T → ℂ} (y : Y)
    (hG : ContDiff ℝ ∞ (fun t => G (y,t))) (vs : List T) :
    ContDiff ℝ ∞ (fun t => spectatorFiberJet G vs (y,t)) := by
  induction vs with
  | nil => exact hG
  | cons v vs ih => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

theorem spectator_fiber_smooth_weak_test
    {G : Y × T → ℂ} (v : T) (hG : MemLp G 2 (volume : Measure (Y × T)))
    (hD : MemLp (spectatorFiberDirectional G v) 2 (volume : Measure (Y × T)))
    (hs : ∀ᵐ y ∂(volume : Measure Y), ContDiff ℝ ∞ (fun t => G (y,t)))
    {φ : Y × T → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ p, φ p • spectatorFiberDirectional G v p) =
      -(∫ p, fderiv ℝ φ p (0,v) • G p) := by
  have hi0 := (hG.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport hφ.continuous hc
  have hi1 := (hD.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport hφ.continuous hc
  have hφD : Continuous (fun p => fderiv ℝ φ p (0,v)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hi2 := (hG.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
    hφD (hc.fderiv_apply ℝ (0,v))
  change (∫ p, φ p • spectatorFiberDirectional G v p ∂(volume : Measure Y).prod volume) =
    -(∫ p, fderiv ℝ φ p (0,v) • G p ∂(volume : Measure Y).prod volume)
  rw [integral_prod _ hi1,integral_prod _ hi2,← integral_neg]
  apply integral_congr_ae
  filter_upwards [hs,hi0.prod_right_ae,hi1.prod_right_ae,hi2.prod_right_ae] with y hy h0 h1 h2
  have ht : ContDiff ℝ ∞ (fun t => φ (y,t)) := hφ.comp (contDiff_const.prodMk contDiff_id)
  have hchain := product_spectator_test_fderiv hφ y
  simp_rw [← hchain] at h2 ⊢
  exact integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable h2 h1 h0
    (fun t _ => ht.differentiable (by simp) t) (fun t _ => hy.differentiable (by simp) t)

theorem partialSpectatorConvolution_fiber_jets_weak_test
    {K : T → ℝ} {G : Y × T → ℂ} (hK : ContDiff ℝ ∞ K) (hcK : HasCompactSupport K)
    (hG : MemLp G 2 (volume : Measure (Y × T))) (vs : List T) (v : T)
    {φ : Y × T → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ p, φ p • spectatorFiberJet (partialSpectatorConvolution (ν := volume) K G) (v::vs) p) =
      -(∫ p, fderiv ℝ φ p (0,v) • spectatorFiberJet (partialSpectatorConvolution (ν := volume) K G) vs p) := by
  apply spectator_fiber_smooth_weak_test v
    (partialSpectatorConvolution_fiber_jet_memLp hK hcK hG vs)
    (partialSpectatorConvolution_fiber_jet_memLp hK hcK hG (v::vs)) _ hφ hc
  filter_upwards [partialSpectatorConvolution_smooth_fiber_ae hK hcK hG] with y hy
  exact spectatorFiberJet_fiber_contDiff y hy vs

#print axioms product_spectator_test_fderiv
#print axioms spectatorFiberJet_fiber_contDiff
#print axioms spectator_fiber_smooth_weak_test
#print axioms partialSpectatorConvolution_fiber_jets_weak_test
end TheoremT.Continuum
