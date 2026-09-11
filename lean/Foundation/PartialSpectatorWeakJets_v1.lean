import SpectatorFiberWeakTest_v1

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ContDiff
namespace TheoremT.Continuum
variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

def partialSpectatorJetLp {K : T → ℝ} {G : Y × T → ℂ}
    (hK : ContDiff ℝ ∞ K) (hcK : HasCompactSupport K)
    (hG : MemLp G 2 (volume : Measure (Y × T))) (vs : List T) :
    Lp ℂ 2 (volume : Measure (Y × T)) :=
  (partialSpectatorConvolution_fiber_jet_memLp hK hcK hG vs).toLp
    (spectatorFiberJet (partialSpectatorConvolution (ν := volume) K G) vs)

theorem partialSpectatorJetLp_ae {K : T → ℝ} {G : Y × T → ℂ}
    (hK : ContDiff ℝ ∞ K) (hcK : HasCompactSupport K)
    (hG : MemLp G 2 (volume : Measure (Y × T))) (vs : List T) :
    partialSpectatorJetLp hK hcK hG vs =ᵐ[volume]
      spectatorFiberJet (partialSpectatorConvolution (ν := volume) K G) vs :=
  (partialSpectatorConvolution_fiber_jet_memLp hK hcK hG vs).coeFn_toLp

theorem partialSpectatorJetLp_weak_derivative {K : T → ℝ} {G : Y × T → ℂ}
    (hK : ContDiff ℝ ∞ K) (hcK : HasCompactSupport K)
    (hG : MemLp G 2 (volume : Measure (Y × T))) (vs : List T) (v : T) :
    WeakProductL2Directional (partialSpectatorJetLp hK hcK hG vs)
      (partialSpectatorJetLp hK hcK hG (v::vs)) (0,v) := by
  intro φ hφ hc
  have he1 : (∫ p, φ p • partialSpectatorJetLp hK hcK hG (v::vs) p) =
      ∫ p, φ p • spectatorFiberJet (partialSpectatorConvolution (ν := volume) K G) (v::vs) p := by
    apply integral_congr_ae
    filter_upwards [partialSpectatorJetLp_ae hK hcK hG (v::vs)] with p hp
    rw [hp]
  have he0 : (∫ p, fderiv ℝ φ p (0,v) • partialSpectatorJetLp hK hcK hG vs p) =
      ∫ p, fderiv ℝ φ p (0,v) • spectatorFiberJet (partialSpectatorConvolution (ν := volume) K G) vs p := by
    apply integral_congr_ae
    filter_upwards [partialSpectatorJetLp_ae hK hcK hG vs] with p hp
    rw [hp]
  rw [he1,he0]
  exact partialSpectatorConvolution_fiber_jets_weak_test hK hcK hG vs v hφ hc

theorem partialSpectatorJetLp_norm_le {K : T → ℝ} {G : Y × T → ℂ}
    (hK : ContDiff ℝ ∞ K) (hcK : HasCompactSupport K)
    (hG : MemLp G 2 (volume : Measure (Y × T))) (vs : List T) :
    ‖partialSpectatorJetLp hK hcK hG vs‖ ≤
      (∫ s, ‖spectatorKernelJet K vs s‖) * ‖hG.toLp G‖ := by
  have hi := partialSpectatorConvolution_fiber_jet_integral_sq_le hK hcK hG vs
  have hGp : MemLp G 2 ((volume : Measure Y).prod (volume : Measure T)) := hG
  rw [← actual_l2_toLp_norm_sq_integral (partialSpectatorConvolution_fiber_jet_memLp hK hcK hG vs),
    ← actual_l2_toLp_norm_sq_integral hGp] at hi
  change ‖partialSpectatorJetLp hK hcK hG vs‖^2 ≤ _ at hi
  have hp := mul_nonneg (integral_nonneg (μ := (volume : Measure T))
    (fun s => norm_nonneg (spectatorKernelJet K vs s))) (norm_nonneg (hG.toLp G))
  nlinarith only [hi,hp,norm_nonneg (partialSpectatorJetLp hK hcK hG vs)]

#print axioms partialSpectatorJetLp
#print axioms partialSpectatorJetLp_ae
#print axioms partialSpectatorJetLp_weak_derivative
#print axioms partialSpectatorJetLp_norm_le
end TheoremT.Continuum
