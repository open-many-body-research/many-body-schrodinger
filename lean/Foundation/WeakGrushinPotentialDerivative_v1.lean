import WeakGrushinPotentialDerivativeTest_v1
import WeakGrushinPotentialDerivativeLocalL2_v1

/-! Actual local spectator Leibniz rule with all local L2 and test
integrability obligations discharged. The potential is only smooth on the
open coefficient domain; no global L2 product hypothesis is introduced. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum
variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

theorem weakProduct_spectator_local_potential_leibniz
    {f d : Lp ℂ 2 (volume : Measure (Y × T))} {v : T}
    (hd : WeakProductL2Directional f d (0,v))
    {Ω : Set (Y × T)} (hΩ : IsOpen Ω)
    {B : Y × T → ℝ} (hB : ContDiffOn ℝ ∞ B Ω) :
    ProductLocallyL2On (fun p => B p • f p) Ω ∧
    ProductLocallyL2On (fun p => B p • d p + fderiv ℝ B p (0,v) • f p) Ω ∧
    ∀ φ : Y × T → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      Integrable (fun p => φ p • (B p • d p + fderiv ℝ B p (0,v) • f p)) volume ∧
      Integrable (fun p => fderiv ℝ φ p (0,v) • (B p • f p)) volume ∧
      (∫ p, φ p • (B p • d p + fderiv ℝ B p (0,v) • f p)) =
        -(∫ p, fderiv ℝ φ p (0,v) • (B p • f p)) := by
  refine ⟨product_smooth_coefficient_locallyL2 hΩ hB f,
    product_spectator_potential_leibniz_locallyL2 hΩ hB f d v,?_⟩
  intro φ hφ hc hs
  exact weakProduct_directional_local_potential_test hd hΩ hB hφ hc hs

#print axioms weakProduct_spectator_local_potential_leibniz
end TheoremT.Continuum
