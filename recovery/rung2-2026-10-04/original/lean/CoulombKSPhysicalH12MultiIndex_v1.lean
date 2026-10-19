import CoulombKSPhysicalH12_v1
import SmoothTransitionExplicitBounds_v1
import PhysicalCoordinateMultiIndexWeakH12_v1

/-! Physical order-twelve scalar initialization with the proved numerical
cutoff derivative bounds 96 and 14016. The genuine multiindex family remains
on the physical product domain, with the exact 50388 summand aggregate.
The coefficient constants are chosen before center, solution and dilation.
This is a finite weak derivative reserve, not an all-order analytic claim. -/
noncomputable section
open MeasureTheory Metric
open scoped ContDiff NNReal BigOperators
namespace TheoremT.Continuum
open WeakGrushin

theorem scalar_coulomb_nuclear_zero_physical_h12_multiindex (Z E : ℝ) :
    ∃ KT KY QY : ℝ, 1 ≤ KT ∧ 1 ≤ KY ∧ 0 ≤ QY ∧
      0 ≤ ksH12MixedBudget 4 96 14016 KT KY QY ∧
      ∀ t0 : SpectatorConfiguration (0 : Fin 2), ‖t0‖ = 1 →
      ∀ f : SpatialL2 2, scalarHamiltonianGraph 2 Z f ((E : ℂ) • f) →
      ∀ g : Configuration 2 → ℂ, Continuous g → (f : Configuration 2 → ℂ) =ᵐ[volume] g →
      ∀ (L : ℝ≥0) (R ε : ℝ), LipschitzOnWith L g (ball 0 R) →
        0 < ε → ε ≤ min 1 (R/4) →
        let Ω := physicalSpectatorReindex ⁻¹'
          rectangularOpenBox (0,pairCenterEquiv t0) (1/128) (1/128)
        let u := originScaledDifference g ε ∘ (nuclearKSLift (0 : Fin 2))
        let W := ((L : ℝ)^2+‖g 0‖^2)*ksH12MixedBudget 4 96 14016 KT KY QY
        ProductCoordinateWeakHk Ω u 12 W ∧
        ∃ V : boundedMultiIndex 7 12 → PairKSSpace → ℂ,
          V h12ZeroMultiIndex = u ∧
          (∀ alpha, RegionL2Budget (V alpha) Ω W) ∧
          physicalH12RegionL2Sum (0 : Fin 2) V Ω ≤ 50388 * W ∧
          ∀ alpha (φ : PairKSSpace → ℝ), ContDiff ℝ ∞ φ →
            HasCompactSupport φ → tsupport φ ⊆ Ω →
            Integrable (fun p => φ p • V alpha p) ∧
            Integrable (fun p => productCoordinateTestWord
              (h12PhysicalCoordinateWord (0 : Fin 2) alpha) φ p • u p) ∧
            (∫ p, φ p • V alpha p) =
              ((-1 : ℝ)^(∑ k, alpha.val k)) •
                (∫ p, productCoordinateTestWord
                  (h12PhysicalCoordinateWord (0 : Fin 2) alpha) φ p • u p) := by
  obtain ⟨KT,KY,QY,hKT,hKY,hQY,hC,hgain⟩ :=
    scalar_coulomb_nuclear_zero_physical_coordinate_h12 Z E 96 14016
      smoothTransition_deriv_abs_le_ninety_six
      smoothTransition_second_deriv_abs_le_fourteen_thousand_sixteen
  refine ⟨KT,KY,QY,hKT,hKY,hQY,hC,?_⟩
  intro t0 ht0 f hgraph g hg hfg L R ε hLip hε hεlim
  have hu := hgain t0 ht0 f hgraph g hg hfg L R ε hLip hε hεlim
  exact ⟨hu,physical_coordinateWeakHk_multiIndex_extraction (0 : Fin 2) hu⟩

theorem scalar_coulomb_pair_physical_h12_multiindex (Z E : ℝ) :
    ∃ KT KY QY : ℝ, 1 ≤ KT ∧ 1 ≤ KY ∧ 0 ≤ QY ∧
      0 ≤ ksH12MixedBudget 1 96 14016 KT KY QY ∧
      ∀ t0 : SpectatorConfiguration (0 : Fin 2), ‖t0‖ = 1 →
      ∀ f : SpatialL2 2, scalarHamiltonianGraph 2 Z f ((E : ℂ) • f) →
      ∀ g : Configuration 2 → ℂ, Continuous g → (f : Configuration 2 → ℂ) =ᵐ[volume] g →
      ∀ (L : ℝ≥0) (R ε : ℝ), LipschitzOnWith L g (ball 0 R) →
        0 < ε → ε ≤ min 1 (R/4) →
        let Ω := physicalSpectatorReindex ⁻¹'
          rectangularOpenBox (0,pairCenterEquiv t0) (1/128) (1/128)
        let u := originScaledDifference g ε ∘ (pairKSLift)
        let W := ((L : ℝ)^2+‖g 0‖^2)*ksH12MixedBudget 1 96 14016 KT KY QY
        ProductCoordinateWeakHk Ω u 12 W ∧
        ∃ V : boundedMultiIndex 7 12 → PairKSSpace → ℂ,
          V h12ZeroMultiIndex = u ∧
          (∀ alpha, RegionL2Budget (V alpha) Ω W) ∧
          physicalH12RegionL2Sum (0 : Fin 2) V Ω ≤ 50388 * W ∧
          ∀ alpha (φ : PairKSSpace → ℝ), ContDiff ℝ ∞ φ →
            HasCompactSupport φ → tsupport φ ⊆ Ω →
            Integrable (fun p => φ p • V alpha p) ∧
            Integrable (fun p => productCoordinateTestWord
              (h12PhysicalCoordinateWord (0 : Fin 2) alpha) φ p • u p) ∧
            (∫ p, φ p • V alpha p) =
              ((-1 : ℝ)^(∑ k, alpha.val k)) •
                (∫ p, productCoordinateTestWord
                  (h12PhysicalCoordinateWord (0 : Fin 2) alpha) φ p • u p) := by
  obtain ⟨KT,KY,QY,hKT,hKY,hQY,hC,hgain⟩ :=
    scalar_coulomb_pair_physical_coordinate_h12 Z E 96 14016
      smoothTransition_deriv_abs_le_ninety_six
      smoothTransition_second_deriv_abs_le_fourteen_thousand_sixteen
  refine ⟨KT,KY,QY,hKT,hKY,hQY,hC,?_⟩
  intro t0 ht0 f hgraph g hg hfg L R ε hLip hε hεlim
  have hu := hgain t0 ht0 f hgraph g hg hfg L R ε hLip hε hεlim
  exact ⟨hu,physical_coordinateWeakHk_multiIndex_extraction (0 : Fin 2) hu⟩

end TheoremT.Continuum
