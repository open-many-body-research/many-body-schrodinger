import CoulombKSPhysicalH12All_v1
import SmoothTransitionExplicitBounds_v1
import PhysicalCoordinateMultiIndexWeakH12_v1

/-! Numerical-cutoff finite weak H12 initialization for either nuclear chart.
The full multiindex family and compact-test identities use the selected
physical spectator domain and its genuine product Lebesgue measure. -/
noncomputable section
open MeasureTheory Metric
open scoped ContDiff NNReal BigOperators
namespace TheoremT.Continuum
open WeakGrushin

theorem scalar_coulomb_nuclear_physical_h12_multiindex (i : Fin 2) (Z E : ℝ) :
    ∃ KT KY QY : ℝ, 1 ≤ KT ∧ 1 ≤ KY ∧ 0 ≤ QY ∧
      0 ≤ ksH12MixedBudgetAt i 4 96 14016 KT KY QY ∧
      ∀ t0 : SpectatorConfiguration i, ‖t0‖ = 1 →
      ∀ f : SpatialL2 2, scalarHamiltonianGraph 2 Z f ((E : ℂ) • f) →
      ∀ g : Configuration 2 → ℂ, Continuous g → (f : Configuration 2 → ℂ) =ᵐ[volume] g →
      ∀ (L : ℝ≥0) (R ε : ℝ), LipschitzOnWith L g (ball 0 R) →
        0 < ε → ε ≤ min 1 (R/4) →
        let Ω := (physicalSpectatorReindexAt i) ⁻¹'
          rectangularOpenBox (0,(twoElectronSpectatorPositionEquiv i) t0) (1/128) (1/128)
        let u := originScaledDifference g ε ∘ (nuclearKSLift i)
        let W := ((L : ℝ)^2+‖g 0‖^2)*ksH12MixedBudgetAt i 4 96 14016 KT KY QY
        ProductCoordinateWeakHk Ω u 12 W ∧
        ∃ V : boundedMultiIndex 7 12 → (NuclearKSSpace i) → ℂ,
          V h12ZeroMultiIndex = u ∧
          (∀ alpha, RegionL2Budget (V alpha) Ω W) ∧
          physicalH12RegionL2Sum i V Ω ≤ 50388 * W ∧
          ∀ alpha (φ : (NuclearKSSpace i) → ℝ), ContDiff ℝ ∞ φ →
            HasCompactSupport φ → tsupport φ ⊆ Ω →
            Integrable (fun p => φ p • V alpha p) ∧
            Integrable (fun p => productCoordinateTestWord
              (h12PhysicalCoordinateWord i alpha) φ p • u p) ∧
            (∫ p, φ p • V alpha p) =
              ((-1 : ℝ)^(∑ k, alpha.val k)) •
                (∫ p, productCoordinateTestWord
                  (h12PhysicalCoordinateWord i alpha) φ p • u p) := by
  obtain ⟨KT,KY,QY,hKT,hKY,hQY,hC,hgain⟩ :=
    scalar_coulomb_nuclear_physical_coordinate_h12 i Z E 96 14016
      smoothTransition_deriv_abs_le_ninety_six
      smoothTransition_second_deriv_abs_le_fourteen_thousand_sixteen
  refine ⟨KT,KY,QY,hKT,hKY,hQY,hC,?_⟩
  intro t0 ht0 f hgraph g hg hfg L R ε hLip hε hεlim
  have hu := hgain t0 ht0 f hgraph g hg hfg L R ε hLip hε hεlim
  exact ⟨hu,physical_coordinateWeakHk_multiIndex_extraction i hu⟩

end TheoremT.Continuum
