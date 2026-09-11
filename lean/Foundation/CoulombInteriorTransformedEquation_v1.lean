import CoulombTransformedEquation_v1
import ConstantOpenDerivative_v1

/-! Homogeneous transformed weak equation on every centered ball, including
every nuclear/pair collision stratum in that ball. No eigensolution existence
or spectral isolation is assumed or concluded. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace TheoremT.Continuum

theorem scalar_coulomb_interior_transformed_equation {N : ℕ} {Z E : ℝ}
    {f : SpatialL2 N} (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    {R : ℝ} (hR : 0 < R) :
    ∃ g : SpatialL2 N, ∃ a : Coordinate N → SpatialL2 N,
      ∃ b : Coordinate N → Coordinate N → SpatialL2 N,
        HasH2 g ∧ (∀ k, WeakPartial g (a k) k) ∧ (∀ k l, WeakPartial (a k) (b k l) l) ∧
        ∀ᵐ x ∂volume.restrict (Metric.ball 0 R),
          g x=Real.exp (-coulombCusp N Z x) • f x ∧
          (∑ k, b k k x) = -2*(∑ k, (coulombCuspGradient N Z (coordinateVector k) x : ℂ)*a k x)-
            (((∑ k, (coulombCuspGradient N Z (coordinateVector k) x)^2)+2*E : ℝ) : ℂ)*g x := by
  let χ := scaledCutoff N R
  have hχ : ContDiff ℝ ∞ χ := scaledCutoff_contDiff N R
  have hc : HasCompactSupport χ := scaledCutoff_hasCompactSupport N hR
  have h1 : ∀ x ∈ Metric.ball (0 : Configuration N) R, χ x=1 := by
    intro x hx
    exact scaledCutoff_eq_one hR ((mem_ball_zero_iff.mp hx).le)
  obtain ⟨d,g,a,b,hd,hg2,hga,hab,hv,heq⟩ := scalar_coulomb_localized_transformed_equation hg hχ hc
  refine ⟨g,a,b,hg2,hga,hab,?_⟩
  filter_upwards [ae_restrict_of_ae hv,ae_restrict_of_ae heq,
    ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx he hxB
  have hD := fderiv_zero_of_constant_open Metric.isOpen_ball h1 hxB
  have hL := realTestLaplacian_zero_of_constant_open Metric.isOpen_ball h1 hxB
  constructor
  · simpa only [h1 x hxB,one_mul] using hx
  · simpa only [hD,hL,ContinuousLinearMap.zero_apply,Complex.ofReal_zero,zero_mul,
      Finset.sum_const_zero,add_zero,mul_zero] using he

#print axioms scalar_coulomb_interior_transformed_equation
end TheoremT.Continuum
