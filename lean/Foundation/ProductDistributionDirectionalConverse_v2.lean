import GenericDistributionDirectionalConverse_v1
import ProductWeakDirectionalLift_v1

/-!
Version 2 reuses canonical weak-jet transport from ProductWeakDirectionalLift_v1.
The actual first weak L2 derivative on the ordinary Cartesian product is
equivalent to the tempered derivative of its exact Euclidean-copy lift.
All tests, derivatives, and Lebesgue measures are those already defined;
the converse requires no derivative-existence or density hypothesis.
-/
noncomputable section
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv ContDiff
namespace TheoremT.Continuum

variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

theorem distribution_directional_of_weakProductL2Directional
    {f g : Lp ℂ 2 (volume : Measure (Y × T))} {v : Y × T}
    (h : WeakProductL2Directional f g v) :
    ∂_{WithLp.toLp 2 v} (productEuclideanLift f : 𝓢'(WithLp 2 (Y × T), ℂ)) =
      (productEuclideanLift g : 𝓢'(WithLp 2 (Y × T), ℂ)) :=
  distribution_directional_of_weakL2Directional (weakL2Directional_productEuclideanLift h)

theorem weakProductL2Directional_iff_distribution
    {f g : Lp ℂ 2 (volume : Measure (Y × T))} {v : Y × T} :
    WeakProductL2Directional f g v ↔
    ∂_{WithLp.toLp 2 v} (productEuclideanLift f : 𝓢'(WithLp 2 (Y × T), ℂ)) =
      (productEuclideanLift g : 𝓢'(WithLp 2 (Y × T), ℂ)) := by
  refine ⟨distribution_directional_of_weakProductL2Directional, ?_⟩
  intro h
  have hh := weakProductL2Directional_of_euclidean (weakL2Directional_of_distribution h)
  simpa only [productEuclideanUnlift_lift] using hh

#print axioms distribution_directional_of_weakProductL2Directional
#print axioms weakProductL2Directional_iff_distribution
end TheoremT.Continuum
