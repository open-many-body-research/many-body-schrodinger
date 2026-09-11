import ProductDistributionDirectionalConverse_v2
import LpDistributionIdentification_v1

/-! Uniqueness of actual product-space weak derivative witnesses. The proof
uses the exact Euclidean-copy distribution identity and injectivity of the
Lebesgue L2 embedding in tempered distributions. No regularity or convergence
assumption is introduced. -/
noncomputable section
open MeasureTheory
open scoped SchwartzMap
namespace TheoremT.Continuum

variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

theorem weakProductL2Directional_unique
    {f g h : Lp ℂ 2 (volume : Measure (Y × T))} {v : Y × T}
    (hg : WeakProductL2Directional f g v)
    (hh : WeakProductL2Directional f h v) : g = h := by
  apply productEuclideanLift.injective
  apply Lp.ext
  apply ae_eq_of_Lp_temperedDistribution_eq
  exact (distribution_directional_of_weakProductL2Directional hg).symm.trans
    (distribution_directional_of_weakProductL2Directional hh)

theorem weakProductL2SecondDirectional_unique
    {f d₁ d₂ e₁ e₂ : Lp ℂ 2 (volume : Measure (Y × T))} {v w : Y × T}
    (hd₁ : WeakProductL2Directional f d₁ v)
    (hd₂ : WeakProductL2Directional f d₂ v)
    (he₁ : WeakProductL2Directional d₁ e₁ w)
    (he₂ : WeakProductL2Directional d₂ e₂ w) : e₁ = e₂ := by
  have hd : d₁ = d₂ := weakProductL2Directional_unique hd₁ hd₂
  subst d₂
  exact weakProductL2Directional_unique he₁ he₂

#print axioms weakProductL2Directional_unique
#print axioms weakProductL2SecondDirectional_unique
end TheoremT.Continuum
