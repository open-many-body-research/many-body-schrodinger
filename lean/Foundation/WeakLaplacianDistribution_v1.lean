import ActualH2DomainEquivalence_v1

/-! The exact distributional output of supplied diagonal weak derivatives.
This permits norm and shifted-equation arguments on the original graph. -/

noncomputable section
open MeasureTheory TemperedDistribution
open scoped SchwartzMap Laplacian LineDeriv BigOperators

namespace TheoremT.Continuum

theorem distribution_laplacian_eq_sum_of_weakPartial {N : ℕ}
    {f : SpatialL2 N} (d e : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k)
    (he : ∀ k, WeakPartial (d k) (e k) k) :
    Δ (f : 𝓢'(Configuration N, ℂ)) =
      ((∑ k, e k : SpatialL2 N) : 𝓢'(Configuration N, ℂ)) := by
  classical
  rw [laplacian_eq_sum (EuclideanSpace.basisFun (Coordinate N) ℝ)]
  simp only [EuclideanSpace.basisFun_apply]
  change (∑ k : Coordinate N,
    ∂_{coordinateVector k} (∂_{coordinateVector k} (f : 𝓢'(Configuration N, ℂ)))) = _
  simp_rw [fun k => (hd k).temperedDistribution_derivative,
    fun k => (he k).temperedDistribution_derivative]
  simp only [← Lp.toTemperedDistributionCLM_apply, map_sum]

#print axioms distribution_laplacian_eq_sum_of_weakPartial

end TheoremT.Continuum
