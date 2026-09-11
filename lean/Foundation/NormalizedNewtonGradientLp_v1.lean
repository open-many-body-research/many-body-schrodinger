import NewtonWeakGradient_v1

noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

theorem normalizedNewtonGradient_locallyIntegrable {N : ℕ} (hN : 0 < N) (k : Coordinate N) :
    LocallyIntegrable (normalizedNewtonGradient N k) volume :=
  (newtonGradient_locallyIntegrable hN k).smul ((newtonMass N)⁻¹)

theorem normalizedNewtonGradient_memLp_on_compact {N : ℕ} (hN : 0 < N) (k : Coordinate N)
    {q : ℝ} (hq : 0 < q) (hqd : ((3*N:ℝ)-1)*q < (3*N:ℝ))
    {K : Set (Configuration N)} (hK : IsCompact K) :
    MemLp (normalizedNewtonGradient N k) (ENNReal.ofReal q) (volume.restrict K) :=
  (newtonGradient_memLp_on_compact hN k hq hqd hK).const_mul ((newtonMass N)⁻¹)

theorem normalizedNewtonGradient_indicator_memLp {N : ℕ} (hN : 0 < N) (k : Coordinate N)
    {q : ℝ} (hq : 0 < q) (hqd : ((3*N:ℝ)-1)*q < (3*N:ℝ)) (R : ℝ) :
    MemLp ((Metric.closedBall (0 : Configuration N) R).indicator (normalizedNewtonGradient N k))
      (ENNReal.ofReal q) volume :=
  (memLp_indicator_iff_restrict Metric.isClosed_closedBall.measurableSet).mpr
    (normalizedNewtonGradient_memLp_on_compact hN k hq hqd (isCompact_closedBall 0 R))

#print axioms normalizedNewtonGradient_indicator_memLp
end TheoremT.Continuum
