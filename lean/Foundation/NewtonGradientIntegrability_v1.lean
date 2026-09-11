import NewtonGradientLimits_v1

noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

theorem newtonGradient_measurable (N : ℕ) (k : Coordinate N) : Measurable (newtonGradient N k) :=
  (continuous_norm.measurable.pow_const (-(3*N:ℝ))).mul (EuclideanSpace.proj k).continuous.measurable

theorem newtonGradient_locallyIntegrable {N : ℕ} (hN : 0 < N) (k : Coordinate N) :
    LocallyIntegrable (newtonGradient N k) volume := by
  apply locallyIntegrable_of_norm_le_rpow (C := 1) (α := (3*N:ℝ)-1)
    (by rw [configuration_finrank]; omega)
    (by rw [configuration_finrank]; push_cast; linarith)
  · filter_upwards with x
    have hh := newtonGradient_abs_bound hN k x
    simpa only [Real.norm_eq_abs,one_mul,neg_sub] using hh
  · exact (newtonGradient_measurable N k).aestronglyMeasurable

theorem newtonGradient_memLp_on_compact {N : ℕ} (hN : 0 < N) (k : Coordinate N)
    {q : ℝ} (hq : 0 < q) (hqd : ((3*N:ℝ)-1)*q < (3*N:ℝ))
    {K : Set (Configuration N)} (hK : IsCompact K) :
    MemLp (newtonGradient N k) (ENNReal.ofReal q) (volume.restrict K) := by
  have hh := configuration_norm_rpow_memLp_on_compact hN hq hqd hK
  apply hh.mono' (newtonGradient_measurable N k).aestronglyMeasurable
  filter_upwards with x
  simpa only [Real.norm_eq_abs,neg_sub] using newtonGradient_abs_bound hN k x

#print axioms newtonGradient_memLp_on_compact
end TheoremT.Continuum
