import ConfigurationLocalDominated_v1

noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

theorem configuration_norm_rpow_locallyIntegrable {N : ℕ} (hN : 0 < N)
    {α : ℝ} (hα : α < (3*N:ℝ)) :
    LocallyIntegrable (fun x : Configuration N => ‖x‖^(-α)) volume := by
  apply locallyIntegrable_of_norm_le_rpow (C := 1) (α := α)
    (by rw [configuration_finrank]; omega)
    (by simpa only [configuration_finrank,Nat.cast_mul,Nat.cast_ofNat] using hα)
  · filter_upwards with x
    simp only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _),one_mul,le_refl]
  · exact (continuous_norm.measurable.pow_const (-α)).aestronglyMeasurable

theorem configuration_norm_rpow_memLp_on_compact {N : ℕ} (hN : 0 < N)
    {α q : ℝ} (hq : 0 < q) (hα : α*q < (3*N:ℝ))
    {K : Set (Configuration N)} (hK : IsCompact K) :
    MemLp (fun x : Configuration N => ‖x‖^(-α)) (ENNReal.ofReal q) (volume.restrict K) := by
  have hm : AEStronglyMeasurable (fun x : Configuration N => ‖x‖^(-α)) (volume.restrict K) :=
    (continuous_norm.measurable.pow_const (-α)).aestronglyMeasurable
  rw [← integrable_norm_rpow_iff hm (by positivity : ENNReal.ofReal q ≠ 0) (by simp)]
  have hi := (configuration_norm_rpow_locallyIntegrable hN hα).integrableOn_isCompact hK
  apply hi.congr
  filter_upwards with x
  simp only [ENNReal.toReal_ofReal hq.le,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _),← Real.rpow_mul (norm_nonneg x)]
  congr 1
  ring

#print axioms configuration_norm_rpow_memLp_on_compact
end TheoremT.Continuum
