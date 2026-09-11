import BoundedSmoothMultiplierJet_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.Continuum

theorem real_multiplier_memLp_of_bound {N : ℕ} (f : SpatialL2 N)
    {c b : Configuration N → ℝ} (hc : AEStronglyMeasurable c volume)
    (hb : MemLp (fun x => b x*‖f x‖) 2 volume)
    (hcb : ∀ᵐ x, ‖c x‖ ≤ ‖b x‖) : MemLp (fun x => c x • f x) 2 volume := by
  apply hb.of_le (hc.smul (Lp.memLp f).aestronglyMeasurable)
  filter_upwards [hcb] with x hx
  change ‖c x • f x‖ ≤ ‖b x*‖f x‖‖
  simpa only [Pi.smul_apply,norm_smul,norm_mul,norm_norm] using
    mul_le_mul_of_nonneg_right hx (norm_nonneg (f x))

theorem real_multiplier_toLp_tendsto {N : ℕ} (f : SpatialL2 N)
    {c : ℕ → Configuration N → ℝ} {c₀ b : Configuration N → ℝ}
    (hc : ∀ n, AEStronglyMeasurable (c n) volume)
    (hc₀ : AEStronglyMeasurable c₀ volume)
    (hb : MemLp (fun x => b x*‖f x‖) 2 volume)
    (hcb : ∀ n, ∀ᵐ x, ‖c n x‖ ≤ ‖b x‖)
    (hc₀b : ∀ᵐ x, ‖c₀ x‖ ≤ ‖b x‖)
    (ht : ∀ᵐ x, Tendsto (fun n => c n x) atTop (𝓝 (c₀ x))) :
    Tendsto
      (fun n => (real_multiplier_memLp_of_bound f (hc n) hb (hcb n)).toLp (fun x => c n x • f x))
      atTop (𝓝 ((real_multiplier_memLp_of_bound f hc₀ hb hc₀b).toLp (fun x => c₀ x • f x))) := by
  apply configuration_toLp_tendsto_dominated
    (fun n => real_multiplier_memLp_of_bound f (hc n) hb (hcb n))
    (real_multiplier_memLp_of_bound f hc₀ hb hc₀b) hb
  · intro n
    filter_upwards [hcb n] with x hx
    simpa only [Pi.smul_apply,norm_smul,norm_mul,norm_norm] using
      mul_le_mul_of_nonneg_right hx (norm_nonneg (f x))
  · filter_upwards [hc₀b] with x hx
    simpa only [Pi.smul_apply,norm_smul,norm_mul,norm_norm] using
      mul_le_mul_of_nonneg_right hx (norm_nonneg (f x))
  · filter_upwards [ht] with x hx
    exact hx.smul tendsto_const_nhds

#print axioms real_multiplier_toLp_tendsto
end TheoremT.Continuum
