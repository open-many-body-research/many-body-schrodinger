import RealMultiplierL2Limit_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.Continuum

theorem ae_norm_bound_of_pointwise_limit {N : ℕ}
    {c : ℕ → Configuration N → ℝ} {c₀ b : Configuration N → ℝ}
    (hb : ∀ n, ∀ᵐ x, ‖c n x‖ ≤ ‖b x‖)
    (ht : ∀ᵐ x, Tendsto (fun n => c n x) atTop (𝓝 (c₀ x))) :
    ∀ᵐ x, ‖c₀ x‖ ≤ ‖b x‖ := by
  have hall : ∀ᵐ x, ∀ n : ℕ, ‖c n x‖ ≤ ‖b x‖ := ae_all_iff.mpr hb
  filter_upwards [hall,ht] with x hx htx
  exact le_of_tendsto htx.norm (Eventually.of_forall hx)

theorem bounded_real_multiplier_limit {N : ℕ}
    {c : ℕ → Configuration N → ℝ} {c₀ : Configuration N → ℝ}
    (hc : ∀ n, MemLp (c n) (⊤ : ENNReal) volume)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n, ∀ᵐ x, ‖c n x‖ ≤ C)
    (ht : ∀ᵐ x, Tendsto (fun n => c n x) atTop (𝓝 (c₀ x))) :
    ∃ h₀ : MemLp c₀ (⊤ : ENNReal) volume, ∀ f : SpatialL2 N,
      Tendsto (fun n => boundedRealMul (c n) (hc n) f) atTop (𝓝 (boundedRealMul c₀ h₀ f)) := by
  have hm₀ : AEStronglyMeasurable c₀ volume :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hc n).aestronglyMeasurable) ht
  have hb' : ∀ n, ∀ᵐ x, ‖c n x‖ ≤ ‖(fun _ : Configuration N => C) x‖ := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg hC] using hb
  have hb₀ := ae_norm_bound_of_pointwise_limit hb' ht
  have h₀ : MemLp c₀ (⊤ : ENNReal) volume := memLp_top_of_bound hm₀ C
    (by simpa only [Real.norm_eq_abs,abs_of_nonneg hC] using hb₀)
  refine ⟨h₀,?_⟩
  intro f
  have hB : MemLp (fun x => C*‖f x‖) 2 volume := (Lp.memLp f).norm.const_mul C
  have h := real_multiplier_toLp_tendsto f (fun n => (hc n).aestronglyMeasurable) hm₀ hB hb' hb₀ ht
  exact h

theorem dominated_real_multiplier_limit {N : ℕ} (f : SpatialL2 N)
    {c : ℕ → Configuration N → ℝ} {c₀ b : Configuration N → ℝ}
    (hc : ∀ n, MemLp (c n) (⊤ : ENNReal) volume)
    (hb : MemLp (fun x => b x*‖f x‖) 2 volume)
    (hcb : ∀ n, ∀ᵐ x, ‖c n x‖ ≤ ‖b x‖)
    (ht : ∀ᵐ x, Tendsto (fun n => c n x) atTop (𝓝 (c₀ x))) :
    ∃ h₀ : MemLp (fun x => c₀ x • f x) 2 volume,
      Tendsto (fun n => boundedRealMul (c n) (hc n) f) atTop
        (𝓝 (h₀.toLp (fun x => c₀ x • f x))) := by
  have hm₀ : AEStronglyMeasurable c₀ volume :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hc n).aestronglyMeasurable) ht
  have hb₀ := ae_norm_bound_of_pointwise_limit hcb ht
  exact ⟨real_multiplier_memLp_of_bound f hm₀ hb hb₀,
    real_multiplier_toLp_tendsto f (fun n => (hc n).aestronglyMeasurable) hm₀ hb hcb hb₀ ht⟩

#print axioms bounded_real_multiplier_limit
#print axioms dominated_real_multiplier_limit
end TheoremT.Continuum
