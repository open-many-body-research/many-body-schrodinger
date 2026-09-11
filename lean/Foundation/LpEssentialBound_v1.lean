import LpIncreasingExponentBound_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace TheoremT.Continuum

theorem configuration_ae_norm_le_of_Lp_bounds {N : ℕ} (f : SpatialL2 N)
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (ht : Tendsto a atTop atTop)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n, eLpNorm f (ENNReal.ofReal (a n)) volume ≤ ENNReal.ofReal C) :
    ∀ᵐ x, ‖f x‖ ≤ C := by
  have hpoint (n : ℕ) : ∀ᵐ x, ‖f x‖ < C+1/((n:ℝ)+1) := by
    have htC : C < C+1/((n:ℝ)+1) := by
      have : 0 < 1/((n:ℝ)+1) := by positivity
      linarith
    have hnull := configuration_norm_superlevel_null_of_Lp_bounds f ha ht hC hb htC
    apply ae_iff.mpr
    have hset : {x | ¬ ‖f x‖ < C+1/((n:ℝ)+1)} =
        {x | ENNReal.ofReal (C+1/((n:ℝ)+1)) ≤ ‖f x‖ₑ} := by
      ext x
      simp only [Set.mem_setOf_eq,not_lt,← ofReal_norm]
      exact (ENNReal.ofReal_le_ofReal_iff (norm_nonneg (f x))).symm
    rw [hset]
    exact hnull
  have hall : ∀ᵐ x, ∀ n : ℕ, ‖f x‖ < C+1/((n:ℝ)+1) := by
    rw [ae_all_iff]; exact hpoint
  filter_upwards [hall] with x hx
  have hlim : Tendsto (fun n : ℕ => C+1/((n:ℝ)+1)) atTop (𝓝 C) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add C
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim (fun n => (hx n).le)

theorem configuration_eLpNorm_top_le_of_Lp_bounds {N : ℕ} (f : SpatialL2 N)
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (ht : Tendsto a atTop atTop)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n, eLpNorm f (ENNReal.ofReal (a n)) volume ≤ ENNReal.ofReal C) :
    eLpNorm f ⊤ volume ≤ ENNReal.ofReal C :=
  eLpNormEssSup_le_of_ae_bound (configuration_ae_norm_le_of_Lp_bounds f ha ht hC hb)

#print axioms configuration_ae_norm_le_of_Lp_bounds
end TheoremT.Continuum
