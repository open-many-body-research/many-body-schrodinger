import KSHoleTestLimit_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.Continuum

theorem nuclear_KS_hole_integral_tendsto {N : ℕ} (i : Fin N)
    {g : NuclearKSSpace i → ℂ} (hg : Integrable g volume)
    {δ : ℕ → ℝ} (hδ : ∀ n, 0 < δ n) (hd : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => ∫ q, (ksHole (δ n) q.1 : ℂ)*g q) atTop (𝓝 (∫ q,g q)) := by
  have hae : ∀ᵐ q : NuclearKSSpace i ∂volume, q.1 ≠ 0 := by
    rw [ae_iff]
    simpa using nuclear_KS_transverse_zero_null i
  apply tendsto_integral_of_dominated_convergence (fun q => ‖g q‖)
  · intro n
    exact ((Complex.continuous_ofReal.comp ((ksHole_contDiff (δ n)).continuous.comp continuous_fst)).aestronglyMeasurable).mul hg.aestronglyMeasurable
  · exact hg.norm
  · intro n
    exact Eventually.of_forall (fun q => by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (ksHole_nonneg _ _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (ksHole_le_one _ _))
  · filter_upwards [hae] with q hq
    have hh := ((Complex.continuous_ofReal.tendsto 1).comp (ksHole_tendsto_one hδ hd hq)).mul (tendsto_const_nhds (x := g q))
    simpa using hh

#print axioms nuclear_KS_hole_integral_tendsto
end TheoremT.Continuum
