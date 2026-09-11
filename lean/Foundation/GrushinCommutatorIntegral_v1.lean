import GrushinCommutatorBound_v1
import GrushinCommutatorSupport_v1
import KSTubeIntegralLimit_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

theorem nuclear_KS_commutator_integral_tendsto_zero {N : ℕ} (i : Fin N)
    {φ : NuclearKSSpace i → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    {u : NuclearKSSpace i → ℂ} {M : ℝ} (hM : ∀ q, ‖u q‖ ≤ M)
    {δ : ℕ → ℝ} (hδ : ∀ n, 0 < δ n) (hδ1 : ∀ n, δ n ≤ 1)
    (hd : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => ∫ q, (ksHoleCommutator (δ n) φ q : ℂ)*u q) atTop (𝓝 0) := by
  obtain ⟨A,hA,hb⟩ := ksHoleCommutator_bound hφ hc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  apply nuclear_KS_supported_integral_tendsto_zero i _
    (A := A*M) (Prod.snd '' tsupport φ)
    (hc.isCompact.image continuous_snd |>.measure_lt_top.ne) hδ hd
  · intro n q hq
    simp only [nuclear_KS_commutator_tube_support i (hδ n) q hq,Complex.ofReal_zero,zero_mul]
  · intro n q
    rw [norm_mul,Complex.norm_real]
    have hh := mul_le_mul (hb (δ n) (hδ n) (hδ1 n) q) (hM q)
      (norm_nonneg _) (by positivity : 0 ≤ A/(δ n)^2)
    simpa only [div_mul_eq_mul_div] using hh

#print axioms nuclear_KS_commutator_integral_tendsto_zero
end TheoremT.Continuum
