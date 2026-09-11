import KSTubeIntegralBound_v1
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace TheoremT.Continuum

theorem nuclear_KS_supported_integral_tendsto_zero {N : ℕ} (i : Fin N)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : ℕ → NuclearKSSpace i → G) {A : ℝ}
    (T : Set (SpectatorConfiguration i)) (hT : volume T ≠ ⊤)
    {δ : ℕ → ℝ} (hδ : ∀ n, 0 < δ n) (hd : Tendsto δ atTop (𝓝 0))
    (hs : ∀ n q, q ∉ (Metric.ball (0 : KSSpace) (3*δ n)) ×ˢ T → g n q=0)
    (hb : ∀ n q, ‖g n q‖ ≤ A/(δ n)^2) :
    Tendsto (fun n => ∫ q, g n q) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hh : Tendsto (fun n => 81*A*(Real.pi^2/2)*volume.real T*(δ n)^2) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (hd.pow 2)
  exact squeeze_zero (fun n => norm_nonneg _) (fun n =>
    nuclear_KS_supported_integral_bound i (hδ n) T hT (hs n) (hb n)) hh

#print axioms nuclear_KS_supported_integral_tendsto_zero
end TheoremT.Continuum
