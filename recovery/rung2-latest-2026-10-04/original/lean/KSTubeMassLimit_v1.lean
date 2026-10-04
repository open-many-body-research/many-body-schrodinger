import KSTubeL2Mass_v1
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace TheoremT.Continuum

theorem nuclear_KS_tube_squared_mass_tendsto_zero {N : ℕ} (i : Fin N)
    {g : NuclearKSSpace i → ℂ} {M : ℝ} (hM : ∀ q, ‖g q‖ ≤ M)
    (T : Set (SpectatorConfiguration i)) (hT : volume T ≠ ⊤)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ q in (Metric.ball (0 : KSSpace) (r n)) ×ˢ T, ‖g q‖ₑ^2)
      atTop (𝓝 0) := by
  have hp : Tendsto (fun n => (ENNReal.ofReal (r n))^4) atTop (𝓝 0) := by
    have he : Tendsto (fun n => ENNReal.ofReal (r n)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal hr
    simpa using (ENNReal.Tendsto.pow (n := 4) he)
  have hfin : ENNReal.ofReal (Real.pi^2/2)*volume T ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT
  have hb : Tendsto (fun n => (ENNReal.ofReal M)^2*
      ((ENNReal.ofReal (r n))^4*ENNReal.ofReal (Real.pi^2/2)*volume T)) atTop (𝓝 0) := by
    have hh := (ENNReal.continuous_mul_const hfin).tendsto 0 |>.comp hp
    have hh' := (ENNReal.continuous_const_mul (show (ENNReal.ofReal M)^2 ≠ ⊤ by finiteness)).tendsto 0 |>.comp (by simpa using hh)
    simpa only [Function.comp_def,zero_mul,mul_zero,mul_assoc] using hh'
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    (fun n => bot_le) (fun n => nuclear_KS_tube_squared_mass_le i hM (r n) T)

#print axioms nuclear_KS_tube_squared_mass_tendsto_zero
end TheoremT.Continuum
