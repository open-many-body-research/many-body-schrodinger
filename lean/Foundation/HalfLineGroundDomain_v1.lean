import HalfLineGroundCutoffs_v1
import HalfLineL2Dominated_v1
import HalfLineCoreDensity_v1

/-! The actual radial hydrogen ground vector belongs to the declared H1_0
closure, proved by explicit smooth positive compact tests and L2 convergence
of both values and their actual derivatives. No trace characterization is used. -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Set Filter
open scoped Topology
namespace TheoremT.HalfLine

theorem groundTest_value_tendsto (Z : ℝ) (hZ : 0 < Z) :
    Tendsto (fun n => (groundTest Z n).value) atTop (𝓝 (radialGroundL2 Z hZ)) := by
  apply tendsto_toLp_of_dominated (fun n => (groundTest Z n).memLp)
    (radialGround_memLp hZ) (radialGround_memLp hZ).norm
  · intro n
    exact ae_of_all _ fun r => by
      simpa only [norm_norm] using groundTest_value_norm_le Z n r
  · exact ae_of_all _ fun r => by simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    apply tendsto_const_nhds.congr'
    filter_upwards [groundTest_eventually_profile (Z := Z) hr] with n hn
    exact hn.1.symm

theorem groundTest_gradient_tendsto (Z : ℝ) (hZ : 0 < Z) :
    Tendsto (fun n => (groundTest Z n).gradient) atTop (𝓝 (radialGroundPrimeL2 Z hZ)) := by
  obtain ⟨C,hC,hb⟩ := transition_deriv_bounded
  apply tendsto_toLp_of_dominated (fun n => (groundTest Z n).deriv_memLp)
    (radialGroundPrime_memLp hZ) (groundDerivativeMajorant_memLp hZ C)
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (groundDerivativeMajorant_nonneg Z C r hC)]
    exact groundTest_deriv_norm_le Z n hC hb hr
  · exact ae_of_all _ fun r => by
      rw [Real.norm_eq_abs, abs_of_nonneg (groundDerivativeMajorant_nonneg Z C r hC)]
      exact groundPrime_norm_le_majorant Z C r hC
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    apply tendsto_const_nhds.congr'
    filter_upwards [groundTest_eventually_profile (Z := Z) hr] with n hn
    exact hn.2.symm

theorem radialGround_pair_mem_domain (Z : ℝ) (hZ : 0 < Z) :
    (radialGroundL2 Z hZ, radialGroundPrimeL2 Z hZ) ∈ domain := by
  apply core.isClosed_topologicalClosure.mem_of_tendsto
    ((groundTest_value_tendsto Z hZ).prodMk_nhds (groundTest_gradient_tendsto Z hZ))
  exact Eventually.of_forall fun n => (testEmbed (groundTest Z n)).property

def radialGroundD (Z : ℝ) (hZ : 0 < Z) : D :=
  ⟨(radialGroundL2 Z hZ,radialGroundPrimeL2 Z hZ),radialGround_pair_mem_domain Z hZ⟩

theorem J_radialGroundD (Z : ℝ) (hZ : 0 < Z) : J (radialGroundD Z hZ) = radialGroundL2 Z hZ := rfl

theorem dJ_radialGroundD (Z : ℝ) (hZ : 0 < Z) :
    dJ (radialGroundD Z hZ) = radialGroundPrimeL2 Z hZ := rfl

#print axioms groundTest_value_tendsto
#print axioms groundTest_gradient_tendsto
#print axioms radialGround_pair_mem_domain
#print axioms radialGroundD
#print axioms J_radialGroundD
#print axioms dJ_radialGroundD
end TheoremT.HalfLine
