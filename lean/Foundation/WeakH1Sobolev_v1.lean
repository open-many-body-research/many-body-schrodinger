import ConfigurationSobolevCore_v1
import LpLimitBound_v1
import HardyH1ScalarDensity_v2

/-! Sobolev embedding on the actual distributional H1 domain. Compact smooth
density and lower semicontinuity are discharged by proved project/Mathlib lemmas.
The coefficient is finite but not asserted to be an explicit computable number. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff NNReal ENNReal
namespace TheoremT.Continuum
set_option maxHeartbeats 800000

theorem weakH1_sobolev_bound {N : ℕ} {f : SpatialL2 N}
    (d : Coordinate N → SpatialL2 N) (hd : ∀ k, WeakPartial f (d k) k)
    {q : ℝ≥0} (hN : 0 < Module.finrank ℝ (Configuration N))
    (hq : (q : ℝ)⁻¹ = (2 : ℝ)⁻¹ -
      (Module.finrank ℝ (Configuration N) : ℝ)⁻¹) :
    eLpNorm f q volume ≤ ENNReal.ofReal
      ((configurationSobolevConstant N : ℝ) * ∑ k, ‖d k‖) := by
  classical
  obtain ⟨u,g,dg,hu,hc,hgu,hdgu,_hw,_hH2,hg,hdg⟩ :=
    weakH1_smooth_compact_graph_sequence d hd
  apply eLpNorm_le_of_L2_tendsto_bound g hg
    (fun n => (configurationSobolevConstant N : ℝ) * ∑ k, ‖dg n k‖)
  · exact tendsto_const_nhds.mul (tendsto_finset_sum Finset.univ (fun k _ => (hdg k).norm))
  · intro n
    rw [eLpNorm_congr_ae (hgu n)]
    have he (k : Coordinate N) : eLpNorm (smoothPartial (u n) k) 2 volume =
        ENNReal.ofReal ‖dg n k‖ := by
      rw [← eLpNorm_congr_ae (hdgu n k),← Lp.enorm_def,← ofReal_norm]
    have hb := configuration_sobolev_core (hu n) (hc n) hN hq
    simp_rw [he] at hb
    simpa only [ENNReal.ofReal_mul (NNReal.coe_nonneg _),ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_sum_of_nonneg (fun k _ => norm_nonneg _)] using hb

theorem weakH1_sobolev_memLp {N : ℕ} {f : SpatialL2 N}
    (d : Coordinate N → SpatialL2 N) (hd : ∀ k, WeakPartial f (d k) k)
    {q : ℝ≥0} (hN : 0 < Module.finrank ℝ (Configuration N))
    (hq : (q : ℝ)⁻¹ = (2 : ℝ)⁻¹ -
      (Module.finrank ℝ (Configuration N) : ℝ)⁻¹) : MemLp f q volume :=
  ⟨Lp.aestronglyMeasurable f,
    (weakH1_sobolev_bound d hd hN hq).trans_lt ENNReal.ofReal_lt_top⟩

#print axioms weakH1_sobolev_bound
#print axioms weakH1_sobolev_memLp
end TheoremT.Continuum
