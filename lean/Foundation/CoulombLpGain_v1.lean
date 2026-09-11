import UncappedRadialPowerL2_v1

/-! An actual higher-integrability step for every scalar Coulomb H2 eigenfunction.
Only the previous finite Lp membership is required; caps and regularizations
have been removed by proved L2 limits. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace TheoremT.Continuum

theorem scalar_eigen_Lp_power_bound {N : ℕ} (hN : 0 < N)
    {Z E r : ℝ} {f : SpatialL2 N} (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    (hr : 0 ≤ r) (hf : MemLp f (2*ENNReal.ofReal (2*r+1)) volume) :
    (eLpNorm f ((atomicSobolevExponent N : ℝ≥0∞)*ENNReal.ofReal (2*r+1)) volume)^(2*r+1) ≤
      ENNReal.ofReal (smoothPowerSobolevCoefficient N Z E r)*
        (eLpNorm f (2*ENNReal.ofReal (2*r+1)) volume)^(2*r+1) := by
  have h := scalar_eigen_radial_power_sobolev hN hg hr hf
  have he (q : ℝ≥0∞) : eLpNorm (radialPowerL2 hr hf) q volume =
      (eLpNorm f (q*ENNReal.ofReal (2*r+1)) volume)^(2*r+1) := by
    rw [eLpNorm_congr_ae (radialPowerL2_ae hr hf),radialPower_eLpNorm hr]
  rw [he] at h
  rw [ENNReal.ofReal_mul (smoothPowerSobolevCoefficient_nonneg N Z E r)] at h
  rw [ofReal_norm, Lp.enorm_def,he] at h
  exact h

theorem scalar_eigen_Lp_gain {N : ℕ} (hN : 0 < N)
    {Z E r : ℝ} {f : SpatialL2 N} (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    (hr : 0 ≤ r) (hf : MemLp f (2*ENNReal.ofReal (2*r+1)) volume) :
    eLpNorm f ((atomicSobolevExponent N : ℝ≥0∞)*ENNReal.ofReal (2*r+1)) volume ≤
      (ENNReal.ofReal (smoothPowerSobolevCoefficient N Z E r))^((2*r+1)⁻¹)*
        eLpNorm f (2*ENNReal.ofReal (2*r+1)) volume := by
  have hp : 0 < 2*r+1 := by linarith
  have h := ENNReal.rpow_le_rpow (scalar_eigen_Lp_power_bound hN hg hr hf)
    (inv_nonneg.mpr hp.le)
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hp.le),
    ← ENNReal.rpow_mul,mul_inv_cancel₀ hp.ne',ENNReal.rpow_one] using h

theorem scalar_eigen_memLp_gain {N : ℕ} (hN : 0 < N)
    {Z E r : ℝ} {f : SpatialL2 N} (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    (hr : 0 ≤ r) (hf : MemLp f (2*ENNReal.ofReal (2*r+1)) volume) :
    MemLp f ((atomicSobolevExponent N : ℝ≥0∞)*ENNReal.ofReal (2*r+1)) volume := by
  refine ⟨Lp.aestronglyMeasurable f, (scalar_eigen_Lp_gain hN hg hr hf).trans_lt ?_⟩
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg
    (inv_nonneg.mpr (by linarith)) ENNReal.ofReal_ne_top) hf.2

#print axioms scalar_eigen_Lp_gain
#print axioms scalar_eigen_memLp_gain
end TheoremT.Continuum
