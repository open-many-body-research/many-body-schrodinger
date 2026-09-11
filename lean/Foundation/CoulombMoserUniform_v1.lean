import MoserLogSeries_v1
import CoulombMoserCoefficient_v1

noncomputable section
open MeasureTheory
open scoped NNReal ENNReal BigOperators
namespace TheoremT.Continuum

def coulombMoserBoundCoefficient (N : ℕ) (Z E : ℝ) : ℝ :=
  Real.exp (∑' j, moserLogWeight (coulombMoserBase N Z E) (atomicMoserRatio N) j)

theorem coulombMoserBoundCoefficient_pos (N : ℕ) (Z E : ℝ) :
    0 < coulombMoserBoundCoefficient N Z E := Real.exp_pos _

theorem coulomb_moser_factor_le_exp {N : ℕ} (hN : 0 < N) (Z E : ℝ) (k : ℕ) :
    (ENNReal.ofReal (smoothPowerSobolevCoefficient N Z E (moserPowerParameter N k)))^
      ((atomicMoserRatio N ^ k)⁻¹) ≤
    ENNReal.ofReal (Real.exp (moserLogWeight (coulombMoserBase N Z E) (atomicMoserRatio N) k)) := by
  have hc : 0 < atomicMoserRatio N := lt_trans zero_lt_one (atomicMoserRatio_gt_one hN)
  have he : 0 ≤ (atomicMoserRatio N ^ k)⁻¹ := by positivity
  have hb : 0 ≤ coulombMoserBase N Z E := le_trans zero_le_one (coulombMoserBase_ge_one N Z E)
  have h := smoothPowerSobolevCoefficient_polynomial (moserPowerParameter_nonneg hN k) N Z E
  rw [moserPowerParameter_identity] at h
  have h' := ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal h) he
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity : 0 ≤
    coulombMoserBase N Z E*(atomicMoserRatio N ^ k)^2) he,
    moser_polynomial_factor_exp (coulombMoserBase_ge_one N Z E) (atomicMoserRatio_gt_one hN)] at h'
  exact h'

theorem scalar_eigen_moser_partial_bound {N : ℕ} (hN : 0 < N)
    {Z E : ℝ} {f : SpatialL2 N} (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    (k : ℕ) :
    eLpNorm f (ENNReal.ofReal (2*atomicMoserRatio N ^ k)) volume ≤
      ENNReal.ofReal (Real.exp (∑ j ∈ Finset.range k,
        moserLogWeight (coulombMoserBase N Z E) (atomicMoserRatio N) j))*ENNReal.ofReal ‖f‖ := by
  induction k with
  | zero => simp [ofReal_norm,Lp.enorm_def]
  | succ k ih =>
    have hs := scalar_eigen_moser_step hN hg k
    have hm := mul_le_mul (coulomb_moser_factor_le_exp hN Z E k) ih
      (by positivity) (by positivity)
    apply (hs.trans hm).trans_eq
    rw [Finset.sum_range_succ,Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le]
    ring

theorem scalar_eigen_moser_uniform_bound {N : ℕ} (hN : 0 < N)
    {Z E : ℝ} {f : SpatialL2 N} (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    (k : ℕ) :
    eLpNorm f (ENNReal.ofReal (2*atomicMoserRatio N ^ k)) volume ≤
      ENNReal.ofReal (coulombMoserBoundCoefficient N Z E*‖f‖) := by
  have hs := scalar_eigen_moser_partial_bound hN hg k
  have hb := moserLogWeight_partial_sum_le (coulombMoserBase_ge_one N Z E)
    (atomicMoserRatio_gt_one hN) k
  apply hs.trans
  rw [ENNReal.ofReal_mul (coulombMoserBoundCoefficient_pos N Z E).le]
  exact mul_le_mul (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hb)) le_rfl
    (by positivity) (by positivity)

#print axioms scalar_eigen_moser_uniform_bound
end TheoremT.Continuum
