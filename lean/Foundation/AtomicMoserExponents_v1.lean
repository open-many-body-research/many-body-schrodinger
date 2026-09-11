import CoulombLpGain_v1

noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace TheoremT.Continuum

def atomicMoserRatio (N : ℕ) : ℝ := (atomicSobolevExponent N : ℝ)/2

theorem atomicMoserRatio_gt_one {N : ℕ} (hN : 0 < N) : 1 < atomicMoserRatio N := by
  have hn : (1 : ℝ≥0) ≤ N := by exact_mod_cast hN
  have hn' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hd : (2 : ℝ≥0) ≤ 3*N := by nlinarith
  simp only [atomicMoserRatio,atomicSobolevExponent,NNReal.coe_div,NNReal.coe_mul,
    NNReal.coe_ofNat,NNReal.coe_natCast,NNReal.coe_sub hd]
  apply (lt_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  apply (lt_div_iff₀ (by linarith : (0:ℝ)<3*N-2)).mpr
  nlinarith

def moserPowerParameter (N k : ℕ) : ℝ := (atomicMoserRatio N ^ k-1)/2

theorem moserPowerParameter_nonneg {N : ℕ} (hN : 0 < N) (k : ℕ) :
    0 ≤ moserPowerParameter N k := by
  have h := one_le_pow₀ (atomicMoserRatio_gt_one hN).le (n := k)
  unfold moserPowerParameter; linarith

theorem moserPowerParameter_identity (N k : ℕ) :
    2*moserPowerParameter N k+1 = atomicMoserRatio N ^ k := by
  unfold moserPowerParameter; ring

theorem moser_input_exponent {N : ℕ} (hN : 0 < N) (k : ℕ) :
    2*ENNReal.ofReal (2*moserPowerParameter N k+1) =
      ENNReal.ofReal (2*atomicMoserRatio N ^ k) := by
  rw [moserPowerParameter_identity,ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]
  norm_num

theorem moser_output_exponent {N : ℕ} (hN : 0 < N) (k : ℕ) :
    (atomicSobolevExponent N : ℝ≥0∞)*ENNReal.ofReal (2*moserPowerParameter N k+1) =
      ENNReal.ofReal (2*atomicMoserRatio N ^ (k+1)) := by
  rw [moserPowerParameter_identity]
  have he : (atomicSobolevExponent N : ℝ≥0∞) =
      ENNReal.ofReal (2*atomicMoserRatio N) := by
    have ha : 2*atomicMoserRatio N = (atomicSobolevExponent N : ℝ) := by
      unfold atomicMoserRatio; ring
    rw [ha,ENNReal.ofReal_coe_nnreal]
  have hc : 0 < atomicMoserRatio N := lt_trans zero_lt_one (atomicMoserRatio_gt_one hN)
  rw [he,← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*atomicMoserRatio N),pow_succ]
  congr 1; ring

theorem scalar_eigen_memLp_moser_sequence {N : ℕ} (hN : 0 < N)
    {Z E : ℝ} {f : SpatialL2 N} (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    (k : ℕ) : MemLp f (ENNReal.ofReal (2*atomicMoserRatio N ^ k)) volume := by
  induction k with
  | zero => simpa using Lp.memLp f
  | succ k ih =>
    rw [← moser_output_exponent hN k]
    apply scalar_eigen_memLp_gain hN hg (moserPowerParameter_nonneg hN k)
    simpa only [moser_input_exponent hN k] using ih

theorem scalar_eigen_moser_step {N : ℕ} (hN : 0 < N)
    {Z E : ℝ} {f : SpatialL2 N} (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    (k : ℕ) :
    eLpNorm f (ENNReal.ofReal (2*atomicMoserRatio N ^ (k+1))) volume ≤
      (ENNReal.ofReal (smoothPowerSobolevCoefficient N Z E (moserPowerParameter N k)))^
        ((atomicMoserRatio N ^ k)⁻¹)*
      eLpNorm f (ENNReal.ofReal (2*atomicMoserRatio N ^ k)) volume := by
  have hf := scalar_eigen_memLp_moser_sequence hN hg k
  rw [← moser_input_exponent hN k] at hf
  have h := scalar_eigen_Lp_gain hN hg (moserPowerParameter_nonneg hN k) hf
  rw [moser_input_exponent hN k,moser_output_exponent hN k,
    moserPowerParameter_identity] at h
  exact h

#print axioms scalar_eigen_memLp_moser_sequence
#print axioms scalar_eigen_moser_step
end TheoremT.Continuum
