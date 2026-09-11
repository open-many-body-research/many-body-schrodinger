import GrushinCutoffEnergy_v1
import CompactSupportWeightedL2_v1

noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def grushinCutoffWeight (c : ℝ)
    (η : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℝ)
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) : ℝ :=
  (∑ i : ι,(partialYDirectional η (oscillatorBasis i) p)^2) +
    c*‖p.1‖^2*(∑ j : κ,(partialTDirectional η (oscillatorBasis j) p)^2)

theorem grushin_cutoff_energy_l2_identity (c : ℝ)
    {η : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℝ}
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ))) :
    grushinCutoffEnergy c η f = ∫ p, grushinCutoffWeight c η p*‖f p‖^2 := by
  have hf := (Lp.memLp f).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have iy (i : ι) : Integrable (fun p =>
      (partialYDirectional η (oscillatorBasis i) p)^2*‖f p‖^2) := by
    have hcy : HasCompactSupport (fun p => (partialYDirectional η (oscillatorBasis i) p)^2) := by
      apply (partialYDirectional_hasCompactSupport hc (oscillatorBasis i)).mono
      intro p hp hz
      exact hp (by simp [hz])
    simpa only [smul_eq_mul, Pi.pow_apply, Pi.mul_apply] using hf.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
      ((partialYDirectional_contDiff hη _).continuous.pow 2)
      hcy
  have it (j : κ) : Integrable (fun p =>
      (‖p.1‖^2*(partialTDirectional η (oscillatorBasis j) p)^2)*‖f p‖^2) := by
    have hct : HasCompactSupport (fun p => (partialTDirectional η (oscillatorBasis j) p)^2) := by
      apply (partialTDirectional_hasCompactSupport hc (oscillatorBasis j)).mono
      intro p hp hz
      exact hp (by simp [hz])
    simpa only [smul_eq_mul, Pi.pow_apply, Pi.mul_apply] using hf.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
      ((continuous_fst.norm.pow 2).mul ((partialTDirectional_contDiff hη _).continuous.pow 2))
      hct.mul_left
  have iys := integrable_finsetSum Finset.univ (fun i _ => iy i)
  have its := integrable_finsetSum Finset.univ (fun j _ => it j)
  calc
    grushinCutoffEnergy c η f =
        (∫ p, ∑ i : ι, (partialYDirectional η (oscillatorBasis i) p)^2*‖f p‖^2) +
        c*(∫ p, ∑ j : κ, (‖p.1‖^2*(partialTDirectional η (oscillatorBasis j) p)^2)*‖f p‖^2) := by
      rw [integral_finsetSum _ (fun i _ => iy i), integral_finsetSum _ (fun j _ => it j)]
      simp only [grushinCutoffEnergy,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,mul_assoc,
        Measure.volume_eq_prod]
    _ = ∫ p, (∑ i : ι, (partialYDirectional η (oscillatorBasis i) p)^2*‖f p‖^2) +
        c*(∑ j : κ, (‖p.1‖^2*(partialTDirectional η (oscillatorBasis j) p)^2)*‖f p‖^2) := by
      rw [integral_add iys (its.const_mul c), integral_const_mul]
    _ = ∫ p, grushinCutoffWeight c η p*‖f p‖^2 := by
      apply integral_congr_ae
      filter_upwards with p
      simp only [grushinCutoffWeight,add_mul,Finset.sum_mul,Finset.mul_sum,mul_assoc]

theorem grushin_cutoff_energy_l2_bound (c C : ℝ)
    {η : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℝ}
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hb : ∀ p, grushinCutoffWeight c η p ≤ C)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ))) :
    grushinCutoffEnergy c η f ≤ C * (∫ p, ‖f p‖^2) := by
  rw [grushin_cutoff_energy_l2_identity c hη hc f,← integral_const_mul]
  have hf := (Lp.memLp f).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hW : Continuous (grushinCutoffWeight c η) := by
    unfold grushinCutoffWeight
    exact (continuous_finsetSum _ (fun i _ => (partialYDirectional_contDiff hη _).continuous.pow 2)).add
      ((continuous_const.mul (continuous_fst.norm.pow 2)).mul
        (continuous_finsetSum _ (fun j _ => (partialTDirectional_contDiff hη _).continuous.pow 2)))
  have hWs : HasCompactSupport (grushinCutoffWeight c η) := by
    apply hc.mono'
    intro p hp
    by_contra hn
    have hy (i : ι) : partialYDirectional η (oscillatorBasis i) p = 0 := by
      change fderiv ℝ η p (oscillatorBasis i,0) = 0
      rw [fderiv_of_notMem_tsupport ℝ hn]
      rfl
    have ht (j : κ) : partialTDirectional η (oscillatorBasis j) p = 0 := by
      change fderiv ℝ η p (0,oscillatorBasis j) = 0
      rw [fderiv_of_notMem_tsupport ℝ hn]
      rfl
    exact hp (by simp [grushinCutoffWeight,hy,ht])
  have hi : Integrable (fun p => grushinCutoffWeight c η p*‖f p‖^2) := by
    simpa only [smul_eq_mul, Pi.pow_apply, Pi.mul_apply] using hf.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hW hWs
  exact integral_mono hi (hf.const_mul C) (fun p => mul_le_mul_of_nonneg_right (hb p) (sq_nonneg _))

#print axioms grushin_cutoff_energy_l2_identity
#print axioms grushin_cutoff_energy_l2_bound
end TheoremT.Continuum
