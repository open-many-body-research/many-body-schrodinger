import CoulombMoserUniform_v1
import MoserLogClosedForm_v1
import LpEssentialBound_v1

/-! Global essential boundedness of every actual scalar Coulomb H2 eigenfunction
at every finite positive electron count and every real charge and eigenvalue.
No binding, isolation, ground-state, symmetry or pre-existing higher Lp premise. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace TheoremT.Continuum

theorem atomic_moser_exponents_tendsto {N : ℕ} (hN : 0 < N) :
    Tendsto (fun k : ℕ => 2*atomicMoserRatio N ^ k) atTop atTop :=
  (tendsto_pow_atTop_atTop_of_one_lt (atomicMoserRatio_gt_one hN)).const_mul_atTop
    (by norm_num)

theorem scalar_coulomb_eigen_ae_bound {N : ℕ} (hN : 0 < N)
    {Z E : ℝ} {f : SpatialL2 N} (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f)) :
    ∀ᵐ x, ‖f x‖ ≤ coulombMoserBoundCoefficient N Z E*‖f‖ := by
  have hc : 0 < atomicMoserRatio N := lt_trans zero_lt_one (atomicMoserRatio_gt_one hN)
  exact configuration_ae_norm_le_of_Lp_bounds f (fun k => by positivity)
    (atomic_moser_exponents_tendsto hN)
    (mul_nonneg (coulombMoserBoundCoefficient_pos N Z E).le (norm_nonneg f))
    (scalar_eigen_moser_uniform_bound hN hg)

theorem scalar_coulomb_eigen_Linfty_bound {N : ℕ} (hN : 0 < N)
    {Z E : ℝ} {f : SpatialL2 N} (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f)) :
    eLpNorm f ⊤ volume ≤ ENNReal.ofReal (coulombMoserBoundCoefficient N Z E*‖f‖) :=
  eLpNormEssSup_le_of_ae_bound (scalar_coulomb_eigen_ae_bound hN hg)

theorem scalar_coulomb_eigen_memLp_top {N : ℕ} (hN : 0 < N)
    {Z E : ℝ} {f : SpatialL2 N} (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f)) :
    MemLp f ⊤ volume :=
  ⟨Lp.aestronglyMeasurable f,(scalar_coulomb_eigen_Linfty_bound hN hg).trans_lt ENNReal.ofReal_lt_top⟩

#print axioms scalar_coulomb_eigen_ae_bound
#print axioms scalar_coulomb_eigen_memLp_top
end TheoremT.Continuum
