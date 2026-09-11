import CoulombTransformedLipschitzBall_v1
import CoulombCuspLocallyLipschitz_v1

noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

theorem scalar_coulomb_lipschitz_representative_on_ball {N : ℕ} (hN : 0 < N)
    {Z E : ℝ} {f : SpatialL2 N} (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    {A : ℝ} (hA : 0 < A) :
    ∃ u : Configuration N → ℂ, LocallyLipschitz u ∧
      (f : Configuration N → ℂ) =ᵐ[volume.restrict (Metric.ball 0 A)] u := by
  obtain ⟨K,v,hv,hEq⟩ := scalar_coulomb_transformed_lipschitz_representative_on_ball hN hg hA
  refine ⟨fun x => Real.exp (coulombCusp N Z x) • v x,
    locally_lipschitz_real_smul (coulombCusp_exp_locallyLipschitz N Z) hv.locallyLipschitz,?_⟩
  filter_upwards [hEq] with x hx
  rw [← hx,smul_smul,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_smul]

#print axioms scalar_coulomb_lipschitz_representative_on_ball
end TheoremT.Continuum
