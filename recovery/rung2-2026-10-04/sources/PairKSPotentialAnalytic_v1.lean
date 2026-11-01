import PairKSPotentialSmooth_v1
import KSMapAnalytic_v1

/-! Analyticity of the exact pair KS lift and coefficient.
The existing patch excludes the two nuclear positions and includes the pair
collision fiber away from the nucleus. ContDiff at omega, rather than at
infinity, supplies actual analyticity. No Hamiltonian or coordinate change
is introduced.
-/
noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum

theorem pairKSLift_contDiff_omega : ContDiff ℝ ω pairKSLift :=
  pairCoordinates.contDiff.comp
    ((ksMap_contDiff_omega.comp contDiff_fst).prodMk contDiff_snd)

theorem pairKSLift_analyticAt (q : PairKSSpace) : AnalyticAt ℝ pairKSLift q :=
  pairKSLift_contDiff_omega.contDiffAt.analyticAt

theorem pairKSPotential_contDiffAt_omega (Z E : ℝ)
    {q : PairKSSpace} (hq : q ∈ pairKSCoefficientPatch) :
    ContDiffAt ℝ ω (pairKSPotential Z E) q := by
  have hc (j : Fin 2) : ContDiffAt ℝ ω
      (fun z : PairKSSpace => position (pairKSLift z) j) q := by
    have hp : ContDiff ℝ ω (fun x : Configuration 2 => position x j) := by
      simpa only [← electronPositionCLM_apply] using (electronPositionCLM j).contDiff
    exact (hp.comp pairKSLift_contDiff_omega).contDiffAt
  have h0 := ((hc 0).norm ℝ hq.1).inv (norm_ne_zero_iff.mpr hq.1)
  have h1 := ((hc 1).norm ℝ hq.2).inv (norm_ne_zero_iff.mpr hq.2)
  have hr : ContDiff ℝ ω (fun z : PairKSSpace => ‖z.1‖^2) :=
    (contDiff_norm_sq ℝ).comp contDiff_fst
  exact contDiffAt_const.add ((contDiffAt_const.mul hr.contDiffAt).mul
    ((contDiffAt_const.mul (h0.add h1)).sub contDiffAt_const))

theorem pairKSPotential_analyticAt (Z E : ℝ)
    {q : PairKSSpace} (hq : q ∈ pairKSCoefficientPatch) :
    AnalyticAt ℝ (pairKSPotential Z E) q :=
  (pairKSPotential_contDiffAt_omega Z E hq).analyticAt

theorem pairKSPotential_analyticOnNhd (Z E : ℝ) :
    AnalyticOnNhd ℝ (pairKSPotential Z E) pairKSCoefficientPatch :=
  fun _ hq => pairKSPotential_analyticAt Z E hq

end TheoremT.Continuum
