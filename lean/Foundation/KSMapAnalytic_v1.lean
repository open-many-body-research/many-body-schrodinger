import NuclearKSLift_v1

noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum

theorem ksMap_contDiff_omega : ContDiff ℝ ω ksMap := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ω (fun x : KSSpace => 2*(x 0*x 2+x 1*x 3))
    fun_prop
  · change ContDiff ℝ ω (fun x : KSSpace => 2*(x 1*x 2-x 0*x 3))
    fun_prop
  · change ContDiff ℝ ω (fun x : KSSpace => x 0^2+x 1^2-x 2^2-x 3^2)
    fun_prop

theorem nuclearKSLift_contDiff_omega {N : ℕ} (i : Fin N) : ContDiff ℝ ω (nuclearKSLift i) :=
  (configurationProductEquiv i).symm.contDiff.comp
    ((ksMap_contDiff_omega.comp contDiff_fst).prodMk contDiff_snd)

theorem nuclearKSLift_analyticAt {N : ℕ} (i : Fin N) (q : NuclearKSSpace i) :
    AnalyticAt ℝ (nuclearKSLift i) q := (nuclearKSLift_contDiff_omega i).contDiffAt.analyticAt

#print axioms ksMap_contDiff_omega
#print axioms nuclearKSLift_analyticAt
end TheoremT.Continuum
