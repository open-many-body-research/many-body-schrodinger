import CoulombCuspWeakLaplacian_v1
import LocallyLipschitzAlgebra_v1
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
namespace TheoremT.Continuum

theorem coulombCusp_locallyLipschitz (N : ℕ) (Z : ℝ) :
    LocallyLipschitz (coulombCusp N Z) := by
  have hn (i : Fin N) : LocallyLipschitz (fun x : Configuration N => ‖position x i‖) := by
    simpa only [Function.comp_def,electronPositionCLM_apply] using
      (lipschitzWith_one_norm.comp (electronPositionCLM i).lipschitz).locallyLipschitz
  have hp (i j : Fin N) :
      LocallyLipschitz (fun x : Configuration N => ‖position x i-position x j‖) := by
    simpa only [Function.comp_def,pairDifferenceCLM_apply] using
      (lipschitzWith_one_norm.comp (pairDifferenceCLM i j).lipschitz).locallyLipschitz
  have hns := locally_lipschitz_finset_sum Finset.univ _ (fun i _ => hn i)
  have hps := locally_lipschitz_finset_sum Finset.univ _ (fun i _ =>
    locally_lipschitz_finset_sum (Finset.univ.filter (fun j : Fin N => i<j)) _ (fun j _ => hp i j))
  exact (locally_lipschitz_real_mul (LocallyLipschitz.const (-Z)) hns).add
    (locally_lipschitz_real_mul (LocallyLipschitz.const (1/2:ℝ)) hps)

theorem coulombCusp_exp_locallyLipschitz (N : ℕ) (Z : ℝ) :
    LocallyLipschitz (fun x => Real.exp (coulombCusp N Z x)) :=
  (Real.contDiff_exp (n := 1)).locallyLipschitz.comp (coulombCusp_locallyLipschitz N Z)

#print axioms coulombCusp_locallyLipschitz
#print axioms coulombCusp_exp_locallyLipschitz
end TheoremT.Continuum
