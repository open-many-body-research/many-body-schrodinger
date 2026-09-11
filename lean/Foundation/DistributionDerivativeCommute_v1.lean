import KSLaplacianCompositionAt_v1
import WeakLaplacianDistribution_v1
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

noncomputable section
open MeasureTheory TemperedDistribution LineDeriv
open scoped SchwartzMap Laplacian
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem schwartz_directional_derivatives_commute (φ : 𝓢(E,ℂ)) (v w : E) :
    ∂_{v} (∂_{w} φ) = ∂_{w} (∂_{v} φ) := by
  have he (a : E) : ((∂_{a} φ : 𝓢(E,ℂ)) : E → ℂ) =
      (fun x => fderiv ℝ φ x a) := by
    funext x
    exact SchwartzMap.lineDerivOp_apply_eq_fderiv a φ x
  ext x
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv,he]
  rw [second_directional_fderiv_evaluation_at _ _ _ (φ.smooth 2).contDiffAt,
    second_directional_fderiv_evaluation_at _ _ _ (φ.smooth 2).contDiffAt]
  exact ((φ.smooth 2).contDiffAt.isSymmSndFDerivAt (by norm_num)).eq v w

theorem distribution_directional_derivatives_commute (u : 𝓢'(E,ℂ)) (v w : E) :
    ∂_{v} (∂_{w} u) = ∂_{w} (∂_{v} u) := by
  ext φ
  simp only [TemperedDistribution.lineDerivOp_apply_apply,lineDerivOp_neg,map_neg,neg_neg]
  rw [schwartz_directional_derivatives_commute]

theorem distribution_laplacian_derivative_commute (u : 𝓢'(E,ℂ)) (v : E) :
    Δ (∂_{v} u) = ∂_{v} (Δ u) := by
  rw [laplacian_eq_sum (stdOrthonormalBasis ℝ E),laplacian_eq_sum (stdOrthonormalBasis ℝ E)]
  rw [lineDerivOp_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [distribution_directional_derivatives_commute u _ v,
    distribution_directional_derivatives_commute (∂_{stdOrthonormalBasis ℝ E k} u) _ v]

#print axioms distribution_laplacian_derivative_commute
end TheoremT.Continuum
