import KSVectorLaplacian_v1
import KSHessianTraceContraction_v1
import SecondDirectionalComposition_v1

/-! The exact KS Laplacian chain identity for genuinely C2 functions.
This is not yet the physical weak-pullback/removability theorem. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

theorem second_directional_fderiv_evaluation {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {φ : E → G} (hφ : ContDiff ℝ 2 φ) (x v w : E) :
    fderiv ℝ (fun z => fderiv ℝ φ z v) x w =
      fderiv ℝ (fun z => fderiv ℝ φ z) x w v := by
  have hd : Differentiable ℝ (fun z => fderiv ℝ φ z) :=
    (show ContDiff ℝ 1 (fun z => fderiv ℝ φ z) from hφ.fderiv_right (by norm_num)).differentiable (by norm_num)
  rw [fderiv_clm_apply (hd x) (differentiableAt_const v)]
  simp

theorem ks_laplacian_composition {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {φ : Position → G} (hφ : ContDiff ℝ 2 φ) (y : KSSpace) :
    (∑ k : Fin 4, fderiv ℝ (fun x => fderiv ℝ (φ ∘ ksMap) x (ksBasis k)) y (ksBasis k)) =
      (4*‖y‖^2) • ∑ i : Fin 3, fderiv ℝ
        (fun x => fderiv ℝ φ x (ksTargetBasis i)) (ksMap y) (ksTargetBasis i) := by
  have hK : ContDiff ℝ 2 ksMap := ksMap_contDiff.of_le (by simp)
  simp_rw [second_directional_composition hφ hK]
  rw [Finset.sum_add_distrib,← map_sum,ksMap_vector_laplacian_zero,map_zero,zero_add,
    ks_bilinear_trace_contraction]
  simp_rw [second_directional_fderiv_evaluation hφ]

#print axioms second_directional_fderiv_evaluation
#print axioms ks_laplacian_composition
end TheoremT.Continuum
