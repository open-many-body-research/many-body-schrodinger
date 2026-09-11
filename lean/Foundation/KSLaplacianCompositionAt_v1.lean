import KSLaplacianComposition_v1
import SecondDirectionalCompositionAt_v1

noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

theorem second_directional_fderiv_evaluation_at {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {φ : E → G} (x v w : E) (hφ : ContDiffAt ℝ 2 φ x) :
    fderiv ℝ (fun z => fderiv ℝ φ z v) x w =
      fderiv ℝ (fun z => fderiv ℝ φ z) x w v := by
  have hd : DifferentiableAt ℝ (fun z => fderiv ℝ φ z) x :=
    (show ContDiffAt ℝ 1 (fun z => fderiv ℝ φ z) x from hφ.fderiv_right (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hd (differentiableAt_const v)]
  simp

theorem ks_laplacian_composition_at {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {φ : Position → G} (y : KSSpace) (hφ : ContDiffAt ℝ 2 φ (ksMap y)) :
    (∑ k : Fin 4, fderiv ℝ (fun x => fderiv ℝ (φ ∘ ksMap) x (ksBasis k)) y (ksBasis k)) =
      (4*‖y‖^2) • ∑ i : Fin 3, fderiv ℝ
        (fun x => fderiv ℝ φ x (ksTargetBasis i)) (ksMap y) (ksTargetBasis i) := by
  have hK : ContDiffAt ℝ 2 ksMap y := ksMap_contDiff.contDiffAt.of_le (by simp)
  simp_rw [second_directional_composition_at y _ _ hφ hK]
  rw [Finset.sum_add_distrib,← map_sum,ksMap_vector_laplacian_zero,map_zero,zero_add,
    ks_bilinear_trace_contraction]
  simp_rw [second_directional_fderiv_evaluation_at _ _ _ hφ]

#print axioms ks_laplacian_composition_at
end TheoremT.Continuum
