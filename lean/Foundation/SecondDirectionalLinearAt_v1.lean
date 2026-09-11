import KSLaplacianCompositionAt_v1

noncomputable section
namespace TheoremT.Continuum

theorem second_directional_linear_at {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E →L[ℝ] F) {f : F → G} (x v w : E)
    (hf : ContDiffAt ℝ 2 f (L x)) :
    fderiv ℝ (fun y => fderiv ℝ (f ∘ L) y v) x w =
      fderiv ℝ (fun y => fderiv ℝ f y (L v)) (L x) (L w) := by
  rw [second_directional_composition_at x v w hf L.contDiff.contDiffAt,
    second_directional_fderiv_evaluation_at _ _ _ hf]
  have he (y : E) : fderiv ℝ L y=L := L.hasFDerivAt.fderiv
  simp only [he,fderiv_const_apply,ContinuousLinearMap.zero_apply,map_zero,zero_add]

#print axioms second_directional_linear_at
end TheoremT.Continuum
