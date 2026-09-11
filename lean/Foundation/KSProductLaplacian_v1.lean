import KSProductMapJets_v1

noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum
variable {S G : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem ksProductMap_laplacian_first {Φ : Position × S → G} (q : KSSpace × S)
    (hΦ : ContDiffAt ℝ 2 Φ (ksProductMap q)) :
    (∑ k : Fin 4, fderiv ℝ (fun z => fderiv ℝ (Φ ∘ ksProductMap) z (ksBasis k,0)) q (ksBasis k,0)) =
    (4*‖q.1‖^2) • ∑ k : Fin 3, fderiv ℝ
      (fun z => fderiv ℝ Φ z (ksTargetBasis k,0)) (ksProductMap q) (ksTargetBasis k,0) := by
  have hθ : ContDiffAt ℝ 2 ksProductMap q := ksProductMap_contDiff.contDiffAt.of_le (by simp)
  simp_rw [second_directional_composition_at q _ _ hΦ hθ,ksProductMap_second,ksProductMap_first]
  simp only [Finset.sum_add_distrib]
  have hzero : (∑ k : Fin 4, (fderiv ℝ
      (fun y => fderiv ℝ ksMap y (ksBasis k)) q.1 (ksBasis k), (0:S)))=0 := by
    change (∑ k : Fin 4, (ContinuousLinearMap.inl ℝ Position S)
      (fderiv ℝ (fun y => fderiv ℝ ksMap y (ksBasis k)) q.1 (ksBasis k)))=0
    rw [← map_sum,ksMap_vector_laplacian_zero,map_zero]
  rw [← map_sum,hzero,map_zero,zero_add]
  let B := fderiv ℝ (fun z => fderiv ℝ Φ z) (ksProductMap q)
  have hc := ks_bilinear_trace_contraction
    (B.bilinearComp (ContinuousLinearMap.inl ℝ Position S) (ContinuousLinearMap.inl ℝ Position S)) q.1
  simpa only [B,ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.inl_apply,
    ← second_directional_fderiv_evaluation_at _ _ _ hΦ] using hc

theorem ksProductMap_second_spectator {Φ : Position × S → G} (q : KSSpace × S)
    (hΦ : ContDiffAt ℝ 2 Φ (ksProductMap q)) (v w : S) :
    fderiv ℝ (fun z => fderiv ℝ (Φ ∘ ksProductMap) z (0,v)) q (0,w) =
      fderiv ℝ (fun z => fderiv ℝ Φ z (0,v)) (ksProductMap q) (0,w) := by
  have hθ : ContDiffAt ℝ 2 ksProductMap q := ksProductMap_contDiff.contDiffAt.of_le (by simp)
  rw [second_directional_composition_at q _ _ hΦ hθ,ksProductMap_first,ksProductMap_first,ksProductMap_second,
    second_directional_fderiv_evaluation_at _ _ _ hΦ]
  simp only [map_zero,fderiv_fun_const,zero_apply,zero_add]
  change (fderiv ℝ Φ (ksProductMap q)) (0 : Position × S)+_ = _
  rw [map_zero,zero_add]

#print axioms ksProductMap_laplacian_first
#print axioms ksProductMap_second_spectator
end TheoremT.Continuum
