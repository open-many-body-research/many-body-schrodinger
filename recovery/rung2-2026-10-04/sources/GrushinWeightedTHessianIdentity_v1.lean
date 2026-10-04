import GrushinYHessianIdentity_v1
import FstDirectionalJet_v1

/-! Weighted spectator Hessian identity on the actual ordinary product
space. Multiplication by a smooth spatial-only weight commutes with every
spectator derivative. Applying the existing compact Hessian identity to
the weighted function avoids an extra fiberwise integration argument. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem partialTDirectional_fst_smul
    {a : EuclideanSpace ℝ ι → ℝ} (ha : ContDiff ℝ ∞ a)
    {G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ} (hG : ContDiff ℝ ∞ G)
    (v : EuclideanSpace ℝ κ) (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) :
    partialTDirectional (fun q => a q.1 • G q) v p = a p.1 • partialTDirectional G v p := by
  change fderiv ℝ (fun q => a q.1 • G q) p (0,v) = _
  have haF : ContDiff ℝ ∞ (fun q : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ => a q.1) :=
    ha.comp contDiff_fst
  rw [cutoff_directional_product haF hG]
  rw [first_directional_fst (ha.differentiable (by simp))]
  simp only [ContinuousLinearMap.map_zero,zero_smul,zero_add]
  rfl

theorem partialTDirectional_second_fst_smul
    {a : EuclideanSpace ℝ ι → ℝ} (ha : ContDiff ℝ ∞ a)
    {G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ} (hG : ContDiff ℝ ∞ G)
    (v w : EuclideanSpace ℝ κ) (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) :
    partialTDirectional (partialTDirectional (fun q => a q.1 • G q) v) w p =
      a p.1 • partialTDirectional (partialTDirectional G v) w p := by
  have he : partialTDirectional (fun q => a q.1 • G q) v =
      (fun q => a q.1 • partialTDirectional G v q) := funext (partialTDirectional_fst_smul ha hG v)
  rw [he]
  exact partialTDirectional_fst_smul ha (partialTDirectional_contDiff hG v) w p

theorem compact_weighted_t_hessian_identity
    {a : EuclideanSpace ℝ ι → ℝ} (ha : ContDiff ℝ ∞ a)
    {G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ}
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) :
    (∫ p, ‖a p.1 • grushinTLaplacian G p‖^2
      ∂((volume : Measure (EuclideanSpace ℝ ι)).prod volume)) =
      ∑ i : κ, ∑ j : κ, ∫ p,
        ‖a p.1 • partialTDirectional (partialTDirectional G (oscillatorBasis i)) (oscillatorBasis j) p‖^2
        ∂((volume : Measure (EuclideanSpace ℝ ι)).prod volume) := by
  let U := fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ => a p.1 • G p
  have hU : ContDiff ℝ ∞ U := (ha.comp contDiff_fst).smul hG
  have hcU : HasCompactSupport U := by
    apply hc.mono
    intro p hp
    change G p ≠ 0
    intro hzero
    exact hp (by simp [U,hzero])
  letI := euclidean_product_volume_isAddHaar (ι := ι) (κ := κ)
  have hh := compact_finite_hessian_identity
    (μ := (volume : Measure (EuclideanSpace ℝ ι)).prod volume)
    hU hcU (fun i : κ => (0,oscillatorBasis i))
  change (∫ p, ‖∑ i : κ, partialTDirectional (partialTDirectional U (oscillatorBasis i)) (oscillatorBasis i) p‖^2
      ∂((volume : Measure (EuclideanSpace ℝ ι)).prod volume)) =
    ∑ i : κ, ∑ j : κ, ∫ p, ‖partialTDirectional (partialTDirectional U (oscillatorBasis i)) (oscillatorBasis j) p‖^2
      ∂((volume : Measure (EuclideanSpace ℝ ι)).prod volume) at hh
  simp only [U] at hh
  simp_rw [partialTDirectional_second_fst_smul ha hG] at hh
  simpa only [grushinTLaplacian,← Finset.smul_sum] using hh

theorem compact_grushin_full_weighted_hessian_bound {c : ℝ} (hc0 : 0 ≤ c)
    {G : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ κ → ℂ}
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) :
    (∑ i : Fin 4, ∑ j : Fin 4, ∫ p,
      ‖partialYDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis j) p‖^2
        ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume))+
    (∑ i : κ, ∑ j : κ, ∫ p,
      ‖(c*‖p.1‖^2) • partialTDirectional (partialTDirectional G (oscillatorBasis i)) (oscillatorBasis j) p‖^2
        ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume))+
    2*c*(∑ i : Fin 4, ∑ j : κ, ∫ p, ‖p.1‖^2*
      ‖partialTDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis j) p‖^2
        ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume)) ≤
      (3/2 : ℝ)*(∫ p, ‖euclideanGrushin c G p‖^2
        ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume)) := by
  have hw := compact_weighted_t_hessian_identity
    (contDiff_const.mul (contDiff_norm_sq ℝ) : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin 4) => c*‖y‖^2)) hG hc
  have hh := compact_grushin_full_y_hessian_bound hc0 hG hc
  simpa only [grushinWeightedT,hw] using hh

end TheoremT.Continuum
