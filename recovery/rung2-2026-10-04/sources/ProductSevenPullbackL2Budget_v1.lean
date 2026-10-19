import ProductSevenCoordinateTransport_v1
import SpectatorIterationState_v1
import ActualL2IntegralCauchy_v1

/-! Exact restricted-volume transport and quantitative L2 control for the
literal seven-coordinate pullback. Actual MemLp is required before interpreting
the real L2 norm or estimating the integral. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum
open WeakGrushin

theorem sevenToProduct_restrict_measurePreserving (K : Set (Fin 7 → ℝ)) :
    MeasurePreserving sevenToProduct (volume.restrict K) (volume.restrict (sevenToProduct '' K)) := by
  refine ⟨sevenToProduct_measurePreserving.measurable,?_⟩
  have h := sevenToProduct.toHomeomorph.measurableEmbedding.restrict_map volume (sevenToProduct '' K)
  change (volume.map sevenToProduct).restrict (sevenToProduct '' K) =
    (volume.restrict (sevenToProduct ⁻¹' (sevenToProduct '' K))).map sevenToProduct at h
  rw [sevenToProduct_measurePreserving.map_eq,
    preimage_image_eq K sevenToProduct.injective] at h
  exact h.symm

theorem sevenToProduct_integral_restrict_image (K : Set (Fin 7 → ℝ))
    (f : Space (Fin 3) → ℝ) :
    (∫ x in K, f (sevenToProduct x)) = ∫ p in sevenToProduct '' K, f p :=
  (sevenToProduct_restrict_measurePreserving K).integral_comp
    sevenToProduct.toHomeomorph.measurableEmbedding f

theorem sevenToProduct_pullback_memLp
    {K : Set (Fin 7 → ℝ)} {Ω : Set (Space (Fin 3))}
    (hK : MapsTo sevenToProduct K Ω) {f : Space (Fin 3) → ℂ}
    (hf : MemLp f 2 (volume.restrict Ω)) :
    MemLp (f ∘ sevenToProduct) 2 (volume.restrict K) :=
  (hf.mono_measure (Measure.restrict_mono_set volume (image_subset_iff.mpr hK))).comp_measurePreserving
    (sevenToProduct_restrict_measurePreserving K)

theorem sevenToProduct_integral_sq_le
    {K : Set (Fin 7 → ℝ)} {Ω : Set (Space (Fin 3))}
    (hK : MapsTo sevenToProduct K Ω) {f : Space (Fin 3) → ℂ}
    (hf : MemLp f 2 (volume.restrict Ω)) :
    (∫ x in K, ‖f (sevenToProduct x)‖^2) ≤ ∫ p in Ω, ‖f p‖^2 := by
  rw [sevenToProduct_integral_restrict_image K (fun p => ‖f p‖^2)]
  apply integral_mono_measure (Measure.restrict_mono_set volume (image_subset_iff.mpr hK))
  · exact Filter.Eventually.of_forall (fun p => sq_nonneg ‖f p‖)
  · exact hf.integrable_norm_pow (by norm_num)

theorem sevenToProduct_sqrt_integral_le_eLpNorm
    {K : Set (Fin 7 → ℝ)} {Ω : Set (Space (Fin 3))}
    (hK : MapsTo sevenToProduct K Ω) {f : Space (Fin 3) → ℂ}
    (hf : MemLp f 2 (volume.restrict Ω)) :
    Real.sqrt (∫ x in K, ‖f (sevenToProduct x)‖^2) ≤ (eLpNorm f 2 (volume.restrict Ω)).toReal := by
  have h := Real.sqrt_le_sqrt (sevenToProduct_integral_sq_le hK hf)
  rw [← actual_l2_toLp_norm_sq_integral hf,Real.sqrt_sq (norm_nonneg _),Lp.norm_toLp] at h
  exact h

theorem sevenToProduct_regionL2Budget
    {K : Set (Fin 7 → ℝ)} {Ω : Set (Space (Fin 3))}
    (hK : MapsTo sevenToProduct K Ω) {f : Space (Fin 3) → ℂ} {W : ℝ}
    (hf : RegionL2Budget f Ω W) :
    MemLp (f ∘ sevenToProduct) 2 (volume.restrict K) ∧
      Real.sqrt (∫ x in K, ‖f (sevenToProduct x)‖^2) ≤ Real.sqrt W :=
  ⟨sevenToProduct_pullback_memLp hK hf.1,
    Real.sqrt_le_sqrt ((sevenToProduct_integral_sq_le hK hf.1).trans hf.2)⟩

theorem sevenToProduct_regionL2Budget_sq
    {K : Set (Fin 7 → ℝ)} {Ω : Set (Space (Fin 3))}
    (hK : MapsTo sevenToProduct K Ω) {f : Space (Fin 3) → ℂ} {M : ℝ}
    (hM : 0 ≤ M) (hf : RegionL2Budget f Ω (M^2)) :
    Real.sqrt (∫ x in K, ‖f (sevenToProduct x)‖^2) ≤ M := by
  simpa only [Real.sqrt_sq hM] using (sevenToProduct_regionL2Budget hK hf).2

end TheoremT.Continuum
