import TwoElectronFirstSliceGeometry_v1
import TwoElectronTensorExchange_v1
import WeakPermutation_v2

/-! Actual tensor products preserve distributional coordinate derivatives.
The proof integrates the literal compact test identity on each physical slice. -/
noncomputable section
open MeasureTheory Filter
namespace TheoremT.Continuum

theorem twoElectronTensor_test_integral (f g : SpatialL2 1)
    {φ : Configuration 2 → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    (∫ q, φ q • twoElectronTensor f g q) =
      ∫ y, (∫ x, φ (twoElectronConfigurationProduct.symm (x,y)) • f x) * g y := by
  have he : (fun p : Configuration 1 × Configuration 1 =>
      φ (twoElectronConfigurationProduct.symm p) •
        twoElectronTensor f g (twoElectronConfigurationProduct.symm p)) =ᵐ[
          (volume : Measure (Configuration 1)).prod volume]
      fun p => (φ (twoElectronConfigurationProduct.symm p) • f p.1) * g p.2 := by
    filter_upwards [twoElectronConfigurationProduct_symm_measurePreserving.quasiMeasurePreserving.ae
      (twoElectronTensor_ae f g)] with p hp
    simp only [twoElectronConfigurationProduct.apply_symm_apply] at hp
    rw [hp]
    simp only [smul_mul_assoc]
  have hi := (twoElectronConfigurationProduct_symm_measurePreserving.integrable_comp_of_integrable
    (test_integrable (twoElectronTensor f g) hφ hc)).congr he
  calc
    _ = ∫ p : Configuration 1 × Configuration 1,
        φ (twoElectronConfigurationProduct.symm p) •
          twoElectronTensor f g (twoElectronConfigurationProduct.symm p) :=
      (twoElectronConfigurationProduct_symm_measurePreserving.integral_comp
        twoElectronConfigurationProduct.symm.toHomeomorph.measurableEmbedding
        (fun q => φ q • twoElectronTensor f g q)).symm
    _ = ∫ p : Configuration 1 × Configuration 1,
        (φ (twoElectronConfigurationProduct.symm p) • f p.1) * g p.2 :=
      integral_congr_ae he
    _ = _ := by
      change (∫ p : Configuration 1 × Configuration 1,
        (φ (twoElectronConfigurationProduct.symm p) • f p.1) * g p.2
          ∂(volume : Measure (Configuration 1)).prod volume) = _
      rw [integral_prod_symm _ hi]
      congr 1
      funext y
      exact integral_mul_const (g y) (fun x => φ (twoElectronConfigurationProduct.symm (x,y)) • f x)

theorem twoElectronTensor_weakPartial_first {f df : SpatialL2 1}
    (g : SpatialL2 1) (k : Fin 3) (hf : WeakPartial f df (0,k)) :
    WeakPartial (twoElectronTensor f g) (twoElectronTensor df g) (0,k) := by
  intro φ hφ hc
  have hdφ : Continuous (fun q => fderiv ℝ φ q (coordinateVector (0,k))) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  rw [twoElectronTensor_test_integral df g hφ.continuous hc,
    twoElectronTensor_test_integral f g hdφ (hc.fderiv_apply ℝ (coordinateVector (0,k))),
    ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with y
  have hcs : HasCompactSupport (fun x => φ (twoElectronConfigurationProduct.symm (x,y))) := by
    apply HasCompactSupport.of_support_subset_isCompact
      (hc.isCompact.image (continuous_fst.comp twoElectronConfigurationProduct.continuous))
    intro x hx
    exact ⟨twoElectronConfigurationProduct.symm (x,y),subset_tsupport φ hx,by simp⟩
  have hs := hf (fun x => φ (twoElectronConfigurationProduct.symm (x,y)))
    (hφ.comp (twoElectronReassembleFirst_contDiff y)) hcs
  have hd (x : Configuration 1) :
      fderiv ℝ (fun z => φ (twoElectronConfigurationProduct.symm (z,y))) x
        (coordinateVector (0,k)) =
      fderiv ℝ φ (twoElectronConfigurationProduct.symm (x,y)) (coordinateVector (0,k)) := by
    have h := ((hφ.differentiable (by simp)
      (twoElectronConfigurationProduct.symm (x,y))).hasFDerivAt).comp x
        (twoElectronReassembleFirst_hasFDerivAt y x)
    have hv := congrArg (fun L : Configuration 1 →L[ℝ] ℝ =>
      L (coordinateVector (0,k))) h.fderiv
    simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,
      twoElectronFirstInsertion_basis] using hv
  simp_rw [hd] at hs
  rw [hs,neg_mul]

theorem twoElectronTensor_weakPartial_second (f : SpatialL2 1)
    {g dg : SpatialL2 1} (k : Fin 3) (hg : WeakPartial g dg (0,k)) :
    WeakPartial (twoElectronTensor f g) (twoElectronTensor f dg) (1,k) := by
  have h := weakPartial_pullback twoElectronSwap
    (twoElectronTensor_weakPartial_first f k hg)
  rw [twoElectronTensor_swap,twoElectronTensor_swap] at h
  simpa [coordinatePermutation,twoElectronSwap] using h

#print axioms twoElectronTensor_test_integral
#print axioms twoElectronTensor_weakPartial_first
#print axioms twoElectronTensor_weakPartial_second
end TheoremT.Continuum
