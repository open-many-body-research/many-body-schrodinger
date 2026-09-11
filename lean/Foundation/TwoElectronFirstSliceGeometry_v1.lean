import TwoElectronCoordinateProduct_v1
import ProductL2Slices_v1
import HardyLaplacianCore_v1

/-! First-coordinate smooth slices in the actual Configuration 1 and Configuration 2 spaces. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

def twoElectronFirstSlice (F : SpatialL2 2) (y : Configuration 1) : SpatialL2 1 :=
  ProductL2.sliceLeft (twoElectronL2ProductEquiv F) y

def twoElectronFirstInsertion : Configuration 1 →L[ℝ] Configuration 2 :=
  twoElectronConfigurationProduct.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ (Configuration 1) (Configuration 1))

theorem twoElectronFirstInsertion_basis (k : Fin 3) :
    twoElectronFirstInsertion (coordinateVector (N := 1) (0,k)) =
      coordinateVector (N := 2) (0,k) := by
  apply (WithLp.ext_iff 2).mpr
  funext q
  rcases q with ⟨i,l⟩
  fin_cases i
  · change twoElectronConfigurationProduct.symm (coordinateVector (N := 1) (0,k),0) (0,l) = _
    rw [twoElectronConfigurationProduct_symm_first]
    simp [coordinateVector]
  · change twoElectronConfigurationProduct.symm (coordinateVector (N := 1) (0,k),0) (1,l) = _
    rw [twoElectronConfigurationProduct_symm_second]
    simp [coordinateVector]

theorem twoElectronReassembleFirst_hasFDerivAt (y x : Configuration 1) :
    HasFDerivAt (fun z => twoElectronConfigurationProduct.symm (z,y))
      twoElectronFirstInsertion x :=
  twoElectronConfigurationProduct.symm.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x y)

theorem twoElectronReassembleFirst_contDiff (y : Configuration 1) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun x => twoElectronConfigurationProduct.symm (x,y)) :=
  twoElectronConfigurationProduct.symm.contDiff.comp (contDiff_id.prodMk contDiff_const)

theorem twoElectronFirstSlice_compact {u : Configuration 2 → ℂ}
    (hu : HasCompactSupport u) (y : Configuration 1) :
    HasCompactSupport (fun x => u (twoElectronConfigurationProduct.symm (x,y))) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (hu.isCompact.image (continuous_fst.comp twoElectronConfigurationProduct.continuous))
  intro x hx
  refine ⟨twoElectronConfigurationProduct.symm (x,y),subset_tsupport u hx,?_⟩
  simp

theorem twoElectronFirstSlice_smoothPartial {u : Configuration 2 → ℂ}
    (hu : ContDiff ℝ 1 u) (y x : Configuration 1) (k : Fin 3) :
    smoothPartial (fun z => u (twoElectronConfigurationProduct.symm (z,y))) (0,k) x =
      smoothPartial u (0,k) (twoElectronConfigurationProduct.symm (x,y)) := by
  have hd := ((hu.differentiable (by norm_num)
    (twoElectronConfigurationProduct.symm (x,y))).hasFDerivAt).comp x
      (twoElectronReassembleFirst_hasFDerivAt y x)
  have hv := congrArg (fun L : Configuration 1 →L[ℝ] ℂ => L (coordinateVector (0,k))) hd.fderiv
  simpa only [smoothPartial,Function.comp_def,ContinuousLinearMap.comp_apply,
    twoElectronFirstInsertion_basis] using hv

theorem twoElectronFirstSlice_ae_of_ae (F : SpatialL2 2) (u : Configuration 2 → ℂ)
    (hu : F =ᵐ[volume] u) :
    ∀ᵐ y ∂volume, twoElectronFirstSlice F y =ᵐ[volume]
      fun x => u (twoElectronConfigurationProduct.symm (x,y)) := by
  have hprod : twoElectronL2ProductEquiv F =ᵐ[(volume : Measure (Configuration 1)).prod volume]
      fun p => u (twoElectronConfigurationProduct.symm p) :=
    (twoElectronL2ToProduct_ae F).trans
      (twoElectronConfigurationProduct_symm_measurePreserving.quasiMeasurePreserving.ae hu)
  have hs := (Measure.measurePreserving_swap
    (μ := (volume : Measure (Configuration 1))) (ν := volume)).quasiMeasurePreserving.ae hprod
  filter_upwards [ProductL2.sliceLeft_ae_coe (twoElectronL2ProductEquiv F),
    Measure.ae_ae_of_ae_prod hs] with y hy hs
  exact hy.trans hs

#print axioms twoElectronFirstInsertion_basis
#print axioms twoElectronFirstSlice_smoothPartial
#print axioms twoElectronFirstSlice_ae_of_ae
end TheoremT.Continuum
