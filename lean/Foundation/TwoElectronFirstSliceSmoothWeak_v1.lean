import TwoElectronFirstSliceGeometry_v1
import HardyWeakCore_v1

/-! Classical derivative compatibility gives actual weak derivatives on smooth slices. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum

theorem twoElectronFirstSlice_smooth_weakPartial (u : Configuration 2 → ℂ)
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) (F D : SpatialL2 2) (k : Fin 3)
    (hF : F =ᵐ[volume] u) (hD : D =ᵐ[volume] smoothPartial u (0,k)) :
    ∀ᵐ y ∂volume, WeakPartial (twoElectronFirstSlice F y) (twoElectronFirstSlice D y) (0,k) := by
  filter_upwards [twoElectronFirstSlice_ae_of_ae F u hF,
    twoElectronFirstSlice_ae_of_ae D (smoothPartial u (0,k)) hD] with y hyF hyD
  let v : Configuration 1 → ℂ := fun x => u (twoElectronConfigurationProduct.symm (x,y))
  have hv : ContDiff ℝ ∞ v := hu.comp (twoElectronReassembleFirst_contDiff y)
  have hvc : HasCompactSupport v := twoElectronFirstSlice_compact hc y
  have hvm : MemLp v 2 volume := hv.continuous.memLp_of_hasCompactSupport hvc
  have hdm : MemLp (smoothPartial v (0,k)) 2 volume :=
    (smoothPartial_contDiff hv (0,k)).continuous.memLp_of_hasCompactSupport
      (smoothPartial_compact hvc (0,k))
  have heF : twoElectronFirstSlice F y = hvm.toLp v :=
    Lp.ext (hyF.trans hvm.coeFn_toLp.symm)
  have heD : twoElectronFirstSlice D y = hdm.toLp (smoothPartial v (0,k)) := by
    apply Lp.ext
    filter_upwards [hyD,hdm.coeFn_toLp] with x hxD hx
    rw [hxD,hx]
    exact (twoElectronFirstSlice_smoothPartial (hu.of_le (by norm_num)) y x k).symm
  rw [heF,heD]
  exact classicalDerivative_to_WeakPartial (hv.of_le (by norm_num)) (0,k) hvm hdm

#print axioms twoElectronFirstSlice_smooth_weakPartial
end TheoremT.Continuum
