import ContinuumFoundation_v1
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section
open MeasureTheory Filter
namespace TheoremT.Continuum

theorem continuous_representative_invariant {N : ℕ}
    {f : SpatialL2 N} {u : Configuration N → ℂ} (hu : Continuous u)
    (hEq : (f : Configuration N → ℂ) =ᵐ[volume] u)
    (T : Configuration N ≃ₗᵢ[ℝ] Configuration N)
    (hT : (f : Configuration N → ℂ) =ᵐ[volume] (fun x => f (T x))) :
    ∀ x, u (T x)=u x := by
  have he : (fun x => u (T x)) =ᵐ[volume] u := by
    filter_upwards [hEq,hT,T.measurePreserving.quasiMeasurePreserving.ae hEq] with x hx ht htx
    exact htx.symm.trans (ht.symm.trans hx)
  exact congrFun (volume.eq_of_ae_eq he (hu.comp T.continuous) hu)

theorem continuous_representative_real {N : ℕ}
    {f : SpatialL2 N} {u : Configuration N → ℂ} (hu : Continuous u)
    (hEq : (f : Configuration N → ℂ) =ᵐ[volume] u)
    (hr : ∀ᵐ x ∂volume, (f x).im=0) : ∀ x, (u x).im=0 := by
  have he : (fun x => (u x).im) =ᵐ[volume] (fun _ => (0:ℝ)) := by
    filter_upwards [hEq,hr] with x hx hrx
    rw [← hx]
    exact hrx
  exact congrFun (volume.eq_of_ae_eq he (Complex.continuous_im.comp hu) continuous_const)

#print axioms continuous_representative_invariant
#print axioms continuous_representative_real
end TheoremT.Continuum
