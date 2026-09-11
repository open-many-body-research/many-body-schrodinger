import CompactPartialFourier_v1
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open MeasureTheory
open scoped ContDiff FourierTransform RealInnerProductSpace
namespace TheoremT.Continuum
variable {Y T : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T]
  [MeasurableSpace T] [BorelSpace T] [FiniteDimensional ℝ T]

theorem partialFourier_joint_stronglyMeasurable {G : Y × T → ℂ} (hG : Continuous G) :
    StronglyMeasurable (fun p : Y × T => partialFourier G p.2 p.1) := by
  have hK : Continuous (fun q : (Y × T) × T => partialFourierKernel q.1.2 q.2) := by
    unfold partialFourierKernel
    fun_prop
  have hp : Continuous (fun q : (Y × T) × T => (q.1.1,q.2)) := by fun_prop
  have hI := (hK.mul (hG.comp hp)).stronglyMeasurable.integral_prod_right' (ν := volume)
  simpa only [partialFourier,Real.fourier_eq',partialFourierKernel,smul_eq_mul,Pi.mul_apply,Function.comp_apply] using hI

#print axioms partialFourier_joint_stronglyMeasurable
end TheoremT.Continuum
