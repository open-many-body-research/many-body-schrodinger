import SphericalAverageSupport_v1
import Mathlib.MeasureTheory.Function.L2Space

/-! Exact centering and variance on an actual finite positive measure space.
The normalized mean is an explicit Bochner integral divided by total mass.
Square-integrability and all needed integral manipulations are proved from L². -/
noncomputable section
open MeasureTheory Set
namespace TheoremT.Polar

variable {α F : Type*} [MeasurableSpace α]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  (ν : Measure α) [IsFiniteMeasure ν]

def finiteMeasureMean (h : α → F) : F := (ν.real univ)⁻¹ • ∫ x, h x ∂ν

theorem mass_smul_finiteMeasureMean (hM : 0 < ν.real univ) (h : α → F) :
    ν.real univ • finiteMeasureMean ν h = ∫ x, h x ∂ν := by
  rw [finiteMeasureMean, smul_smul, mul_inv_cancel₀ hM.ne', one_smul]

theorem finiteMeasureMean_centered_integral (hM : 0 < ν.real univ)
    {h : α → F} (hh : Integrable h ν) :
    (∫ x, h x - finiteMeasureMean ν h ∂ν) = 0 := by
  rw [integral_sub hh (integrable_const _), integral_const,
    mass_smul_finiteMeasureMean ν hM, sub_self]

theorem finiteMeasureMean_centered_memLp {h : α → F} (hh : MemLp h 2 ν) :
    MemLp (fun x => h x - finiteMeasureMean ν h) 2 ν := hh.sub (memLp_const _)

theorem finiteMeasureMean_variance (hM : 0 < ν.real univ)
    {h : α → F} (hh : MemLp h 2 ν) :
    (∫ x, ‖h x - finiteMeasureMean ν h‖ ^ 2 ∂ν) +
      ν.real univ * ‖finiteMeasureMean ν h‖ ^ 2 = ∫ x, ‖h x‖ ^ 2 ∂ν := by
  let m := finiteMeasureMean ν h
  have hI : Integrable h ν := hh.integrable (by norm_num)
  have hN : Integrable (fun x => ‖h x‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hh.aestronglyMeasurable).mp hh
  have hinner : Integrable (fun x => inner ℝ m (h x)) ν := hI.const_inner m
  have he : (fun x => ‖h x - m‖ ^ 2) =
      fun x => ‖h x‖ ^ 2 - 2 * inner ℝ m (h x) + ‖m‖ ^ 2 := by
    funext x
    rw [norm_sub_sq_real, real_inner_comm (h x) m]
  have hcross : inner ℝ m (∫ x, h x ∂ν) = ν.real univ * ‖m‖ ^ 2 := by
    rw [← mass_smul_finiteMeasureMean ν hM h]
    exact real_inner_smul_right _ _ _ |>.trans (by rw [real_inner_self_eq_norm_sq])
  change (∫ x, ‖h x - m‖ ^ 2 ∂ν) + ν.real univ * ‖m‖ ^ 2 = _
  have hsub : Integrable (fun x => ‖h x‖ ^ 2 - 2 * inner ℝ m (h x)) ν :=
    hN.sub (hinner.const_mul 2)
  rw [he, integral_add hsub (integrable_const _),
    integral_sub hN (hinner.const_mul 2), integral_const_mul,
    integral_inner hI, hcross, integral_const, smul_eq_mul]
  ring

theorem finiteMeasureMean_norm_sq_le (hM : 0 < ν.real univ)
    {h : α → F} (hh : MemLp h 2 ν) :
    ν.real univ * ‖finiteMeasureMean ν h‖ ^ 2 ≤ ∫ x, ‖h x‖ ^ 2 ∂ν := by
  have hv := finiteMeasureMean_variance ν hM hh
  have hn : 0 ≤ ∫ x, ‖h x - finiteMeasureMean ν h‖ ^ 2 ∂ν :=
    integral_nonneg (fun x => sq_nonneg _)
  linarith

#print axioms finiteMeasureMean_centered_integral
#print axioms finiteMeasureMean_centered_memLp
#print axioms finiteMeasureMean_variance
#print axioms finiteMeasureMean_norm_sq_le
end TheoremT.Polar
