import Mathlib.Analysis.Distribution.Sobolev
import Mathlib.Tactic

/-!
New distribution-level bridge, using mathlib's exp(-2*pi*i*inner) Fourier convention.
The hypothesis below is an equality for the actual distributional Laplacian.
It is not yet an equivalence with the project's compact-test WeakPartial domain.
-/

noncomputable section
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Laplacian LineDeriv

namespace TheoremT.Continuum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem besselPotential_two_eq_add_multiplier (T : 𝓢'(E, ℂ)) :
    besselPotential E ℂ 2 T = T +
      fourierMultiplierCLM ℂ (fun x : E => Complex.ofReal (‖x‖ ^ 2)) T := by
  have hfun : (fun x : E => (((1 + ‖x‖ ^ 2) ^ ((2 : ℝ) / 2) : ℝ) : ℂ)) =
      (fun _ : E => (1 : ℂ)) + (fun x : E => Complex.ofReal (‖x‖ ^ 2)) := by
    ext x
    simp
  rw [besselPotential, fourierMultiplierCLM_apply, hfun,
    smulLeftCLM_add (by fun_prop) (by fun_prop)]
  simp [fourierMultiplierCLM_apply]

theorem besselPotential_two_eq_sub_laplacian (T : 𝓢'(E, ℂ)) :
    besselPotential E ℂ 2 T = T - ((2 * Real.pi) ^ 2)⁻¹ • (Δ T) := by
  rw [besselPotential_two_eq_add_multiplier, laplacian_eq_fourierMultiplierCLM]
  have hpi : (2 * Real.pi) ^ 2 ≠ 0 := by positivity
  simp [smul_smul, hpi, sub_eq_add_neg]

theorem memSobolev_two_of_laplacian_l2
    (u w : Lp ℂ 2 (volume : Measure E))
    (hw : Δ (u : 𝓢'(E, ℂ)) = (w : 𝓢'(E, ℂ))) :
    MemSobolev 2 2 (u : 𝓢'(E, ℂ)) := by
  refine ⟨u - ((2 * Real.pi) ^ 2)⁻¹ • w, ?_⟩
  rw [besselPotential_two_eq_sub_laplacian, hw]
  simp only [← Lp.toTemperedDistributionCLM_apply, map_sub,
    ContinuousLinearMap.map_smul_of_tower]

#print axioms besselPotential_two_eq_add_multiplier
#print axioms besselPotential_two_eq_sub_laplacian
#print axioms memSobolev_two_of_laplacian_l2

end TheoremT.Continuum
