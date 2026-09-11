import SobolevToActualH2_v1
import FourierLaplacianRepresentation_v1

/-! A weighted Fourier-domain input gives the actual weak H2 domain.
Conversely an L2 distributional Laplacian proves this weighted membership.
No unbounded polynomial multiplier is assumed to preserve all of L2. -/

noncomputable section
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Laplacian

namespace TheoremT.Continuum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem fourier_normSq_memLp_of_laplacian
    (f w : Lp ℂ 2 (volume : Measure E))
    (h : Δ (f : 𝓢'(E, ℂ)) = (w : 𝓢'(E, ℂ))) :
    MemLp (fun x : E => Complex.ofReal (‖x‖ ^ 2) * (𝓕 f) x) 2 volume := by
  let c : ℂ := ((-(2 * Real.pi) ^ 2 : ℝ) : ℂ)
  have hc : c ≠ 0 := by
    dsimp [c]
    norm_cast
    exact neg_ne_zero.mpr (pow_ne_zero _ (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  have hp := (fourier_laplacian_product_memLp f w h).const_mul c⁻¹
  convert hp using 1
  ext x
  simp [c, Complex.ofReal_mul, ← mul_assoc, hc]

theorem memSobolev_two_of_fourier_normSq_memLp
    (f : Lp ℂ 2 (volume : Measure E))
    (hf : MemLp (fun x : E => Complex.ofReal (‖x‖ ^ 2) * (𝓕 f) x) 2 volume) :
    MemSobolev 2 2 (f : 𝓢'(E, ℂ)) := by
  let g : Lp ℂ 2 (volume : Measure E) :=
    hf.toLp (fun x : E => Complex.ofReal (‖x‖ ^ 2) * (𝓕 f) x)
  have hg : (g : 𝓢'(E, ℂ)) = smulLeftCLM ℂ
      (fun x : E => Complex.ofReal (‖x‖ ^ 2))
      ((𝓕 f : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E, ℂ)) :=
    toTemperedDistribution_smul_of_product_memLp (𝓕 f) (by fun_prop) hf
  refine ⟨f + 𝓕⁻ g, ?_⟩
  rw [besselPotential_two_eq_add_multiplier, fourierMultiplierCLM_apply,
    Lp.fourier_toTemperedDistribution_eq, ← hg,
    Lp.fourierInv_toTemperedDistribution_eq]
  simp only [← Lp.toTemperedDistributionCLM_apply, map_add]

theorem hasH2_of_fourier_normSq_memLp {N : ℕ} (f : SpatialL2 N)
    (hf : MemLp (fun x : Configuration N =>
      Complex.ofReal (‖x‖ ^ 2) * (𝓕 f) x) 2 volume) :
    HasH2 f :=
  hasH2_of_memSobolev_two f (memSobolev_two_of_fourier_normSq_memLp f hf)

#print axioms fourier_normSq_memLp_of_laplacian
#print axioms memSobolev_two_of_fourier_normSq_memLp
#print axioms hasH2_of_fourier_normSq_memLp

end TheoremT.Continuum
