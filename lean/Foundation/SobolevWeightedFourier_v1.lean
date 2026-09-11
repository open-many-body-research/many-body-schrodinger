import ActualWeakOrderSobolev_v1
import LpDistributionIdentification_v1

noncomputable section
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem MemSobolev.actual_fourier_weight_memLp {s : ℝ}
    (f : Lp ℂ 2 (volume : Measure E)) (hf : MemSobolev s 2 (f : 𝓢'(E,ℂ))) :
    MemLp (fun x : E => ((1+‖x‖^2)^(s/2) : ℝ) • (𝓕 f) x) 2 volume := by
  obtain ⟨g,hg⟩ := memSobolev_iff_exists_smulLeftCLM_fourier.mp hf
  rw [Lp.fourier_toTemperedDistribution_eq] at hg
  have hh := memLp_smul_of_toTemperedDistribution_eq (𝓕 f) g
    (m := fun x : E => (((1+‖x‖^2)^(s/2) : ℝ) : ℂ)) (by fun_prop) hg.symm
  simpa only [Complex.coe_smul] using hh

theorem inverse_bessel_weight_memLp {s : ℝ} (hs : Module.finrank ℝ E < 2*s) :
    MemLp (fun x : E => (1+‖x‖^2)^(-s/2)) 2 volume := by
  constructor
  · have h : (fun x : E => (1+‖x‖^2)^(-s/2)).HasTemperateGrowth := by fun_prop
    exact h.1.continuous.aestronglyMeasurable
  · rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
    suffices h : ∫⁻ a : E, ENNReal.ofReal ‖(1+‖a‖^2)^(-s)‖ < ⊤ from by
      norm_cast
      simp_rw [ofReal_norm] at h
      simp_rw [← enorm_pow]
      convert h
      rw [← Real.rpow_mul_natCast (by positivity)]
      simp
    apply ((integrable_rpow_neg_one_add_norm_sq hs).congr _).lintegral_lt_top
    filter_upwards with x
    rw [Real.norm_eq_abs,abs_eq_self.mpr (by positivity)]
    congr 1
    ring

#print axioms MemSobolev.actual_fourier_weight_memLp
#print axioms inverse_bessel_weight_memLp
end TheoremT.Continuum
