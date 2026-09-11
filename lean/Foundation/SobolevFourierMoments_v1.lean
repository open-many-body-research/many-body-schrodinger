import SobolevWeightedFourier_v1

noncomputable section
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem fourier_bessel_weight_integrable {s t : ℝ}
    (hs : Module.finrank ℝ E < 2*s) (f : Lp ℂ 2 (volume : Measure E))
    (hf : MemSobolev (s+t) 2 (f : 𝓢'(E,ℂ))) :
    Integrable (fun x : E => (1+‖x‖^2)^(t/2) * ‖(𝓕 f) x‖) := by
  have hw := (MemSobolev.actual_fourier_weight_memLp f hf).norm
  have hi := (inverse_bessel_weight_memLp hs).integrable_mul hw
  convert hi using 1
  ext x
  simp only [Pi.mul_apply]
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos (by positivity) _)]
  rw [← mul_assoc,← Real.rpow_add (by positivity)]
  congr 2
  ring

theorem all_weak_orders_fourier_moments {N : ℕ} (f : SpatialL2 N)
    (hf : ∀ m : ℕ, HasWeakOrder f m) (n : ℕ) :
    Integrable (fun x : Configuration N => ‖x‖^n * ‖(𝓕 f) x‖) := by
  let m : ℕ := Module.finrank ℝ (Configuration N)+1
  have hs : (Module.finrank ℝ (Configuration N) : ℝ) < 2*(2*(m:ℝ)) := by
    dsimp [m]
    push_cast
    nlinarith [show (0 : ℝ) ≤ (Module.finrank ℝ (Configuration N) : ℝ) by positivity]
  have hh : MemSobolev (2*(m:ℝ)+2*(n:ℝ)) 2 (f : 𝓢'(Configuration N,ℂ)) := by
    convert (hf (2*(m+n))).memSobolev_even (m+n) using 1 <;> push_cast <;> ring
  have hi := fourier_bessel_weight_integrable hs f hh
  apply hi.mono' ((continuous_norm.pow n).aestronglyMeasurable.mul (Lp.memLp (𝓕 f)).aestronglyMeasurable.norm)
  filter_upwards [] with x
  change ‖‖x‖^n * ‖(𝓕 f) x‖‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hb : ‖x‖ ≤ 1+‖x‖^2 := by nlinarith [sq_nonneg (‖x‖-1)]
  have hp := pow_le_pow_left₀ (norm_nonneg x) hb n
  have he : (2*(n:ℝ))/2=(n:ℝ) := by ring
  simpa only [he,Real.rpow_natCast] using mul_le_mul_of_nonneg_right hp (norm_nonneg ((𝓕 f) x))

#print axioms fourier_bessel_weight_integrable
#print axioms all_weak_orders_fourier_moments
end TheoremT.Continuum
