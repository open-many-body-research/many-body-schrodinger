import FourierDerivativeRepresentation_v1
import FourierLaplacianRepresentation_v1
import WeakPartialDistribution_v1

/-! Every actual ordered mixed weak second derivative has L² norm at most
the actual distributional Laplacian norm. Fourier normalization constants are
kept explicit and cancel, on the original physical configuration space. -/
noncomputable section
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Laplacian
namespace TheoremT.Continuum

theorem weak_mixed_norm_le_laplacian {N : ℕ} {f d e w : SpatialL2 N}
    {k l : Coordinate N} (hd : WeakPartial f d k) (he : WeakPartial d e l)
    (hw : Δ (f : 𝓢'(Configuration N, ℂ)) = (w : 𝓢'(Configuration N, ℂ))) :
    ‖e‖ ≤ ‖w‖ := by
  rw [← Lp.norm_fourier_eq e,← Lp.norm_fourier_eq w]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [fourier_derivative_ae f d (coordinateVector k) hd.temperedDistribution_derivative,
    fourier_derivative_ae d e (coordinateVector l) he.temperedDistribution_derivative,
    fourier_laplacian_ae f w hw] with x hdx hex hwx
  rw [hex,hdx,hwx]
  have hk : |inner ℝ x (coordinateVector k)| ≤ ‖x‖ := by
    simpa [coordinateVector] using abs_real_inner_le_norm x (coordinateVector k)
  have hl : |inner ℝ x (coordinateVector l)| ≤ ‖x‖ := by
    simpa [coordinateVector] using abs_real_inner_le_norm x (coordinateVector l)
  have hprod := mul_le_mul hl hk (abs_nonneg _) (norm_nonneg x)
  have hc : ‖(2*Real.pi*Complex.I : ℂ)‖ = 2*Real.pi := by
    norm_num [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  simp only [norm_mul,hc,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_neg,abs_pow,
    abs_norm,abs_of_pos (by positivity : (0 : ℝ) < 2*Real.pi)]
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hprod (by positivity : (0 : ℝ) ≤ (2*Real.pi)^2))
    (norm_nonneg ((𝓕 f) x))
  nlinarith

#print axioms weak_mixed_norm_le_laplacian
end TheoremT.Continuum
