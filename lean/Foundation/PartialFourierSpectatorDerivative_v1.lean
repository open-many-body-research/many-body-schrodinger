import CompactFourierDirectional_v1
import PartialSpectatorDirectional_v1

noncomputable section
open MeasureTheory
open scoped ContDiff FourierTransform RealInnerProductSpace
namespace TheoremT.Continuum
variable {Y T : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T]
  [MeasurableSpace T] [BorelSpace T] [FiniteDimensional ℝ T]

theorem partialFourier_tDirectional {G : Y × T → ℂ} (hG : ContDiff ℝ ∞ G)
    (hc : HasCompactSupport G) (ξ v : T) (y : Y) :
    partialFourier (partialTDirectional G v) ξ y =
      (2*Real.pi*Complex.I)*(⟪ξ,v⟫ : ℂ)*partialFourier G ξ y := by
  have h := compact_fourier_directional (compact_slice_contDiff hG y)
    (compact_slice_hasCompactSupport hc y) ξ v
  simpa only [partialFourier,partialTDirectional_eq_slice hG] using h

theorem partialFourier_second_tDirectional {G : Y × T → ℂ} (hG : ContDiff ℝ ∞ G)
    (hc : HasCompactSupport G) (ξ v : T) (y : Y) :
    partialFourier (partialTDirectional (partialTDirectional G v) v) ξ y =
      -((2*Real.pi)^2*⟪ξ,v⟫^2 : ℝ) • partialFourier G ξ y := by
  rw [partialFourier_tDirectional (partialTDirectional_contDiff hG v)
    (partialTDirectional_hasCompactSupport hc v),partialFourier_tDirectional hG hc]
  simp only [Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_mul,Complex.ofReal_pow,
    Complex.ofReal_ofNat]
  calc
    _ = Complex.I^2 * ((2*Real.pi : ℝ) : ℂ)^2 * (⟪ξ,v⟫ : ℂ)^2 * partialFourier G ξ y := by
      push_cast
      ring
    _ = _ := by rw [Complex.I_sq]; push_cast; ring

#print axioms partialFourier_tDirectional
#print axioms partialFourier_second_tDirectional
end TheoremT.Continuum
