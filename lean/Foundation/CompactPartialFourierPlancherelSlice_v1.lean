import CompactPartialFourier_v1
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

noncomputable section
open MeasureTheory
open scoped ContDiff FourierTransform SchwartzMap
namespace TheoremT.Continuum
variable {Y T : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T]
  [MeasurableSpace T] [BorelSpace T] [FiniteDimensional ℝ T]

theorem compact_slice_contDiff {G : Y × T → ℂ} (hG : ContDiff ℝ ∞ G) (y : Y) :
    ContDiff ℝ ∞ (fun t => G (y,t)) :=
  hG.comp (contDiff_const.prodMk contDiff_id)

theorem partialFourier_slice_memLp {G : Y × T → ℂ} (hG : ContDiff ℝ ∞ G)
    (hc : HasCompactSupport G) (y : Y) (p : ENNReal) :
    MemLp (fun ξ => partialFourier G ξ y) p volume := by
  let f : 𝓢(T,ℂ) := (compact_slice_hasCompactSupport hc y).toSchwartzMap (compact_slice_contDiff hG y)
  exact (𝓕 f).memLp p volume

theorem partialFourier_slice_norm_sq_integrable {G : Y × T → ℂ} (hG : ContDiff ℝ ∞ G)
    (hc : HasCompactSupport G) (y : Y) : Integrable (fun ξ => ‖partialFourier G ξ y‖^2) volume :=
  (partialFourier_slice_memLp hG hc y 2).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)

theorem partialFourier_slice_plancherel {G : Y × T → ℂ} (hG : ContDiff ℝ ∞ G)
    (hc : HasCompactSupport G) (y : Y) :
    (∫ ξ, ‖partialFourier G ξ y‖^2) = ∫ t, ‖G (y,t)‖^2 := by
  let f : 𝓢(T,ℂ) := (compact_slice_hasCompactSupport hc y).toSchwartzMap (compact_slice_contDiff hG y)
  exact SchwartzMap.integral_norm_sq_fourier f

#print axioms partialFourier_slice_memLp
#print axioms partialFourier_slice_norm_sq_integrable
#print axioms partialFourier_slice_plancherel
end TheoremT.Continuum
