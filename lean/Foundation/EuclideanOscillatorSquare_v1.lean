import EuclideanOscillatorCross_v1
import EuclideanOscillatorNorm_v1

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff RealInnerProductSpace
namespace TheoremT.Continuum
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem oscillatorLaplacian_contDiff {u : EuclideanSpace ℝ ι → ℂ}
    (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (oscillatorLaplacian u) := by
  change ContDiff ℝ ∞ (fun x => ∑ k : ι, oscillatorPartial (oscillatorPartial u k) k x)
  exact ContDiff.sum (fun k _ => oscillatorPartial_contDiff (oscillatorPartial_contDiff hu k) k)

theorem oscillatorLaplacian_compact {u : EuclideanSpace ℝ ι → ℂ}
    (hc : HasCompactSupport u) : HasCompactSupport (oscillatorLaplacian u) := by
  have he : oscillatorLaplacian u = ∑ k : ι, oscillatorPartial (oscillatorPartial u k) k := by
    funext x
    simp [oscillatorLaplacian]
  rw [he]
  exact HasCompactSupport.finset_sum (fun k _ => oscillatorPartial_compact (oscillatorPartial_compact hc k) k)

theorem euclidean_oscillator_norm_square_pointwise (a : ℝ) (u : EuclideanSpace ℝ ι → ℂ)
    (x : EuclideanSpace ℝ ι) :
    ‖euclideanOscillator a u x‖^2 = ‖oscillatorLaplacian u x‖^2+
      a^4*(‖x‖^4*‖u x‖^2)+2*a^2*inner ℝ (-(oscillatorLaplacian u x)) (‖x‖^2 • u x) := by
  change ‖-(oscillatorLaplacian u x)+(a^2*‖x‖^2) • u x‖^2 = _
  rw [norm_add_sq_real]
  simp only [norm_neg,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,
    real_inner_smul_right]
  ring

theorem compact_euclidean_oscillator_norm_square (a : ℝ) {u : EuclideanSpace ℝ ι → ℂ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    (∫ x,‖euclideanOscillator a u x‖^2) =
      (∫ x,‖oscillatorLaplacian u x‖^2)+a^4*(∫ x,‖x‖^4*‖u x‖^2)+
        2*a^2*((∫ x,‖x‖^2*(∑ k : ι,‖oscillatorPartial u k x‖^2))-
          (Fintype.card ι : ℝ)*(∫ x,‖u x‖^2)) := by
  have hL : Integrable (fun x => ‖oscillatorLaplacian u x‖^2) volume := by
    simpa only [real_inner_self_eq_norm_sq] using compact_real_inner_integrable_general
      (μ := volume) (oscillatorLaplacian_contDiff hu).continuous
      (oscillatorLaplacian_contDiff hu).continuous (oscillatorLaplacian_compact hc)
  have hW : Integrable (fun x => ‖x‖^4*‖u x‖^2) volume := by
    apply ((continuous_norm.pow 4).mul (hu.continuous.norm.pow 2)).integrable_of_hasCompactSupport
    apply hc.mono
    intro x hx
    change u x ≠ 0
    intro hz
    exact hx (by simp [hz])
  have hC : Integrable (fun x => inner ℝ (-(oscillatorLaplacian u x)) (‖x‖^2 • u x)) volume :=
    compact_real_inner_integrable_general (oscillatorLaplacian_contDiff hu).continuous.neg
      ((continuous_norm.pow 2).smul hu.continuous) (oscillatorLaplacian_compact hc).neg
  have hWa : Integrable (fun x => a^4*(‖x‖^4*‖u x‖^2)) volume := hW.const_mul _
  have hCa : Integrable (fun x => (2*a^2)*inner ℝ (-(oscillatorLaplacian u x)) (‖x‖^2 • u x)) volume := hC.const_mul _
  have hsum : Integrable (fun x => ‖oscillatorLaplacian u x‖^2+a^4*(‖x‖^4*‖u x‖^2)) volume := hL.add hWa
  simp_rw [euclidean_oscillator_norm_square_pointwise]
  rw [integral_add hsum hCa,integral_add hL hWa,integral_const_mul,integral_const_mul,
    compact_euclidean_oscillator_cross hu hc]

#print axioms compact_euclidean_oscillator_norm_square
end TheoremT.Continuum
