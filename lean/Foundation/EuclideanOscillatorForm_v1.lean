import CompactComplexOscillatorSquare_v1
import CompactDirectionalGreen_v1
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff RealInnerProductSpace
namespace TheoremT.Continuum
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev oscillatorBasis (k : ι) : EuclideanSpace ℝ ι := EuclideanSpace.single k 1

theorem euclidean_coordinate_smul_norm_sq_sum (x : EuclideanSpace ℝ ι) (z : ℂ) :
    (∑ k : ι, ‖x k • z‖^2)=‖x‖^2*‖z‖^2 := by
  simp_rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  rw [← Finset.sum_mul,EuclideanSpace.real_norm_sq_eq]

theorem compact_euclidean_oscillator_form_bound {u : EuclideanSpace ℝ ι → ℂ}
    (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) (a : ℝ) :
    (Fintype.card ι : ℝ)*a*(∫ x, ‖u x‖^2) ≤
      (∫ x, ∑ k : ι, ‖fderiv ℝ u x (oscillatorBasis k)‖^2)+
        a^2*(∫ x, ‖x‖^2*‖u x‖^2) := by
  have hb (k : ι) := compact_complex_oscillator_directional_bound (μ := volume)
    (EuclideanSpace.proj k) (oscillatorBasis k) (by simp [oscillatorBasis]) hu hc a
  have h := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hb k)
  have hD (k : ι) : Integrable (fun x => ‖fderiv ℝ u x (oscillatorBasis k)‖^2) volume := by
    have hd : Continuous (fun x => fderiv ℝ u x (oscillatorBasis k)) :=
      (hu.continuous_fderiv_apply (by norm_num)).comp (continuous_id.prodMk continuous_const)
    simpa only [real_inner_self_eq_norm_sq] using compact_real_inner_integrable_general
      hd hd (hc.fderiv_apply ℝ (oscillatorBasis k))
  have hW (k : ι) : Integrable (fun x => ‖x k • u x‖^2) volume := by
    have hR : Continuous (fun x : EuclideanSpace ℝ ι => x k) := (EuclideanSpace.proj k).continuous
    have hC : Continuous (fun x : EuclideanSpace ℝ ι => (x k : ℂ)) := Complex.continuous_ofReal.comp hR
    have hw : Continuous (fun x => (x k : ℂ)*u x) := hC.mul hu.continuous
    have hcW : HasCompactSupport (fun x => (x k : ℂ)*u x) := hc.mul_left
    have hI := compact_real_inner_integrable_general (μ := volume) hw hw hcW
    simpa only [real_inner_self_eq_norm_sq, Complex.real_smul] using hI
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.sum_add_distrib,
    ← Finset.mul_sum] at h
  change _ ≤ (∑ k : ι,∫ x,‖fderiv ℝ u x (oscillatorBasis k)‖^2)+
    a^2*(∑ k : ι,∫ x,‖x k • u x‖^2) at h
  rw [← integral_finsetSum _ (fun k _ => hD k),← integral_finsetSum _ (fun k _ => hW k)] at h
  simp_rw [euclidean_coordinate_smul_norm_sq_sum] at h
  simpa only [mul_assoc] using h

#print axioms euclidean_coordinate_smul_norm_sq_sum
#print axioms compact_euclidean_oscillator_form_bound
end TheoremT.Continuum
