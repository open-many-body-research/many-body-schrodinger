import ProductWeakEllipticGain_v1
import FstDirectionalJet_v1
import SecondDirectionalProduct_v1

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum
variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

theorem weakProduct_second_same_test
    {f d e : Lp ℂ 2 (volume : Measure (Y × T))} {v : Y × T}
    (hd : WeakProductL2Directional f d v) (he : WeakProductL2Directional d e v)
    {φ : Y × T → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ p, φ p • e p) = ∫ p, fderiv ℝ (fun q => fderiv ℝ φ q v) p v • f p := by
  have hφD : ContDiff ℝ ∞ (fun p => fderiv ℝ φ p v) :=
    (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have h1 := hd (fun p => fderiv ℝ φ p v) hφD (hc.fderiv_apply ℝ v)
  have h2 := he φ hφ hc
  rw [h1,neg_neg] at h2
  exact h2

theorem spectator_invariant_weight_second_test
    {f d e : Lp ℂ 2 (volume : Measure (Y × T))} {v : T}
    (hd : WeakProductL2Directional f d (0,v)) (he : WeakProductL2Directional d e (0,v))
    {a : Y → ℝ} (ha : ContDiff ℝ ∞ a)
    {φ : Y × T → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ p, (a p.1 * φ p) • e p) =
      ∫ p, (a p.1 * fderiv ℝ (fun q => fderiv ℝ φ q (0,v)) p (0,v)) • f p := by
  have hA : ContDiff ℝ ∞ (fun p : Y × T => a p.1) := ha.comp contDiff_fst
  have htest := weakProduct_second_same_test hd he (hA.mul hφ) hc.mul_left
  have hfirst (p : Y × T) : fderiv ℝ (fun q : Y × T => a q.1) p (0,v) = 0 := by
    rw [first_directional_fst (ha.differentiable (by simp))]
    simp
  have hsecond (p : Y × T) : fderiv ℝ
      (fun q => fderiv ℝ (fun z : Y × T => a z.1) q (0,v)) p (0,v) = 0 := by
    rw [second_directional_fst ha]
    simp
  simp only [second_directional_product hA hφ] at htest
  simp only [hsecond] at htest
  simp only [hfirst,zero_mul,zero_add,add_zero] at htest
  exact htest

#print axioms weakProduct_second_same_test
#print axioms spectator_invariant_weight_second_test
end TheoremT.Continuum
