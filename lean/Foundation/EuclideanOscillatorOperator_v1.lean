import EuclideanOscillatorForm_v1
import ActualL2IntegralCauchy_v1

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff RealInnerProductSpace
namespace TheoremT.Continuum
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def oscillatorPartial (u : EuclideanSpace ℝ ι → ℂ) (k : ι) (x : EuclideanSpace ℝ ι) : ℂ :=
  fderiv ℝ u x (oscillatorBasis k)

def euclideanOscillator (a : ℝ) (u : EuclideanSpace ℝ ι → ℂ) (x : EuclideanSpace ℝ ι) : ℂ :=
  -(∑ k : ι, oscillatorPartial (oscillatorPartial u k) k x)+(a^2*‖x‖^2) • u x

theorem oscillatorPartial_contDiff {u : EuclideanSpace ℝ ι → ℂ} (hu : ContDiff ℝ ∞ u) (k : ι) :
    ContDiff ℝ ∞ (oscillatorPartial u k) :=
  (hu.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const

theorem oscillatorPartial_compact {u : EuclideanSpace ℝ ι → ℂ} (hc : HasCompactSupport u) (k : ι) :
    HasCompactSupport (oscillatorPartial u k) := hc.fderiv_apply ℝ (oscillatorBasis k)

theorem euclideanOscillator_contDiff (a : ℝ) {u : EuclideanSpace ℝ ι → ℂ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (euclideanOscillator a u) :=
  (ContDiff.sum (fun k _ => oscillatorPartial_contDiff (oscillatorPartial_contDiff hu k) k)).neg.add
    ((contDiff_const.mul (contDiff_norm_sq ℝ)).smul hu)

theorem euclideanOscillator_compact (a : ℝ) {u : EuclideanSpace ℝ ι → ℂ} (hc : HasCompactSupport u) :
    HasCompactSupport (euclideanOscillator a u) := by
  have hsum : HasCompactSupport (fun x => ∑ k : ι, oscillatorPartial (oscillatorPartial u k) k x) := by
    have he : (fun x => ∑ k : ι, oscillatorPartial (oscillatorPartial u k) k x)=
        ∑ k : ι, oscillatorPartial (oscillatorPartial u k) k := by funext x;simp
    rw [he]
    exact HasCompactSupport.finset_sum (fun k _ => oscillatorPartial_compact (oscillatorPartial_compact hc k) k)
  have hweight : HasCompactSupport (fun x => (a^2*‖x‖^2) • u x) := by
    apply hc.mono
    intro x hx
    change u x ≠ 0
    intro hz
    exact hx (by simp [hz])
  exact hsum.neg.add hweight

theorem compact_euclidean_oscillator_energy (a : ℝ) {u : EuclideanSpace ℝ ι → ℂ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    (∫ x, inner ℝ (u x) (euclideanOscillator a u x))=
      (∫ x, ∑ k : ι, ‖oscillatorPartial u k x‖^2)+a^2*(∫ x, ‖x‖^2*‖u x‖^2) := by
  have hi (k : ι) := compact_real_inner_integrable_general (μ := volume) hu.continuous
    (oscillatorPartial_contDiff (oscillatorPartial_contDiff hu k) k).continuous hc
  have hd (k : ι) : Integrable (fun x => ‖oscillatorPartial u k x‖^2) volume := by
    simpa only [real_inner_self_eq_norm_sq] using compact_real_inner_integrable_general
      (μ := volume) (oscillatorPartial_contDiff hu k).continuous
      (oscillatorPartial_contDiff hu k).continuous (oscillatorPartial_compact hc k)
  have hW : Integrable (fun x => ‖x‖^2*‖u x‖^2) volume := by
    apply ((continuous_norm.pow 2).mul (hu.continuous.norm.pow 2)).integrable_of_hasCompactSupport
    apply hc.mono
    intro x hx
    change u x ≠ 0
    intro hz
    exact hx (by simp [hz])
  have hsum : Integrable (fun x => ∑ k : ι, inner ℝ (u x) (oscillatorPartial (oscillatorPartial u k) k x)) volume :=
    integrable_finsetSum _ (fun k _ => hi k)
  have hn : Integrable (fun x => -(∑ k : ι, inner ℝ (u x) (oscillatorPartial (oscillatorPartial u k) k x))) volume := hsum.neg
  have hw : Integrable (fun x => a^2*(‖x‖^2*‖u x‖^2)) volume := hW.const_mul _
  simp only [euclideanOscillator,inner_add_right,inner_neg_right,inner_sum,real_inner_smul_right,
    real_inner_self_eq_norm_sq,mul_assoc]
  rw [integral_add hn hw,integral_neg,integral_const_mul,
    integral_finsetSum _ (fun k _ => hi k),integral_finsetSum _ (fun k _ => hd k)]
  have hg (k : ι) : (∫ x,‖oscillatorPartial u k x‖^2)=
      -(∫ x,inner ℝ (u x) (oscillatorPartial (oscillatorPartial u k) k x)) :=
    compact_directional_green hu hc (oscillatorBasis k)
  simp_rw [hg,Finset.sum_neg_distrib]

#print axioms euclideanOscillator_contDiff
#print axioms euclideanOscillator_compact
#print axioms compact_euclidean_oscillator_energy
end TheoremT.Continuum
