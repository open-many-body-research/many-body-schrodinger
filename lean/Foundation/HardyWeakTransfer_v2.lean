import HardyWeakTransfer_v1
import MollifierSequence_v2
import HardyCutoffBounds_v1

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ContDiff Topology RealInnerProductSpace
namespace TheoremT.Continuum

theorem spatialL2_norm_sq_eq_integral {N : ℕ} (f : SpatialL2 N) :
    ‖f‖^2 = (∫ x, ‖f x‖^2) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem spatialL2_family_integral_eq {N : ℕ} (d : Coordinate N → SpatialL2 N) :
    (∫ x, ∑ k : Coordinate N, ‖d k x‖^2) = ∑ k : Coordinate N, ‖d k‖^2 := by
  rw [integral_finset_sum Finset.univ
    (fun k _ => (Lp.memLp (d k)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))]
  simp_rw [← spatialL2_norm_sq_eq_integral]

def cutoffDerivative {N : ℕ} (χ : Configuration N → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N) (k : Coordinate N) : SpatialL2 N :=
  cutoffMul χ hχ.continuous hcχ (d k) +
    cutoffMul (fun x => fderiv ℝ χ x (coordinateVector k))
      ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hcχ.fderiv_apply ℝ (coordinateVector k)) f

/-- All mollifier-sequence, smoothness, compactness and a.e.-limit obligations are
discharged here. Only the weighted smooth-core estimate remains a premise. -/
theorem compact_core_bound_for_cutoff {N : ℕ} (W : Configuration N → ℝ)
    (hW : ∀ x, 0 ≤ W x) {K : ℝ} (hK : 0 ≤ K)
    (hcore : ∀ u : Configuration N → ℂ, ContDiff ℝ ∞ u → HasCompactSupport u →
      Integrable (fun x => W x * ‖u x‖^2) volume ∧
        (∫ x, W x * ‖u x‖^2) ≤ K *
          (∫ x, ∑ k : Coordinate N, ‖fderiv ℝ u x (coordinateVector k)‖^2))
    (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k)
    (χ : Configuration N → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) :
    Integrable (fun x => W x * ‖cutoffMul χ hχ.continuous hcχ f x‖^2) volume ∧
      (∫ x, W x * ‖cutoffMul χ hχ.continuous hcχ f x‖^2) ≤
        K * (∑ k : Coordinate N, ‖cutoffDerivative χ hχ hcχ f d k‖^2) := by
  have h := compact_core_bound_passes_to_weak_limit W hW hK hcore
    (cutoffMul χ hχ.continuous hcχ f) (cutoffDerivative χ hχ hcχ f d)
    (fun k => weakPartial_cutoff (hd k) χ hχ hcχ)
    (mollifierKernel N) (mollifierKernel_contDiff N)
    (mollifierKernel_hasCompactSupport N) (mollifierKernel_nonneg N)
    (mollifierKernel_integral N)
    (fun n => mollify_cutoff_compact (mollifierKernel N n) χ
      (mollifierKernel_hasCompactSupport N n) hχ.continuous hcχ f)
    (mollifyKernel_ae_tendsto _)
  rwa [spatialL2_family_integral_eq] at h

#print axioms spatialL2_norm_sq_eq_integral
#print axioms compact_core_bound_for_cutoff
end TheoremT.Continuum
