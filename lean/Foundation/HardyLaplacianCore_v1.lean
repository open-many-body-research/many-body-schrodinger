import HardyWeakTransfer_v2
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! The compact smooth Laplacian energy identity on actual configuration space. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff RealInnerProductSpace
namespace TheoremT.Continuum

def smoothPartial {N : ℕ} (u : Configuration N → ℂ) (k : Coordinate N)
    (x : Configuration N) : ℂ := fderiv ℝ u x (coordinateVector k)

def smoothLaplacian {N : ℕ} (u : Configuration N → ℂ) (x : Configuration N) : ℂ :=
  ∑ k : Coordinate N, smoothPartial (smoothPartial u k) k x

theorem smoothPartial_contDiff {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (k : Coordinate N) : ContDiff ℝ ∞ (smoothPartial u k) :=
  (hu.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const

theorem smoothPartial_compact {N : ℕ} {u : Configuration N → ℂ}
    (huc : HasCompactSupport u) (k : Coordinate N) : HasCompactSupport (smoothPartial u k) :=
  huc.fderiv_apply ℝ (coordinateVector k)

theorem compact_inner_integrable {N : ℕ} {u v : Configuration N → ℂ}
    (hu : Continuous u) (hv : Continuous v) (huc : HasCompactSupport u) :
    Integrable (fun x => inner ℝ (u x) (v x)) volume := by
  apply (hu.inner (𝕜 := ℝ) hv).integrable_of_hasCompactSupport
  apply huc.mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro hz
  apply hx
  rw [hz]
  simp

theorem compact_partial_energy_identity {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) (k : Coordinate N) :
    (∫ x, ‖smoothPartial u k x‖^2) =
      -(∫ x, inner ℝ (u x) (smoothPartial (smoothPartial u k) k x)) := by
  have hdu := smoothPartial_contDiff hu k
  have hddu := smoothPartial_contDiff hdu k
  have hduc := smoothPartial_compact huc k
  have hh := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (B := innerSL ℝ) (v := coordinateVector k)
    (compact_inner_integrable hdu.continuous hdu.continuous hduc)
    (compact_inner_integrable hu.continuous hddu.continuous huc)
    (compact_inner_integrable hu.continuous hdu.continuous huc)
    (fun x _ => hu.differentiable (by simp) x)
    (fun x _ => hdu.differentiable (by simp) x)
  change (∫ x, inner ℝ (u x) (smoothPartial (smoothPartial u k) k x)) =
    -(∫ x, inner ℝ (smoothPartial u k x) (smoothPartial u k x)) at hh
  simp only [real_inner_self_eq_norm_sq] at hh
  linarith

theorem smooth_partial_sq_integrable {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) (k : Coordinate N) :
    Integrable (fun x => ‖smoothPartial u k x‖^2) volume := by
  simpa only [real_inner_self_eq_norm_sq] using compact_inner_integrable
    (smoothPartial_contDiff hu k).continuous (smoothPartial_contDiff hu k).continuous
    (smoothPartial_compact huc k)

theorem compact_laplacian_energy_identity {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) :
    (∫ x, ∑ k : Coordinate N, ‖smoothPartial u k x‖^2) =
      -(∫ x, inner ℝ (u x) (smoothLaplacian u x)) := by
  have hinner := fun k => compact_inner_integrable hu.continuous
    (smoothPartial_contDiff (smoothPartial_contDiff hu k) k).continuous huc
  simp only [smoothLaplacian, inner_sum]
  rw [integral_finset_sum Finset.univ (fun k _ => smooth_partial_sq_integrable hu huc k),
    integral_finset_sum Finset.univ (fun k _ => hinner k)]
  simp_rw [compact_partial_energy_identity hu huc]
  simp only [Finset.sum_neg_distrib]

#print axioms compact_partial_energy_identity
#print axioms compact_laplacian_energy_identity
end TheoremT.Continuum
