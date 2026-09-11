import HalfLineCutoffBounds_v1
import HalfLineHydrogenNonzero_v1

noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace TheoremT.HalfLine

def groundTest (Z : ℝ) (n : ℕ) : Test :=
  ⟨fun r => interiorCutoff ((n:ℝ)+2) r • radialGround Z r,
   (interiorCutoff_contDiff _).smul (radialGround_contDiff Z),
   (interiorCutoff_compact (by positivity : 0 < (n:ℝ)+2)).smul_right,
   (tsupport_smul_subset_left _ _).trans (interiorCutoff_positive_support (by positivity))⟩

theorem groundTest_deriv (Z : ℝ) (n : ℕ) (r : ℝ) :
    deriv (groundTest Z n : ℝ → ℂ) r =
      interiorCutoff ((n:ℝ)+2) r • radialGroundPrime Z r +
        deriv (interiorCutoff ((n:ℝ)+2)) r • radialGround Z r := by
  have hη := ((interiorCutoff_contDiff ((n:ℝ)+2)).differentiable (by simp) r).hasDerivAt
  exact (hη.smul (radialGround_hasDerivAt Z r)).deriv

theorem groundTest_value_norm_le (Z : ℝ) (n : ℕ) (r : ℝ) :
    ‖groundTest Z n r‖ ≤ ‖radialGround Z r‖ := by
  change ‖interiorCutoff ((n:ℝ)+2) r • radialGround Z r‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (interiorCutoff_nonneg _ _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (interiorCutoff_le_one _ _)

def groundDerivativeMajorant (Z C r : ℝ) : ℝ :=
  ‖radialGroundPrime Z r‖ + C*(2*‖radialExp Z r‖+‖radialGround Z r‖)

theorem groundDerivativeMajorant_memLp {Z : ℝ} (hZ : 0 < Z) (C : ℝ) :
    MemLp (groundDerivativeMajorant Z C) 2 μ :=
  (radialGroundPrime_memLp hZ).norm.add
    ((((radialExp_memLp hZ).norm.const_smul (2:ℝ)).add (radialGround_memLp hZ).norm).const_smul C)

theorem groundDerivativeMajorant_nonneg (Z C r : ℝ) (hC : 0 ≤ C) :
    0 ≤ groundDerivativeMajorant Z C r := by unfold groundDerivativeMajorant; positivity

theorem groundPrime_norm_le_majorant (Z C r : ℝ) (hC : 0 ≤ C) :
    ‖radialGroundPrime Z r‖ ≤ groundDerivativeMajorant Z C r := by
  unfold groundDerivativeMajorant
  exact le_add_of_nonneg_right (by positivity)

theorem groundTest_deriv_norm_le (Z : ℝ) (n : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ r, |deriv transition r| ≤ C) {r : ℝ} (hr : 0 < r) :
    ‖deriv (groundTest Z n : ℝ → ℂ) r‖ ≤ groundDerivativeMajorant Z C r := by
  have hη : ‖interiorCutoff ((n:ℝ)+2) r • radialGroundPrime Z r‖ ≤ ‖radialGroundPrime Z r‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (interiorCutoff_nonneg _ _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (interiorCutoff_le_one _ _)
  have hg : ‖radialGround Z r‖ = r * ‖radialExp Z r‖ := by
    simp only [radialGround, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hd : ‖deriv (interiorCutoff ((n:ℝ)+2)) r • radialGround Z r‖ ≤
      C*(2*‖radialExp Z r‖+‖radialGround Z r‖) := by
    rw [norm_smul, Real.norm_eq_abs, hg]
    have hi := mul_le_mul_of_nonneg_right
      (cutoff_deriv_weighted_bound hC hb (by positivity : 0 < (n:ℝ)+2) hr)
      (norm_nonneg (radialExp Z r))
    nlinarith
  rw [groundTest_deriv]
  exact (norm_add_le _ _).trans (add_le_add hη hd)

theorem groundTest_eventually_profile {Z r : ℝ} (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop, groundTest Z n r = radialGround Z r ∧
      deriv (groundTest Z n : ℝ → ℂ) r = radialGroundPrime Z r := by
  filter_upwards [cutoff_eventually_one_deriv_zero hr] with n hn
  constructor
  · change interiorCutoff ((n:ℝ)+2) r • radialGround Z r = _
    rw [hn.1, one_smul]
  · rw [groundTest_deriv, hn.1, hn.2, one_smul, zero_smul, add_zero]

#print axioms groundTest
#print axioms groundDerivativeMajorant_memLp
#print axioms groundTest_deriv_norm_le
#print axioms groundTest_eventually_profile
end TheoremT.HalfLine
