import LocalizedCuspDerivativeLimits_v1
import LocalizedCuspSecondBound_v1

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum

def regularizedLocalizedCusp (N : ℕ) (Z : ℝ) (χ : Configuration N → ℝ)
    (n : ℕ) (x : Configuration N) : ℝ :=
  χ x*Real.exp (-regularizedCoulombCusp N Z (radiusRegularization n) x)

theorem regularizedLocalizedCusp_contDiff (N : ℕ) (Z : ℝ)
    {χ : Configuration N → ℝ} (hχ : ContDiff ℝ ∞ χ) (n : ℕ) :
    ContDiff ℝ ∞ (regularizedLocalizedCusp N Z χ n) :=
  smooth_localized_exp_contDiff hχ (regularizedCoulombCusp_contDiff N Z (radiusRegularization_pos n))

theorem regularizedLocalizedCusp_compact (N : ℕ) (Z : ℝ)
    {χ : Configuration N → ℝ} (hc : HasCompactSupport χ) (n : ℕ) :
    HasCompactSupport (regularizedLocalizedCusp N Z χ n) := smooth_localized_exp_compact hc

theorem regularizedLocalizedCusp_memLp_top (N : ℕ) (Z : ℝ)
    {χ : Configuration N → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (n : ℕ) :
    MemLp (regularizedLocalizedCusp N Z χ n) (⊤ : ENNReal) volume :=
  (regularizedLocalizedCusp_contDiff N Z hχ n).continuous.memLp_top_of_hasCompactSupport
    (regularizedLocalizedCusp_compact N Z hc n) volume

theorem regularizedLocalizedCusp_partial_memLp_top (N : ℕ) (Z : ℝ)
    {χ : Configuration N → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (n : ℕ) (v : Configuration N) :
    MemLp (fun x => fderiv ℝ (regularizedLocalizedCusp N Z χ n) x v) (⊤ : ENNReal) volume :=
  (((regularizedLocalizedCusp_contDiff N Z hχ n).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport ((regularizedLocalizedCusp_compact N Z hc n).fderiv_apply ℝ v) volume

theorem regularizedLocalizedCusp_mixed_memLp_top (N : ℕ) (Z : ℝ)
    {χ : Configuration N → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (n : ℕ) (v w : Configuration N) :
    MemLp (fun x => fderiv ℝ (fun y => fderiv ℝ (regularizedLocalizedCusp N Z χ n) y v) x w)
      (⊤ : ENNReal) volume := by
  have hd : ContDiff ℝ ∞ (fun y => fderiv ℝ (regularizedLocalizedCusp N Z χ n) y v) :=
    ((regularizedLocalizedCusp_contDiff N Z hχ n).fderiv_right
      (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  exact ((hd.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
    (((regularizedLocalizedCusp_compact N Z hc n).fderiv_apply ℝ v).fderiv_apply ℝ w) volume

#print axioms regularizedLocalizedCusp_mixed_memLp_top
end TheoremT.Continuum
