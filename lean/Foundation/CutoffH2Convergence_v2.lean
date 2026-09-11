import CutoffH1Convergence_v2
import ScaledCutoffSecond_v2

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

def cutoffSecondErrorAt {N : ℕ} (n : ℕ) (f : SpatialL2 N) (k l : Coordinate N) : SpatialL2 N :=
  let χ := scaledCutoff N ((n:ℝ)+1)
  have hχ : ContDiff ℝ ∞ χ := scaledCutoff_contDiff N _
  have hcχ : HasCompactSupport χ := scaledCutoff_hasCompactSupport N (by positivity)
  have hdk : ContDiff ℝ ∞ (fun x => fderiv ℝ χ x (coordinateVector k)) :=
    (hχ.fderiv_right (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).clm_apply contDiff_const
  cutoffMul (fun x => fderiv ℝ (fun y => fderiv ℝ χ y (coordinateVector k)) x (coordinateVector l))
    ((hdk.continuous_fderiv (by simp)).clm_apply continuous_const)
    ((hcχ.fderiv_apply ℝ (coordinateVector k)).fderiv_apply ℝ (coordinateVector l)) f

def cutoffSecondDerivativeAt {N : ℕ} (n : ℕ) (f dk dl e : SpatialL2 N)
    (k l : Coordinate N) : SpatialL2 N :=
  (cutoffAt n e + cutoffErrorAt n dk l) +
    (cutoffErrorAt n dl k + cutoffSecondErrorAt n f k l)

theorem cutoffSecondDerivativeAt_weakPartial {N : ℕ} {f dk dl e : SpatialL2 N}
    {k l : Coordinate N} (hdl : WeakPartial f dl l) (he : WeakPartial dk e l) (n : ℕ) :
    WeakPartial (cutoffDerivativeAt n f dk k) (cutoffSecondDerivativeAt n f dk dl e k l) l := by
  let χ := scaledCutoff N ((n:ℝ)+1)
  have hχ : ContDiff ℝ ∞ χ := scaledCutoff_contDiff N _
  have hcχ : HasCompactSupport χ := scaledCutoff_hasCompactSupport N (by positivity)
  have hdk : ContDiff ℝ ∞ (fun x => fderiv ℝ χ x (coordinateVector k)) :=
    (hχ.fderiv_right (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).clm_apply contDiff_const
  exact weakPartial_add (weakPartial_cutoff he χ hχ hcχ)
    (weakPartial_cutoff hdl _ hdk (hcχ.fderiv_apply ℝ (coordinateVector k)))

theorem cutoffSecondErrorAt_tendsto_zero {N : ℕ} (f : SpatialL2 N) (k l : Coordinate N) :
    Tendsto (fun n : ℕ => cutoffSecondErrorAt n f k l) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := scaledCutoff_secondDerivative_bound N
  have hn (n : ℕ) : ‖cutoffSecondErrorAt n f k l‖ ≤ (C / ((n:ℝ)+1)^2) * ‖f‖ := by
    unfold cutoffSecondErrorAt
    exact norm_cutoffMul_le _ _ _ f (fun x => hbound _ (by positivity) x k l)
  have ht : Tendsto (fun n : ℕ => (C / ((n:ℝ)+1)^2) * ‖f‖) atTop (𝓝 0) := by
    have hh := (((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2).const_mul C).mul_const ‖f‖
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, one_div,
      div_eq_mul_inv, one_mul, inv_pow] using hh
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun _ => norm_nonneg _) hn ht)

theorem cutoffSecondDerivativeAt_tendsto {N : ℕ} (f dk dl e : SpatialL2 N) (k l : Coordinate N) :
    Tendsto (fun n : ℕ => cutoffSecondDerivativeAt n f dk dl e k l) atTop (𝓝 e) := by
  simpa only [cutoffSecondDerivativeAt, add_zero] using
    ((cutoffAt_tendsto e).add (cutoffErrorAt_tendsto_zero dk l)).add
      ((cutoffErrorAt_tendsto_zero dl k).add (cutoffSecondErrorAt_tendsto_zero f k l))

/-- The exact weak H2 derivative graph admits localization approximants
converging in every L2 component, including all ordered mixed derivatives. -/
theorem weakH2_cutoff_approximation {N : ℕ} {f : SpatialL2 N}
    (d : Coordinate N → SpatialL2 N) (e : Coordinate N → Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l) :
    (∀ n k, WeakPartial (cutoffAt n f) (cutoffDerivativeAt n f (d k) k) k) ∧
    (∀ n k l, WeakPartial (cutoffDerivativeAt n f (d k) k)
      (cutoffSecondDerivativeAt n f (d k) (d l) (e k l) k l) l) ∧
    Tendsto (fun n : ℕ => cutoffAt n f) atTop (𝓝 f) ∧
    (∀ k, Tendsto (fun n : ℕ => cutoffDerivativeAt n f (d k) k) atTop (𝓝 (d k))) ∧
    ∀ k l, Tendsto (fun n : ℕ => cutoffSecondDerivativeAt n f (d k) (d l) (e k l) k l)
      atTop (𝓝 (e k l)) :=
  ⟨fun n k => cutoffDerivativeAt_weakPartial (hd k) n,
    fun n k l => cutoffSecondDerivativeAt_weakPartial (hd l) (he k l) n,
    cutoffAt_tendsto f, fun k => cutoffDerivativeAt_tendsto f (d k) k,
    fun k l => cutoffSecondDerivativeAt_tendsto f (d k) (d l) (e k l) k l⟩

#print axioms cutoffSecondDerivativeAt_weakPartial
#print axioms cutoffSecondErrorAt_tendsto_zero
#print axioms cutoffSecondDerivativeAt_tendsto
#print axioms weakH2_cutoff_approximation
end TheoremT.Continuum
