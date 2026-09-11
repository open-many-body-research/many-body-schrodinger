import CutoffConvergence_v2
import Mathlib.Analysis.SpecificLimits.Basic

/-! Cutoff approximation of each actual weak derivative in L2. This establishes
the localization part of graph-norm density without assuming a Sobolev core. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

def cutoffErrorAt {N : ℕ} (n : ℕ) (f : SpatialL2 N) (k : Coordinate N) : SpatialL2 N :=
  cutoffMul (fun x => fderiv ℝ (scaledCutoff N ((n:ℝ)+1)) x (coordinateVector k))
    (((scaledCutoff_contDiff N _).continuous_fderiv (by simp)).clm_apply continuous_const)
    ((scaledCutoff_hasCompactSupport N (by positivity)).fderiv_apply ℝ (coordinateVector k)) f

def cutoffDerivativeAt {N : ℕ} (n : ℕ) (f g : SpatialL2 N) (k : Coordinate N) : SpatialL2 N :=
  cutoffAt n g + cutoffErrorAt n f k

theorem cutoffDerivativeAt_weakPartial {N : ℕ} {f g : SpatialL2 N} {k : Coordinate N}
    (h : WeakPartial f g k) (n : ℕ) :
    WeakPartial (cutoffAt n f) (cutoffDerivativeAt n f g k) k :=
  weakPartial_cutoff h _ (scaledCutoff_contDiff N _) (scaledCutoff_hasCompactSupport N (by positivity))

theorem cutoffErrorAt_tendsto_zero {N : ℕ} (f : SpatialL2 N) (k : Coordinate N) :
    Tendsto (fun n : ℕ => cutoffErrorAt n f k) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := scaledCutoff_derivative_bound N
  have hn (n : ℕ) : ‖cutoffErrorAt n f k‖ ≤ (C / ((n:ℝ)+1)) * ‖f‖ :=
    norm_cutoffMul_le _ _ _ f (fun x => hbound _ (by positivity) x k)
  have ht : Tendsto (fun n : ℕ => (C / ((n:ℝ)+1)) * ‖f‖) atTop (𝓝 0) := by
    have hh := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C).mul_const ‖f‖
    simpa only [mul_zero, zero_mul, mul_one_div] using hh
  have hnorm : Tendsto (fun n : ℕ => ‖cutoffErrorAt n f k‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) hn ht
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

theorem cutoffDerivativeAt_tendsto {N : ℕ} (f g : SpatialL2 N) (k : Coordinate N) :
    Tendsto (fun n : ℕ => cutoffDerivativeAt n f g k) atTop (𝓝 g) := by
  simpa only [cutoffDerivativeAt, add_zero] using (cutoffAt_tendsto g).add (cutoffErrorAt_tendsto_zero f k)

/-- Simultaneous approximation in the actual first-derivative graph topology.
The derivative data are required to be genuine weak derivatives of f. -/
theorem weakH1_cutoff_approximation {N : ℕ} {f : SpatialL2 N}
    (d : Coordinate N → SpatialL2 N) (hd : ∀ k, WeakPartial f (d k) k) :
    (∀ n k, WeakPartial (cutoffAt n f) (cutoffDerivativeAt n f (d k) k) k) ∧
    Tendsto (fun n : ℕ => cutoffAt n f) atTop (𝓝 f) ∧
    ∀ k, Tendsto (fun n : ℕ => cutoffDerivativeAt n f (d k) k) atTop (𝓝 (d k)) :=
  ⟨fun n k => cutoffDerivativeAt_weakPartial (hd k) n, cutoffAt_tendsto f,
    fun k => cutoffDerivativeAt_tendsto f (d k) k⟩

#print axioms cutoffDerivativeAt_weakPartial
#print axioms cutoffErrorAt_tendsto_zero
#print axioms cutoffDerivativeAt_tendsto
#print axioms weakH1_cutoff_approximation
end TheoremT.Continuum
