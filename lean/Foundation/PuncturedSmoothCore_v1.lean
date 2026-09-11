import PuncturedCutoffConvergence_v1
import HardyH1ScalarDensity_v1

/-! Actual smooth compact punctured representatives and their weak derivative graphs.
The approximants vanish on an explicit ball around zero and therefore their closed
supports exclude zero. Membership in actual H² follows from their smooth compact
representatives, not from an assumed second derivative of the input. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

def puncturedAt {N : ℕ} (n : ℕ) (f : SpatialL2 N) : SpatialL2 N :=
  f - shrinkingCutoffAt n f

def puncturedDerivativeAt {N : ℕ} (n : ℕ) (f g : SpatialL2 N)
    (k : Coordinate N) : SpatialL2 N :=
  g - (shrinkingCutoffAt n g + shrinkingCutoffErrorAt n f k)

def puncturedSmooth {N : ℕ} (n : ℕ) (u : Configuration N → ℂ)
    (x : Configuration N) : ℂ :=
  u x - scaledCutoff N (punctureRadius n) x • u x

theorem puncturedAt_ae {N : ℕ} (n : ℕ) (f : SpatialL2 N)
    {u : Configuration N → ℂ} (hu : (f : Configuration N → ℂ) =ᵐ[volume] u) :
    (puncturedAt n f : Configuration N → ℂ) =ᵐ[volume] puncturedSmooth n u := by
  filter_upwards [Lp.coeFn_sub f (shrinkingCutoffAt n f), shrinkingCutoffAt_ae n f, hu]
    with x hx hc hf
  change (f - shrinkingCutoffAt n f) x = _
  simp only [hx, Pi.sub_apply, hc, hf, puncturedSmooth]

theorem puncturedAt_weakPartial {N : ℕ} {f g : SpatialL2 N} {k : Coordinate N}
    (h : WeakPartial f g k) (n : ℕ) :
    WeakPartial (puncturedAt n f) (puncturedDerivativeAt n f g k) k := by
  have hc := weakPartial_cutoff h (scaledCutoff N (punctureRadius n))
    (scaledCutoff_contDiff N _) (scaledCutoff_hasCompactSupport N (punctureRadius_pos n))
  simpa only [puncturedAt, puncturedDerivativeAt, shrinkingCutoffAt,
    shrinkingCutoffErrorAt, neg_one_smul, sub_eq_add_neg] using
    weakPartial_add h (weakPartial_smul (-1 : ℂ) hc)

theorem puncturedAt_tendsto (f : SpatialL2 1) :
    Tendsto (fun n => puncturedAt n f) atTop (𝓝 f) := by
  simpa only [puncturedAt, sub_zero] using tendsto_const_nhds.sub
    (shrinkingCutoffAt_tendsto_zero f)

theorem puncturedDerivativeAt_tendsto (f : SpatialL2 1)
    (d : Coordinate 1 → SpatialL2 1) (hd : ∀ k, WeakPartial f (d k) k)
    (k : Coordinate 1) :
    Tendsto (fun n => puncturedDerivativeAt n f (d k) k) atTop (𝓝 (d k)) := by
  simpa only [puncturedDerivativeAt, zero_add, sub_zero] using tendsto_const_nhds.sub
    ((shrinkingCutoffAt_tendsto_zero (d k)).add
      (shrinkingCutoffErrorAt_tendsto_zero f d hd k))

theorem puncturedSmooth_contDiff {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (n : ℕ) : ContDiff ℝ ∞ (puncturedSmooth n u) :=
  hu.sub ((scaledCutoff_contDiff N _).smul hu)

theorem puncturedSmooth_hasCompactSupport {N : ℕ} {u : Configuration N → ℂ}
    (hu : HasCompactSupport u) (n : ℕ) : HasCompactSupport (puncturedSmooth n u) := by
  have hm : HasCompactSupport (fun x => scaledCutoff N (punctureRadius n) x • u x) :=
    HasCompactSupport.smul_left (f := scaledCutoff N (punctureRadius n)) hu
  exact hu.sub hm

theorem puncturedSmooth_eq_zero_on_ball {N : ℕ} (n : ℕ) (u : Configuration N → ℂ)
    {x : Configuration N} (hx : ‖x‖ ≤ punctureRadius n) : puncturedSmooth n u x = 0 := by
  simp only [puncturedSmooth, scaledCutoff_eq_one (punctureRadius_pos n) hx,
    one_smul, sub_self]

theorem puncturedSmooth_zero_not_mem_tsupport {N : ℕ} (n : ℕ)
    (u : Configuration N → ℂ) : (0 : Configuration N) ∉ tsupport (puncturedSmooth n u) := by
  have hs : Function.support (puncturedSmooth n u) ⊆
      {x : Configuration N | punctureRadius n ≤ ‖x‖} := by
    intro x hx
    change punctureRadius n ≤ ‖x‖
    apply le_of_not_gt
    intro hh
    exact hx (puncturedSmooth_eq_zero_on_ball n u hh.le)
  have ht := closure_minimal hs (isClosed_le continuous_const continuous_norm)
  intro hzero
  have h := ht hzero
  change punctureRadius n ≤ ‖(0 : Configuration N)‖ at h
  rw [norm_zero] at h
  exact (not_le.mpr (punctureRadius_pos n)) h

theorem puncturedSmooth_actual_graph {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) (f : SpatialL2 N)
    (hf : (f : Configuration N → ℂ) =ᵐ[volume] u)
    (d : Coordinate N → SpatialL2 N) (hd : ∀ k, WeakPartial f (d k) k) (n : ℕ) :
    HasH2 (puncturedAt n f) ∧
      ∀ k, (puncturedDerivativeAt n f (d k) k : Configuration N → ℂ) =ᵐ[volume]
        smoothPartial (puncturedSmooth n u) k := by
  have hv := puncturedSmooth_contDiff hu n
  have hvc := puncturedSmooth_hasCompactSupport huc n
  have hvm : MemLp (puncturedSmooth n u) 2 volume :=
    hv.continuous.memLp_of_hasCompactSupport hvc
  have hve : hvm.toLp (puncturedSmooth n u) = puncturedAt n f :=
    Lp.ext (hvm.coeFn_toLp.trans (puncturedAt_ae n f hf).symm)
  constructor
  · rw [← hve]
    exact compact_c2_hasH2 (hv.of_le (by simp)) hvc hvm
  · intro k
    have hdm : MemLp (smoothPartial (puncturedSmooth n u) k) 2 volume :=
      ((hv.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
        (hvc.fderiv_apply ℝ (coordinateVector k))
    have hc := classicalDerivative_to_WeakPartial (hv.of_le (by simp)) k hvm hdm
    rw [hve] at hc
    have heq := weakPartial_unique (puncturedAt_weakPartial (hd k) n) hc
    rw [heq]
    exact hdm.coeFn_toLp

#print axioms puncturedAt_weakPartial
#print axioms puncturedAt_tendsto
#print axioms puncturedDerivativeAt_tendsto
#print axioms puncturedSmooth_zero_not_mem_tsupport
#print axioms puncturedSmooth_actual_graph
end TheoremT.Continuum
