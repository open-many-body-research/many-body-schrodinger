import DistributionWeakPartial_v1
import WeakPartialComplexTests_v1
import CutoffH1Convergence_v2
import HardyWeakCore_v1

/-!
Extension of actual WeakPartial identities from compact tests to Schwartz tests
by convergent compact cutoffs in the first-derivative L2 graph topology.
No Sobolev core or noncompact weak-test identity is assumed.
-/

noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Filter LineDeriv
open scoped Topology ContDiff SchwartzMap

namespace TheoremT.Continuum

theorem WeakPartial.schwartz_test {N : ℕ} {f g : SpatialL2 N} {k : Coordinate N}
    (h : WeakPartial f g k) (φ : 𝓢(Configuration N, ℂ)) :
    (∫ x, φ x • g x) = -(∫ x, (∂_{coordinateVector k} φ) x • f x) := by
  let φL : SpatialL2 N := φ.toLp 2
  let dφL : SpatialL2 N := (∂_{coordinateVector k} φ).toLp 2
  let P : SpatialL2 N →L[ℂ] SpatialL2 N →L[ℂ] ℂ :=
    (ContinuousLinearMap.lsmul ℂ ℂ).lpPairing volume 2 2
  have hp (a b : SpatialL2 N) : P a b = ∫ x, a x • b x := by
    simpa [P] using (ContinuousLinearMap.lsmul ℂ ℂ).lpPairing_eq_integral a b
  have hpa {a : SpatialL2 N} {u : Configuration N → ℂ}
      (ha : a =ᵐ[volume] u) (b : SpatialL2 N) : P a b = ∫ x, u x • b x := by
    rw [hp]
    apply integral_congr_ae
    filter_upwards [ha] with x hx
    rw [hx]
  have hφw : WeakPartial φL dφL k := by
    apply weakPartial_of_temperedDistribution_derivative
    simp only [φL, dφL, Lp.toTemperedDistribution_toLp_eq]
    exact TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq φ (coordinateVector k)
  have hseq (n : ℕ) :
      P (cutoffAt n φL) g = -P (cutoffDerivativeAt n φL dφL k) f := by
    let χ := scaledCutoff N ((n : ℝ) + 1)
    let ψ : Configuration N → ℂ := fun x => χ x • φ x
    have hχ : ContDiff ℝ ∞ χ := scaledCutoff_contDiff N _
    have hcχ : HasCompactSupport χ := scaledCutoff_hasCompactSupport N (by positivity)
    have hψ : ContDiff ℝ ∞ ψ := hχ.smul φ.smooth'
    have hcψ : HasCompactSupport ψ := hcχ.smul_right
    have hmψ : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hcψ
    let ψL : SpatialL2 N := hmψ.toLp ψ
    let dψ : Configuration N → ℂ := fun x => fderiv ℝ ψ x (coordinateVector k)
    have hdψ : Continuous dψ :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hcdψ : HasCompactSupport dψ := hcψ.fderiv_apply ℝ (coordinateVector k)
    have hmdψ : MemLp dψ 2 volume := hdψ.memLp_of_hasCompactSupport hcdψ
    let dψL : SpatialL2 N := hmdψ.toLp dψ
    have hψeq : ψL = cutoffAt n φL := by
      apply Lp.ext
      filter_upwards [hmψ.coeFn_toLp, cutoffAt_ae n φL, φ.coeFn_toLp 2] with x hx hy hz
      change ψL x = cutoffAt n φL x
      rw [hx, hy, hz]
    have hψw : WeakPartial ψL dψL k :=
      classicalDerivative_to_WeakPartial (hψ.of_le (by norm_num)) k hmψ hmdψ
    have hdψeq : dψL = cutoffDerivativeAt n φL dφL k := by
      rw [hψeq] at hψw
      exact weakPartial_unique hψw (cutoffDerivativeAt_weakPartial hφw n)
    calc
      P (cutoffAt n φL) g = ∫ x, ψ x • g x := by
        rw [← hψeq]
        exact hpa hmψ.coeFn_toLp g
      _ = -(∫ x, dψ x • f x) := h.complex_test ψ hψ hcψ
      _ = -P (cutoffDerivativeAt n φL dφL k) f := by
        rw [← hdψeq, hpa hmdψ.coeFn_toLp f]
  have hl : Tendsto (fun n : ℕ => P (cutoffAt n φL) g) atTop (𝓝 (P φL g)) :=
    ((P.flip g).continuous.tendsto φL).comp (cutoffAt_tendsto φL)
  have hr : Tendsto (fun n : ℕ => -P (cutoffDerivativeAt n φL dφL k) f)
      atTop (𝓝 (-P dφL f)) :=
    (((P.flip f).continuous.tendsto dφL).comp (cutoffDerivativeAt_tendsto φL dφL k)).neg
  have hr' : Tendsto (fun n : ℕ => P (cutoffAt n φL) g) atTop (𝓝 (-P dφL f)) :=
    hr.congr' (Eventually.of_forall (fun n => (hseq n).symm))
  have hlim := tendsto_nhds_unique hl hr'
  rw [hpa (φ.coeFn_toLp 2) g, hpa ((∂_{coordinateVector k} φ).coeFn_toLp 2) f] at hlim
  exact hlim

/-- Actual real compact-test weak derivatives agree with distributional
derivatives on all Schwartz tests. The required extension is proved by cutoff. -/
theorem WeakPartial.temperedDistribution_derivative {N : ℕ}
    {f g : SpatialL2 N} {k : Coordinate N} (h : WeakPartial f g k) :
    ∂_{coordinateVector k} (f : 𝓢'(Configuration N, ℂ)) =
      (g : 𝓢'(Configuration N, ℂ)) := by
  ext φ
  simp only [TemperedDistribution.lineDerivOp_apply_apply, Lp.toTemperedDistribution_apply,
    neg_apply, neg_smul, integral_neg]
  exact (h.schwartz_test φ).symm

theorem weakPartial_iff_temperedDistribution_derivative {N : ℕ}
    {f g : SpatialL2 N} {k : Coordinate N} :
    WeakPartial f g k ↔
      ∂_{coordinateVector k} (f : 𝓢'(Configuration N, ℂ)) =
        (g : 𝓢'(Configuration N, ℂ)) :=
  ⟨WeakPartial.temperedDistribution_derivative, weakPartial_of_temperedDistribution_derivative⟩

#print axioms WeakPartial.schwartz_test
#print axioms WeakPartial.temperedDistribution_derivative
#print axioms weakPartial_iff_temperedDistribution_derivative

end TheoremT.Continuum
