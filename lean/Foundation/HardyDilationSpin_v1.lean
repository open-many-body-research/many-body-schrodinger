import HardyDilationCore_v1
import FermionicTrialL2_v2

/-! Compact dilations preserve the actual fermionic spin-space and have exact
L² and kinetic scaling. The spin factor is the same constant factor as in the
previously proved nonzero compact alternating trial. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace TheoremT.Continuum

def smoothCoreSpin {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) : SpinSpace N :=
  WithLp.toLp 2 (fun _ => smoothCoreL2 hu hc)

def smoothCoreSpinDerivative {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) (k : Coordinate N) : SpinSpace N :=
  smoothCoreSpin (smoothPartial_contDiff hu k) (smoothPartial_compact hc k)

theorem smoothCoreSpin_weakPartial {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) (σ : SpinConfiguration N)
    (k : Coordinate N) :
    WeakPartial (smoothCoreSpin hu hc σ) (smoothCoreSpinDerivative hu hc k σ) k :=
  smoothCoreL2_weakPartial hu hc k

theorem smoothCoreSpin_norm_sq {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    ‖smoothCoreSpin hu hc‖^2 =
      (Fintype.card (SpinConfiguration N) : ℝ) * ‖smoothCoreL2 hu hc‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [smoothCoreSpin]

theorem smoothCoreSpin_mem_target {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (halt : ∀ (π : Equiv.Perm (Fin N)) x,
      u (permuteSpace π x) = permutationSign π * u x) :
    smoothCoreSpin hu hc ∈ targetDomain N := by
  constructor
  · intro π σ
    change pullback π (smoothCoreL2 hu hc) = permutationSign π • smoothCoreL2 hu hc
    apply Lp.ext
    have ha := smoothCoreL2_ae hu hc
    have hap := (permuteSpace π).measurePreserving.quasiMeasurePreserving.ae ha
    filter_upwards [pullback_ae π (smoothCoreL2 hu hc),
      Lp.coeFn_smul (permutationSign π) (smoothCoreL2 hu hc), ha, hap]
      with x hpx hsx hax hapx
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at hpx hsx
    rw [hpx, hsx, hax, hapx]
    exact halt π x
  · intro σ
    exact smoothCoreL2_hasH2 hu hc

theorem spatialDilation_alternating {N : ℕ} {u : Configuration N → ℂ}
    (halt : ∀ (π : Equiv.Perm (Fin N)) x,
      u (permuteSpace π x) = permutationSign π * u x) (R : ℝ)
    (π : Equiv.Perm (Fin N)) (x : Configuration N) :
    spatialDilation R u (permuteSpace π x) = permutationSign π * spatialDilation R u x := by
  change u (R⁻¹ • permuteSpace π x) = permutationSign π * u (R⁻¹ • x)
  rw [← (permuteSpace π).map_smul]
  exact halt π _

theorem spatialDilation_spin_norm_sq {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) {R : ℝ} (hR : 0 < R) :
    ‖smoothCoreSpin (spatialDilation_contDiff hu R) (spatialDilation_compact hc hR)‖^2 =
      R ^ Module.finrank ℝ (Configuration N) * ‖smoothCoreSpin hu hc‖^2 := by
  rw [smoothCoreSpin_norm_sq, smoothCoreSpin_norm_sq, spatialDilation_norm_sq hu hc hR]
  ring

theorem spatialDilation_spin_gradient_sq {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) {R : ℝ} (hR : 0 < R) :
    (∑ k, ‖smoothCoreSpinDerivative (spatialDilation_contDiff hu R)
      (spatialDilation_compact hc hR) k‖^2) =
      (R⁻¹)^2 * R ^ Module.finrank ℝ (Configuration N) *
        (∑ k, ‖smoothCoreSpinDerivative hu hc k‖^2) := by
  simp only [smoothCoreSpinDerivative, smoothCoreSpin_norm_sq]
  simp_rw [spatialDilation_partial_norm_sq hu hc hR]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem fermionicTrialAmplitude_smooth (N : ℕ) :
    ContDiff ℝ ∞ (fermionicTrialAmplitude N) := compactAlternatingAmplitude_contDiff N _

theorem fermionicTrialAmplitude_compact (N : ℕ) :
    HasCompactSupport (fermionicTrialAmplitude N) :=
  compactAlternatingAmplitude_compact (by positivity)

theorem fermionicTrialAmplitude_alternating (N : ℕ) (π : Equiv.Perm (Fin N))
    (x : Configuration N) :
    fermionicTrialAmplitude N (permuteSpace π x) =
      permutationSign π * fermionicTrialAmplitude N x :=
  compactAlternatingAmplitude_permute _ π x

theorem smoothCoreSpin_trial_eq (N : ℕ) :
    smoothCoreSpin (fermionicTrialAmplitude_smooth N) (fermionicTrialAmplitude_compact N) =
      fermionicTrialSpin N := rfl

#print axioms spatialDilation_alternating
#print axioms smoothCoreSpin_mem_target
#print axioms spatialDilation_spin_norm_sq
#print axioms spatialDilation_spin_gradient_sq
end TheoremT.Continuum
