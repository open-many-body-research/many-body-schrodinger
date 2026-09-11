import InteriorPoissonGradientGain_v1
import BoundedCoefficientEquationLp_v1
import NewtonBootstrapExponents_v1

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace TheoremT.Continuum

theorem bounded_coefficient_gradient_bootstrap {N : ℕ} (hN : 0 < N)
    {f : SpatialL2 N} {d : Coordinate N → SpatialL2 N}
    {e : Coordinate N → Coordinate N → SpatialL2 N}
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    {β : Coordinate N → Configuration N → ℝ} {c : Configuration N → ℝ}
    (hβ : ∀ k, MemLp (β k) ⊤ volume) (hc : MemLp c ⊤ volume) {R : ℝ}
    (hf : MemLp f ⊤ (volume.restrict (Metric.ball 0 R)))
    (hEq : ∀ᵐ x ∂volume.restrict (Metric.ball 0 R),
      (∑ k, e k k x) = -2*(∑ k, (β k x : ℂ)*d k x)-(c x : ℂ)*f x) :
    ∀ j : ℕ, j < 3*N → ∀ A : ℝ, 0 < A → (4:ℝ)^j*A < R →
      ∀ k, MemLp (d k) (ENNReal.ofReal (newtonBootstrapExponent (3*N:ℝ) j))
        (volume.restrict (Metric.ball 0 A)) := by
  have hD : 3 ≤ (3*N:ℝ) := by exact_mod_cast (show 3 ≤ 3*N by omega)
  intro j
  induction j with
  | zero =>
    intro hj A hA hAR k
    rw [Nat.cast_zero,newtonBootstrapExponent_zero (by linarith),ENNReal.ofReal_ofNat]
    exact (Lp.memLp (d k)).mono_measure Measure.restrict_le_self
  | succ j ih =>
    intro hj A hA hAR
    have hj0 : j < 3*N := by omega
    have hjR : (j:ℝ)+1 < (3*N:ℝ) := by exact_mod_cast hj
    have hs := newtonBootstrapExponent_young_step hD (Nat.cast_nonneg j) hjR
    have hDj : ∀ k, MemLp (d k) (ENNReal.ofReal (newtonBootstrapExponent (3*N:ℝ) j))
        (volume.restrict (Metric.ball 0 (4*A))) :=
      ih hj0 (4*A) (by positivity) (by simpa only [pow_succ,mul_assoc] using hAR)
    have hpow : (1:ℝ) ≤ 4^j := one_le_pow₀ (by norm_num)
    have h4A : 4*A < R := by
      have hb : 4*A ≤ (4:ℝ)^(j+1)*A := by
        rw [pow_succ]
        nlinarith
      exact hb.trans_lt hAR
    have hμ : volume.restrict (Metric.ball (0 : Configuration N) (4*A)) ≤ volume.restrict (Metric.ball 0 R) :=
      Measure.restrict_mono_set volume (Metric.ball_subset_ball h4A.le)
    letI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Configuration N) (4*A))) :=
      isFiniteMeasure_restrict.mpr measure_ball_ne_top
    have hfq : MemLp f (ENNReal.ofReal (newtonBootstrapExponent (3*N:ℝ) j))
        (volume.restrict (Metric.ball 0 (4*A))) := (hf.mono_measure hμ).mono_exponent le_top
    have hLq : MemLp (fun x => ∑ k, e k k x)
        (ENNReal.ofReal (newtonBootstrapExponent (3*N:ℝ) j)) (volume.restrict (Metric.ball 0 (4*A))) := by
      have hEq' : (fun x => ∑ k, e k k x) =ᵐ[volume.restrict (Metric.ball 0 (4*A))]
          (fun x => -2*(∑ k, (β k x : ℂ)*d k x)-(c x : ℂ)*f x) := hEq.filter_mono (ae_mono hμ)
      apply MemLp.ae_eq hEq'.symm
      exact bounded_coefficient_equation_rhs_memLp
        (fun k => (hβ k).mono_measure Measure.restrict_le_self)
        (hc.mono_measure Measure.restrict_le_self) hfq hDj
    have hgain := interior_weakH2_poisson_gradient_memLp hN hA hd he
      hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2
      (newtonBootstrapKernelExponent_bounds hD).2.2 hfq hDj hLq
    simpa only [Nat.cast_add,Nat.cast_one] using hgain

#print axioms bounded_coefficient_gradient_bootstrap
end TheoremT.Continuum
