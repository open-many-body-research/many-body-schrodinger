import BoundedCoefficientGradientBootstrap_v1

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace TheoremT.Continuum

theorem bounded_coefficient_gradient_memLp_top {N : ℕ} (hN : 0 < N)
    {f : SpatialL2 N} {d : Coordinate N → SpatialL2 N}
    {e : Coordinate N → Coordinate N → SpatialL2 N}
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    {β : Coordinate N → Configuration N → ℝ} {c : Configuration N → ℝ}
    (hβ : ∀ k, MemLp (β k) ⊤ volume) (hc : MemLp c ⊤ volume) {R A : ℝ}
    (hf : MemLp f ⊤ (volume.restrict (Metric.ball 0 R)))
    (hEq : ∀ᵐ x ∂volume.restrict (Metric.ball 0 R),
      (∑ k, e k k x) = -2*(∑ k, (β k x : ℂ)*d k x)-(c x : ℂ)*f x)
    (hA : 0 < A) (hAR : (4:ℝ)^(3*N)*A < R) :
    ∀ k, MemLp (d k) ⊤ (volume.restrict (Metric.ball 0 A)) := by
  have hD : 3 ≤ (3*N:ℝ) := by exact_mod_cast (show 3 ≤ 3*N by omega)
  have hj : 3*N-1 < 3*N := by omega
  have hsum : (3*N-1)+1=3*N := by omega
  have hrad : (4:ℝ)^(3*N-1)*(4*A) < R := by
    simpa only [← mul_assoc,← pow_succ,hsum] using hAR
  have hDj := bounded_coefficient_gradient_bootstrap hN hd he hβ hc hf hEq
    (3*N-1) hj (4*A) (by positivity) hrad
  have hexp : newtonBootstrapExponent (3*N:ℝ) ((3*N-1:ℕ):ℝ)=2*(3*N:ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ 3*N),Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,
      newtonBootstrapExponent_last]
  rw [hexp] at hDj
  have hpow : (1:ℝ) ≤ 4^(3*N-1) := one_le_pow₀ (by norm_num)
  have h4A : 4*A < R := (show 4*A ≤ (4:ℝ)^(3*N-1)*(4*A) by nlinarith).trans_lt hrad
  have hμ : volume.restrict (Metric.ball (0 : Configuration N) (4*A)) ≤ volume.restrict (Metric.ball 0 R) :=
    Measure.restrict_mono_set volume (Metric.ball_subset_ball h4A.le)
  letI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Configuration N) (4*A))) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hfq : MemLp f (ENNReal.ofReal (2*(3*N:ℝ))) (volume.restrict (Metric.ball 0 (4*A))) :=
    (hf.mono_measure hμ).mono_exponent le_top
  have hLq : MemLp (fun x => ∑ k, e k k x) (ENNReal.ofReal (2*(3*N:ℝ)))
      (volume.restrict (Metric.ball 0 (4*A))) := by
    have hEq' : (fun x => ∑ k, e k k x) =ᵐ[volume.restrict (Metric.ball 0 (4*A))]
        (fun x => -2*(∑ k, (β k x : ℂ)*d k x)-(c x : ℂ)*f x) := hEq.filter_mono (ae_mono hμ)
    apply MemLp.ae_eq hEq'.symm
    exact bounded_coefficient_equation_rhs_memLp
      (fun k => (hβ k).mono_measure Measure.restrict_le_self)
      (hc.mono_measure Measure.restrict_le_self) hfq hDj
  exact interior_weakH2_poisson_gradient_memLp_top hN hA hd he
    (newtonBootstrapExponent_endpoint hD) (newtonBootstrapKernelExponent_bounds hD).2.2 hfq hDj hLq

#print axioms bounded_coefficient_gradient_memLp_top
end TheoremT.Continuum
