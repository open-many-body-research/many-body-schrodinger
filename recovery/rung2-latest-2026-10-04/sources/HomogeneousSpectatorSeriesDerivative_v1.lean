import HomogeneousSpectatorSumAnalytic_v1
import HomogeneousPolynomialSeriesDerivative_v1
import Mathlib.Data.Nat.Choose.Bounds

/-! Explicit, deliberately coarse derivative bounds for the actual joint
polynomial/spectator sum. The binomial block count is bounded by 2^(n+d)
only for this quantitative bound. The previously proved full analytic
radius is retained separately. This theorem does not assert the original
mixed multiindex Cauchy constant. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Topology
namespace TheoremT.Continuum
variable {d : ℕ}

theorem polynomialCoeffL1_groupedHomogeneousSpectatorPolynomial_coarse
    (A : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 3) ℂ) {M T : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hL : ∀ m γ, polynomialCoeffL1 (A m γ) ≤ M*T^(m+∑ i : Fin d, γ i))
    (n : ℕ) :
    polynomialCoeffL1 (groupedHomogeneousSpectatorPolynomial A n) ≤
      (M*2^d)*(2*T)^n := by
  have hc : ((n+d).choose d : ℝ) ≤ (2:ℝ)^(n+d) := by
    exact_mod_cast Nat.choose_le_two_pow (n+d) d
  calc
    _ ≤ M*((n+d).choose d : ℝ)*T^n := polynomialCoeffL1_groupedHomogeneousSpectatorPolynomial A hL n
    _ ≤ M*2^(n+d)*T^n := by gcongr
    _ = _ := by rw [pow_add,mul_pow]; ring

theorem homogeneousSpectatorSum_eventuallyEq_grouped
    (A : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 3) ℂ)
    (hA : ∀ m γ, (A m γ).IsHomogeneous m) {M T : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hL : ∀ m γ, polynomialCoeffL1 (A m γ) ≤ M*T^(m+∑ i : Fin d, γ i))
    (z : Fin 3 ⊕ Fin d → ℂ) (hz : T*‖z‖ < 1) :
    homogeneousSpectatorSum A =ᶠ[𝓝 z]
      (fun v => ∑' n, MvPolynomial.eval v (groupedHomogeneousSpectatorPolynomial A n)) := by
  have hopen : IsOpen {v : Fin 3 ⊕ Fin d → ℂ | T*‖v‖ < 1} :=
    isOpen_lt (continuous_const.mul continuous_norm) continuous_const
  filter_upwards [hopen.mem_nhds hz] with v hv
  have hL' (m : ℕ) (γ : Fin d → ℕ) :
      polynomialCoeffL1 (A m γ) ≤ M*T^m*T^(∑ i : Fin d, γ i) := by
    simpa only [pow_add,mul_assoc] using hL m γ
  have hs := ((homogeneous_spectator_series_closed_polydiscs A hA hM hT (norm_nonneg v)
    hT (norm_nonneg v) hv hv hL').1
    ((fun i => v (.inl i)),(fun i => v (.inr i)))
    ⟨fun i => norm_le_pi_norm v (.inl i),fun i => norm_le_pi_norm v (.inr i)⟩).2.1
  have heq := groupedHomogeneousSpectatorPolynomial_tsum_eq A
    (fun i => v (.inl i)) (fun i => v (.inr i)) hs
  have hveta : Sum.elim (fun i => v (.inl i)) (fun i => v (.inr i)) = v := by
    funext i
    cases i <;> rfl
  simpa only [hveta,homogeneousSpectatorSum,homogeneousSpectatorTerm] using heq.symm

theorem homogeneous_spectator_series_quarter_domain_factorial_bound
    (A : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 3) ℂ)
    (hA : ∀ m γ, (A m γ).IsHomogeneous m) {M T : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hL : ∀ m γ, polynomialCoeffL1 (A m γ) ≤ M*T^(m+∑ i : Fin d, γ i))
    (z : Fin 3 ⊕ Fin d → ℂ) (hz : T*‖z‖ ≤ 1/4) (k : ℕ) :
    ‖iteratedFDeriv ℂ k (homogeneousSpectatorSum A) z‖ ≤
      (2*(M*2^d))*(4*T)^k*(k.factorial : ℝ) := by
  have hEq := homogeneousSpectatorSum_eventuallyEq_grouped A hA hM hT hL z (by linarith)
  rw [(hEq.iteratedFDeriv ℂ k).eq_of_nhds]
  have hh := homogeneous_polynomial_series_half_domain_factorial_bound
    (groupedHomogeneousSpectatorPolynomial A) (groupedHomogeneousSpectatorPolynomial_isHomogeneous A hA)
    (mul_nonneg hM (by positivity)) (mul_nonneg (by norm_num) hT)
    (polynomialCoeffL1_groupedHomogeneousSpectatorPolynomial_coarse A hM hT hL)
    z (show (2*T)*‖z‖ ≤ 1/2 by nlinarith) k
  convert hh using 1 <;> congr 2 <;> ring

end TheoremT.Continuum
