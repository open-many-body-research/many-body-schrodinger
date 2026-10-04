import ManyBody.S8.Internal.DyadicDistanceRounding
import ManyBody.S8.Internal.RealTaylorDictionarySize
/-! Explicit dyadic rounding of the genuine canonical three-distance Taylor
polynomial. Its actual unshifted support and coefficients precede every bit
count; the true value/gradient/Hessian rounding errors have a literal finite
support/radius rate. On the radius-two box, p+4+7N denominator bits suffice
for error at most 2^(-p). Evaluating arbitrary original real coefficients or
choosing an analytic truncation order is not asserted computable here. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff BigOperators
namespace ManyBody.S8

def realTaylorDyadicDistancePolynomial (f : (Fin 3 → ℝ) → ℝ)
    (a : Fin 3 → ℝ) (N b : ℕ) : (Fin 3 → ℝ) → ℝ :=
  realDistancePolynomial (realTaylorDistanceDictionarySupport f a N)
    (fun α => (dyadicDistanceCoefficient b (realTaylorDistanceDictionaryCoefficient f a N α) : ℝ))

theorem realTaylorDistanceDictionary_rounding_budget_le
    (f : (Fin 3 → ℝ) → ℝ) (a : Fin 3 → ℝ) (N : ℕ) (R : ℝ) :
    distanceC2DyadicRoundingBudget (realTaylorDistanceDictionarySupport f a N) R ≤
      16*(N : ℝ)^3*(4*(1+max 0 R))^N := by
  classical
  let G : ℝ := 4*(1+max 0 R)
  have hG : 1 ≤ G := by dsimp [G]; linarith [le_max_left 0 R]
  have hterm (α : DistanceMultiIndex) (hα : α ∈ realTaylorDistanceDictionarySupport f a N) :
      16*G^(∑ j : Fin 3, α j) ≤ 16*G^N := by
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hα
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hG
      (realTaylorMvPolynomial_support_total_degree_lt f a N hd).le) (by norm_num)
  have hs := Finset.sum_le_sum hterm
  have hcard : ((realTaylorDistanceDictionarySupport f a N).card : ℝ) ≤ (N : ℝ)^3 := by
    exact_mod_cast realTaylorDistanceDictionarySupport_card_le f a N
  calc
    _ ≤ ∑ _α ∈ realTaylorDistanceDictionarySupport f a N, 16*G^N := hs
    _ = ((realTaylorDistanceDictionarySupport f a N).card : ℝ)*(16*G^N) := by simp
    _ ≤ (N : ℝ)^3*(16*G^N) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 16*(N : ℝ)^3*(4*(1+max 0 R))^N := by dsimp [G]; ring

theorem realTaylor_dyadic_rounding_uniform_C2
    (f : (Fin 3 → ℝ) → ℝ) (a : Fin 3 → ℝ) (N b : ℕ) (R : ℝ)
    {q : Fin 3 → ℝ} (hq : ‖q‖ ≤ R) (k : Fin 3) :
    ‖iteratedFDeriv ℝ (k : ℕ) (realTaylorPolynomial f a N) q-
      iteratedFDeriv ℝ (k : ℕ) (realTaylorDyadicDistancePolynomial f a N b) q‖ ≤
      16*(N : ℝ)^3*(4*(1+max 0 R))^N*(1/2 : ℝ)^b := by
  rw [realTaylorPolynomial_exact_distance_dictionary]
  exact (dyadic_realDistancePolynomial_uniform_C2 _ _ R b hq k).trans
    (mul_le_mul_of_nonneg_right (realTaylorDistanceDictionary_rounding_budget_le f a N R)
      (by positivity))

theorem realTaylor_dyadic_rounding_centered_C2
    (f : (Fin 3 → ℝ) → ℝ) (a : Fin 3 → ℝ) (N b : ℕ) (r : ℝ)
    {q : Fin 3 → ℝ} (hq : ‖q-a‖ ≤ r) (k : Fin 3) :
    ‖iteratedFDeriv ℝ (k : ℕ) (realTaylorPolynomial f a N) q-
      iteratedFDeriv ℝ (k : ℕ) (realTaylorDyadicDistancePolynomial f a N b) q‖ ≤
      16*(N : ℝ)^3*(4*(1+max 0 (‖a‖+r)))^N*(1/2 : ℝ)^b := by
  have hnorm : ‖q‖ ≤ ‖a‖+r := by
    have hh := norm_add_le (q-a) a
    rw [sub_add_cancel] at hh
    linarith
  exact realTaylor_dyadic_rounding_uniform_C2 f a N b (‖a‖+r) hnorm k

theorem realTaylorDistanceDictionary_radius_two_dyadic_budget_le
    (f : (Fin 3 → ℝ) → ℝ) (a : Fin 3 → ℝ) (N : ℕ) :
    distanceC2DyadicRoundingBudget (realTaylorDistanceDictionarySupport f a N) 2 ≤
      (2 : ℝ)^(4+7*N) := by
  have hN : (N : ℝ) ≤ (2 : ℝ)^N := by exact_mod_cast (show N < 2^N from Nat.lt_two_pow_self).le
  have hN3 := pow_le_pow_left₀ (Nat.cast_nonneg N) hN 3
  have hG : (4*(1+max 0 (2 : ℝ)))^N ≤ (16 : ℝ)^N :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) N
  have hprod := mul_le_mul hN3 hG (by positivity) (by positivity)
  calc
    _ ≤ 16*(N : ℝ)^3*(4*(1+max 0 (2 : ℝ)))^N :=
      realTaylorDistanceDictionary_rounding_budget_le f a N 2
    _ ≤ 16*((2 : ℝ)^N)^3*(16 : ℝ)^N :=
      by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 16)
    _ = (2 : ℝ)^4*(2 : ℝ)^(N*3)*(2 : ℝ)^(4*N) := by rw [pow_mul, pow_mul]; norm_num
    _ = (2 : ℝ)^(4+7*N) := by rw [←pow_add, ←pow_add]; congr 1; omega

theorem realTaylor_dyadic_rounding_explicit_bits_C2
    (f : (Fin 3 → ℝ) → ℝ) (a : Fin 3 → ℝ) (N p : ℕ)
    {q : Fin 3 → ℝ} (hq : ‖q‖ ≤ 2) (k : Fin 3) :
    ‖iteratedFDeriv ℝ (k : ℕ) (realTaylorPolynomial f a N) q-
      iteratedFDeriv ℝ (k : ℕ)
        (realTaylorDyadicDistancePolynomial f a N (p+4+7*N)) q‖ ≤ (1/2 : ℝ)^p := by
  rw [realTaylorPolynomial_exact_distance_dictionary]
  have h := dyadic_realDistancePolynomial_uniform_C2
    (realTaylorDistanceDictionarySupport f a N) (realTaylorDistanceDictionaryCoefficient f a N)
    2 (p+4+7*N) hq k
  apply h.trans
  calc
    _ ≤ (2 : ℝ)^(4+7*N)*(1/2 : ℝ)^(p+4+7*N) :=
      mul_le_mul_of_nonneg_right (realTaylorDistanceDictionary_radius_two_dyadic_budget_le f a N)
        (by positivity)
    _ = (1/2 : ℝ)^p := by
      rw [show p+4+7*N=p+(4+7*N) by omega, pow_add]
      calc
        _ = (1/2 : ℝ)^p*((2 : ℝ)^(4+7*N)*(1/2 : ℝ)^(4+7*N)) := by ring
        _ = (1/2 : ℝ)^p := by rw [←mul_pow]; norm_num

#print axioms realTaylorDistanceDictionary_rounding_budget_le
#print axioms realTaylor_dyadic_rounding_uniform_C2
#print axioms realTaylor_dyadic_rounding_centered_C2
#print axioms realTaylor_dyadic_rounding_explicit_bits_C2
end ManyBody.S8
