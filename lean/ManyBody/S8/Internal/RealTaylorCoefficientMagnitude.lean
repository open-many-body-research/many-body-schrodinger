import ManyBody.S8.Internal.RealTaylorDictionarySize
import Mathlib.Tactic
/-! Magnitudes of literal canonical Taylor dictionary coefficients.

The true two-term coefficient recurrence controls each translated coordinate
product, including repeated-variable binomial multiplicities. Actual basis
word contractions, factorial cancellation and the genuine 3^n word count
then control every unshifted coefficient from a true center jet bound. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace ManyBody.S8

theorem translated_coordinate_product_coeff_bound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w : ι → Fin 3) (a : Fin 3 → ℝ) (d : Fin 3 →₀ ℕ) :
    |(∏ k∈s, (MvPolynomial.X (w k)-MvPolynomial.C (a (w k)))).coeff d| ≤
      (1+‖a‖)^s.card := by
  classical
  induction s using Finset.induction_on generalizing d with
  | empty =>
      simp only [Finset.prod_empty, Finset.card_empty, pow_zero, MvPolynomial.coeff_one]
      split_ifs <;> norm_num
  | @insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.card_insert_of_notMem hk, pow_succ]
      let P : MvPolynomial (Fin 3) ℝ :=
        ∏ l∈s, (MvPolynomial.X (w l)-MvPolynomial.C (a (w l)))
      have heq : (MvPolynomial.X (w k)-MvPolynomial.C (a (w k)))*P =
          P*MvPolynomial.X (w k)-MvPolynomial.C (a (w k))*P := by ring
      change |((MvPolynomial.X (w k)-MvPolynomial.C (a (w k)))*P).coeff d| ≤ _
      rw [heq, MvPolynomial.coeff_sub, MvPolynomial.coeff_C_mul]
      have hX : |(P*MvPolynomial.X (w k)).coeff d| ≤ (1+‖a‖)^s.card := by
        rw [MvPolynomial.coeff_mul_X']
        split_ifs
        · exact ih _
        · simpa using (by positivity : (0:ℝ) ≤ (1+‖a‖)^s.card)
      calc
        _ ≤ |(P*MvPolynomial.X (w k)).coeff d|+|a (w k)*P.coeff d| := abs_sub _ _
        _ ≤ (1+‖a‖)^s.card+‖a‖*(1+‖a‖)^s.card := by
          rw [abs_mul]
          exact add_le_add hX (mul_le_mul
            (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm a (w k))
            (ih d) (abs_nonneg _) (norm_nonneg _))
        _ = (1+‖a‖)^s.card*(1+‖a‖) := by ring

theorem realTaylor_basis_word_factor_bound
    (f : (Fin 3 → ℝ) → ℝ) (a : Fin 3 → ℝ) {M L : ℝ}
    (hjet : ∀ n, ‖iteratedFDeriv ℝ n f a‖ ≤ M*L^n*(n.factorial:ℝ))
    (n : ℕ) (w : Fin n → Fin 3) :
    |(n.factorial:ℝ)⁻¹ * iteratedFDeriv ℝ n f a (fun k => Pi.single (w k) 1)| ≤
      M*L^n := by
  have hfac : (0:ℝ)<(n.factorial:ℝ) := by positivity
  have hv : ‖iteratedFDeriv ℝ n f a (fun k => Pi.single (w k) 1)‖ ≤
      ‖iteratedFDeriv ℝ n f a‖ := by
    have h := (iteratedFDeriv ℝ n f a).le_opNorm (fun k => Pi.single (w k) 1)
    simpa only [Pi.norm_single, norm_one, Finset.prod_const_one, mul_one] using h
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hfac.le)]
  have hb : |iteratedFDeriv ℝ n f a (fun k => Pi.single (w k) 1)| ≤
      M*L^n*(n.factorial:ℝ) := by
    simpa only [Real.norm_eq_abs] using hv.trans (hjet n)
  calc
    _ ≤ (n.factorial:ℝ)⁻¹*(M*L^n*(n.factorial:ℝ)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = M*L^n := by field_simp


def realTaylorCoefficientGrowthBase (L : ℝ) (a : Fin 3 → ℝ) : ℝ :=
  3*max 1 L*(1+‖a‖)

theorem realTaylorCoefficientGrowthBase_one_le (L : ℝ) (a : Fin 3 → ℝ) :
    1 ≤ realTaylorCoefficientGrowthBase L a := by
  unfold realTaylorCoefficientGrowthBase
  have h := le_max_left (1:ℝ) L
  nlinarith [norm_nonneg a, mul_nonneg (by linarith : 0 ≤ max 1 L) (norm_nonneg a)]

theorem realTaylorMvPolynomial_coefficient_bound
    (f : (Fin 3 → ℝ) → ℝ) (a : Fin 3 → ℝ) {M L : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hjet : ∀ n, ‖iteratedFDeriv ℝ n f a‖ ≤ M*L^n*(n.factorial:ℝ))
    (N : ℕ) (d : Fin 3 →₀ ℕ) :
    |(realTaylorMvPolynomial f a N).coeff d| ≤
      M*N*(realTaylorCoefficientGrowthBase L a)^N := by
  classical
  have hdegree (n : ℕ) :
      |(∑ w : Fin n → Fin 3,
        MvPolynomial.C ((n.factorial:ℝ)⁻¹*
          iteratedFDeriv ℝ n f a (fun k => Pi.single (w k) 1))*
        ∏ k, (MvPolynomial.X (w k)-MvPolynomial.C (a (w k)))).coeff d| ≤
        M*(realTaylorCoefficientGrowthBase L a)^n := by
    rw [MvPolynomial.coeff_sum]
    calc
      _ ≤ ∑ w : Fin n → Fin 3,
          |(MvPolynomial.C ((n.factorial:ℝ)⁻¹*
            iteratedFDeriv ℝ n f a (fun k => Pi.single (w k) 1))*
            ∏ k, (MvPolynomial.X (w k)-MvPolynomial.C (a (w k)))).coeff d| := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _w : Fin n → Fin 3, M*(max 1 L)^n*(1+‖a‖)^n := by
        apply Finset.sum_le_sum
        intro w hw
        rw [MvPolynomial.coeff_C_mul,abs_mul]
        have hb := realTaylor_basis_word_factor_bound f a hjet n w
        have hp := translated_coordinate_product_coeff_bound Finset.univ w a d
        have hp' : |(∏ k, (MvPolynomial.X (w k)-MvPolynomial.C (a (w k)))).coeff d| ≤
            (1+‖a‖)^n := by simpa using hp
        have hb' : |(n.factorial:ℝ)⁻¹*
            iteratedFDeriv ℝ n f a (fun k => Pi.single (w k) 1)| ≤ M*(max 1 L)^n :=
          hb.trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hL
              (le_max_right 1 L) n) hM)
        exact mul_le_mul hb' hp' (abs_nonneg _) (by positivity)
      _ = M*(realTaylorCoefficientGrowthBase L a)^n := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,
          nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat,realTaylorCoefficientGrowthBase,
          mul_pow]
        ring
  unfold realTaylorMvPolynomial
  rw [MvPolynomial.coeff_sum]
  calc
    _ ≤ ∑ n∈Finset.range N, |(∑ w : Fin n → Fin 3,
        MvPolynomial.C ((n.factorial:ℝ)⁻¹*
          iteratedFDeriv ℝ n f a (fun k => Pi.single (w k) 1))*
        ∏ k, (MvPolynomial.X (w k)-MvPolynomial.C (a (w k)))).coeff d| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n∈Finset.range N, M*(realTaylorCoefficientGrowthBase L a)^N := by
      apply Finset.sum_le_sum
      intro n hn
      exact (hdegree n).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (realTaylorCoefficientGrowthBase_one_le L a)
          (Finset.mem_range.mp hn).le) hM)
    _ = M*N*(realTaylorCoefficientGrowthBase L a)^N := by simp; ring

theorem realTaylorDistanceDictionaryCoefficient_bound
    (f : (Fin 3 → ℝ) → ℝ) (a : Fin 3 → ℝ) {M L : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hjet : ∀ n, ‖iteratedFDeriv ℝ n f a‖ ≤ M*L^n*(n.factorial:ℝ))
    (N : ℕ) (α : DistanceMultiIndex) :
    |realTaylorDistanceDictionaryCoefficient f a N α| ≤
      M*N*(realTaylorCoefficientGrowthBase L a)^N :=
  realTaylorMvPolynomial_coefficient_bound f a hM hL hjet N _

#print axioms realTaylorDistanceDictionaryCoefficient_bound
#print axioms translated_coordinate_product_coeff_bound
#print axioms realTaylor_basis_word_factor_bound
end ManyBody.S8
