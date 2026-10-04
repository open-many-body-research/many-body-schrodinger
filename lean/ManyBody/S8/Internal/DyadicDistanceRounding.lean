import ManyBody.S8.Internal.CoordinateProductDerivativeBounds
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic
/-! Literal dyadic floor rounding and explicit true C2 finite dictionary bounds.

Every real coefficient is rounded by its actual integer floor at denominator
2^b. Genuine monomial product derivatives give an explicit support/radius
budget for the same rounded polynomial in value, first and second operator
norm. This proves no algorithm for evaluating arbitrary original real inputs. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff BigOperators
namespace ManyBody.S8

def dyadicDistanceCoefficient (b : ℕ) (c : ℝ) : ℚ :=
  (⌊(2 : ℝ)^b*c⌋ : ℚ)/(2 : ℚ)^b

theorem dyadicDistanceCoefficient_error (b : ℕ) (c : ℝ) :
    0 ≤ c-(dyadicDistanceCoefficient b c : ℝ) ∧
      c-(dyadicDistanceCoefficient b c : ℝ) < (1/2 : ℝ)^b := by
  have hpow : 0 < (2 : ℝ)^b := by positivity
  have hcast : (dyadicDistanceCoefficient b c : ℝ) =
      (⌊(2 : ℝ)^b*c⌋ : ℝ)/(2 : ℝ)^b := by simp [dyadicDistanceCoefficient]
  rw [hcast]
  have hlo := Int.floor_le ((2 : ℝ)^b*c)
  have hhi := Int.lt_floor_add_one ((2 : ℝ)^b*c)
  have h0 : 0 ≤ c-(⌊(2 : ℝ)^b*c⌋ : ℝ)/(2 : ℝ)^b := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hpow).mpr
    simpa only [mul_comm] using hlo
  refine ⟨h0, ?_⟩
  have he : c-(⌊(2 : ℝ)^b*c⌋ : ℝ)/(2 : ℝ)^b < 1/(2 : ℝ)^b := by
    apply (mul_lt_mul_iff_of_pos_right hpow).mp
    rw [sub_mul, div_mul_cancel₀ _ hpow.ne', div_mul_cancel₀ _ hpow.ne']
    nlinarith
  have heq : 1/(2 : ℝ)^b=(1/2 : ℝ)^b := by rw [one_div, ←inv_pow]; norm_num
  exact he.trans_eq heq

theorem dyadicDistanceCoefficient_abs_error (b : ℕ) (c : ℝ) :
    |c-(dyadicDistanceCoefficient b c : ℝ)| ≤ (1/2 : ℝ)^b := by
  rw [abs_of_nonneg (dyadicDistanceCoefficient_error b c).1]
  exact (dyadicDistanceCoefficient_error b c).2.le

@[simp] theorem dyadicDistanceCoefficient_zero (b : ℕ) :
    dyadicDistanceCoefficient b 0 = 0 := by simp [dyadicDistanceCoefficient]

theorem real_C2_product_uniform_bound {f g : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (p : Fin 3 → ℝ)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hfb : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i f p‖ ≤ B)
    (hgb : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i g p‖ ≤ C) (k : Fin 3) :
    ‖iteratedFDeriv ℝ (k : ℕ) (fun q => f q*g q) p‖ ≤ 4*B*C := by
  have h := norm_iteratedFDeriv_mul_le hf hg p (by simp : (k : ℕ∞ω) ≤ ∞)
  apply h.trans
  have heach (i : ℕ) (hi : i ∈ Finset.range ((k : ℕ)+1)) :
      ((k : ℕ).choose i : ℝ)*‖iteratedFDeriv ℝ i f p‖*
        ‖iteratedFDeriv ℝ ((k : ℕ)-i) g p‖ ≤ ((k : ℕ).choose i : ℝ)*B*C := by
    have hi2 : i ≤ 2 := by have := Finset.mem_range.mp hi; have := k.isLt; omega
    have hki : (k : ℕ)-i ≤ 2 := by have := k.isLt; omega
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hfb i hi2) (by positivity))
      (hgb _ hki) (norm_nonneg _) (by positivity)
  have hs := Finset.sum_le_sum heach
  apply hs.trans
  fin_cases k <;> norm_num [Finset.sum_range_succ] <;> nlinarith [mul_nonneg hB hC]

theorem real_distance_coordinate_power_C2_bound (j : Fin 3) (n : ℕ)
    {p : Fin 3 → ℝ} {R : ℝ} (hR : 0 ≤ R) (hp : ‖p‖ ≤ R) (k : Fin 3) :
    ‖iteratedFDeriv ℝ (k : ℕ) (fun q : Fin 3 → ℝ => (q j)^n) p‖ ≤
      (4*(1+R))^n := by
  induction n generalizing k with
  | zero =>
      fin_cases k <;> simp [norm_iteratedFDeriv_zero, iteratedFDeriv_const_of_ne]
  | succ n ih =>
      have hc : ContDiff ℝ ∞ (fun q : Fin 3 → ℝ => q j) :=
        (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).contDiff
      have hn : ContDiff ℝ ∞ (fun q : Fin 3 → ℝ => (q j)^n) := hc.pow n
      have hcoord (i : ℕ) (hi : i ≤ 2) :
          ‖iteratedFDeriv ℝ i (fun q : Fin 3 → ℝ => q j) p‖ ≤ 1+R := by
        have hj : |p j| ≤ R := (norm_le_pi_norm p j).trans hp
        exact (real_distance_coordinate_jet_norm_le j p i hi).trans (by linarith)
      have hb := real_C2_product_uniform_bound hc hn p (by positivity : 0 ≤ 1+R)
        (by positivity : 0 ≤ (4*(1+R))^n) hcoord
        (fun i hi => ih ⟨i, by omega⟩) k
      have heq : (fun q : Fin 3 → ℝ => (q j)^(n+1)) =
          (fun q : Fin 3 → ℝ => q j*(q j)^n) := by funext q; rw [pow_succ]; ring
      rw [heq]
      exact hb.trans_eq (by rw [pow_succ]; ring)

theorem realDistanceMonomial_explicit_C2_bound (α : DistanceMultiIndex)
    {p : Fin 3 → ℝ} {R : ℝ} (hR : 0 ≤ R) (hp : ‖p‖ ≤ R) (k : Fin 3) :
    ‖iteratedFDeriv ℝ (k : ℕ) (realDistanceMonomial α) p‖ ≤
      16*(4*(1+R))^(∑ j : Fin 3, α j) := by
  let G : ℝ := 4*(1+R)
  have hcont (j : Fin 3) : ContDiff ℝ ∞ (fun q : Fin 3 → ℝ => (q j)^(α j)) := by fun_prop
  have hpower (j : Fin 3) (i : ℕ) (hi : i ≤ 2) :
      ‖iteratedFDeriv ℝ i (fun q : Fin 3 → ℝ => (q j)^(α j)) p‖ ≤ G^(α j) :=
    real_distance_coordinate_power_C2_bound j (α j) hR hp ⟨i, by omega⟩
  have h01 (i : ℕ) (hi : i ≤ 2) :
      ‖iteratedFDeriv ℝ i (fun q : Fin 3 → ℝ => (q 0)^(α 0)*(q 1)^(α 1)) p‖ ≤
        4*G^(α 0)*G^(α 1) :=
    real_C2_product_uniform_bound (hcont 0) (hcont 1) p (by dsimp [G]; positivity)
      (by dsimp [G]; positivity) (hpower 0) (hpower 1) ⟨i, by omega⟩
  have hb := real_C2_product_uniform_bound ((hcont 0).mul (hcont 1)) (hcont 2) p
    (by dsimp [G]; positivity : 0 ≤ 4*G^(α 0)*G^(α 1))
    (by dsimp [G]; positivity : 0 ≤ G^(α 2)) h01 (hpower 2) k
  have heq : realDistanceMonomial α =
      (fun q : Fin 3 → ℝ => ((q 0)^(α 0)*(q 1)^(α 1))*(q 2)^(α 2)) := by
    funext q
    simp [realDistanceMonomial, Fin.prod_univ_three]
  rw [heq]
  exact hb.trans_eq (by rw [Fin.sum_univ_three, pow_add, pow_add]; dsimp [G]; ring)

def distanceC2DyadicRoundingBudget (s : Finset DistanceMultiIndex) (R : ℝ) : ℝ :=
  ∑ α ∈ s, 16*(4*(1+max 0 R))^(∑ j : Fin 3, α j)

theorem distanceC2DyadicRoundingBudget_nonneg (s : Finset DistanceMultiIndex) (R : ℝ) :
    0 ≤ distanceC2DyadicRoundingBudget s R := by
  unfold distanceC2DyadicRoundingBudget
  exact Finset.sum_nonneg fun _ _ => by positivity

theorem dyadic_realDistancePolynomial_uniform_C2
    (s : Finset DistanceMultiIndex) (c : DistanceMultiIndex → ℝ) (R : ℝ) (b : ℕ)
    {p : Fin 3 → ℝ} (hp : ‖p‖ ≤ R) (k : Fin 3) :
    ‖iteratedFDeriv ℝ (k : ℕ) (realDistancePolynomial s c) p-
      iteratedFDeriv ℝ (k : ℕ)
        (realDistancePolynomial s (fun α => (dyadicDistanceCoefficient b (c α) : ℝ))) p‖ ≤
      distanceC2DyadicRoundingBudget s R*(1/2 : ℝ)^b := by
  rw [iteratedFDeriv_realDistancePolynomial, iteratedFDeriv_realDistancePolynomial,
    ←Finset.sum_sub_distrib]
  simp_rw [←sub_smul]
  calc
    _ ≤ ∑ α ∈ s, ‖(c α-(dyadicDistanceCoefficient b (c α) : ℝ)) •
      iteratedFDeriv ℝ (k : ℕ) (realDistanceMonomial α) p‖ := norm_sum_le _ _
    _ ≤ ∑ α ∈ s, (16*(4*(1+max 0 R))^(∑ j : Fin 3, α j))*(1/2 : ℝ)^b := by
      apply Finset.sum_le_sum
      intro α hα
      rw [norm_smul, Real.norm_eq_abs]
      have hm := realDistanceMonomial_explicit_C2_bound α (le_max_left 0 R)
        (hp.trans (le_max_right 0 R)) k
      have hh := mul_le_mul (dyadicDistanceCoefficient_abs_error b (c α)) hm
        (norm_nonneg _) (by positivity : 0 ≤ (1/2 : ℝ)^b)
      exact hh.trans_eq (mul_comm _ _)
    _ = distanceC2DyadicRoundingBudget s R*(1/2 : ℝ)^b := by
      simp only [distanceC2DyadicRoundingBudget, Finset.sum_mul]

#print axioms dyadicDistanceCoefficient_error
#print axioms realDistanceMonomial_explicit_C2_bound
#print axioms dyadic_realDistancePolynomial_uniform_C2
end ManyBody.S8
