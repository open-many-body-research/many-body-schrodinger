import CoulombH2Decay_v1
import TwoElectronGroundDecay_v1

/-! Polynomial moments of the actual physical configuration norm, obtained
from exponential L2 membership. The all-order factor is k! / a^k, and the
prefactor is the actual weighted L2 norm; no computable norm is asserted. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace ManyBody.S8
open TheoremT.Continuum

theorem physical_polynomial_weight_le_exponential {a t : ℝ} (ha : 0 < a)
    (ht : 0 ≤ t) (k : ℕ) :
    t^k ≤ ((k.factorial : ℝ) / a^k) * Real.exp (a*t) := by
  have hf : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hp := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp (a*t) (mul_nonneg ha.le ht) k)
  calc
    t^k = (a*t)^k / a^k := by rw [mul_pow, mul_div_cancel_left₀ _ (pow_ne_zero _ ha.ne')]
    _ ≤ (Real.exp (a*t)*(k.factorial : ℝ)) / a^k :=
      div_le_div_of_nonneg_right hp (pow_nonneg ha.le k)
    _ = _ := by ring

theorem physical_polynomial_moment_memLp {N : ℕ} {a : ℝ} (ha : 0 < a)
    (f : SpatialL2 N)
    (hw : MemLp (fun x => Real.exp (a*‖x‖) • f x) 2 volume) (k : ℕ) :
    MemLp (fun x => ‖x‖^k • f x) 2 volume := by
  have hC : 0 ≤ (k.factorial : ℝ)/a^k := by positivity
  apply (hw.const_smul ((k.factorial : ℝ)/a^k)).of_le
    ((continuous_norm.pow k).aestronglyMeasurable.smul (Lp.aestronglyMeasurable f))
  exact Eventually.of_forall (fun x => by
    change ‖‖x‖^k • f x‖ ≤ ‖((k.factorial : ℝ)/a^k) • (Real.exp (a*‖x‖) • f x)‖
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg x) k),
      abs_of_nonneg hC,abs_of_pos (Real.exp_pos _)]
    rw [←mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (physical_polynomial_weight_le_exponential ha (norm_nonneg x) k) (norm_nonneg (f x)))

def physicalPolynomialMomentL2 {N : ℕ} {a : ℝ} (ha : 0 < a)
    (f : SpatialL2 N) (hw : MemLp (fun x => Real.exp (a*‖x‖) • f x) 2 volume)
    (k : ℕ) : SpatialL2 N :=
  (physical_polynomial_moment_memLp ha f hw k).toLp (fun x => ‖x‖^k • f x)

theorem physicalPolynomialMomentL2_ae {N : ℕ} {a : ℝ} (ha : 0 < a)
    (f : SpatialL2 N) (hw : MemLp (fun x => Real.exp (a*‖x‖) • f x) 2 volume)
    (k : ℕ) : physicalPolynomialMomentL2 ha f hw k =ᵐ[volume] (fun x => ‖x‖^k • f x) :=
  MemLp.coeFn_toLp _

theorem physicalPolynomialMomentL2_norm_bound {N : ℕ} {a : ℝ} (ha : 0 < a)
    (f : SpatialL2 N) (hw : MemLp (fun x => Real.exp (a*‖x‖) • f x) 2 volume)
    (k : ℕ) :
    ‖physicalPolynomialMomentL2 ha f hw k‖ ≤ ((k.factorial : ℝ)/a^k) *
      ‖hw.toLp (fun x => Real.exp (a*‖x‖) • f x)‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [physicalPolynomialMomentL2_ae ha f hw k,hw.coeFn_toLp] with x hx hy
  rw [hx,hy]
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg x) k),
    abs_of_pos (Real.exp_pos _)]
  rw [←mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (physical_polynomial_weight_le_exponential ha (norm_nonneg x) k) (norm_nonneg (f x))

#print axioms physical_polynomial_weight_le_exponential
#print axioms physical_polynomial_moment_memLp
#print axioms physicalPolynomialMomentL2_ae
#print axioms physicalPolynomialMomentL2_norm_bound
end ManyBody.S8
