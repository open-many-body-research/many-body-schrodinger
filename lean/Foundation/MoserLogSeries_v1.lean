import AtomicMoserExponents_v1
import Mathlib.Analysis.SpecificLimits.Normed

/-! The summable logarithmic budget for a polynomial Moser coefficient.
This is scalar analysis; application to the actual Coulomb norm sequence is separate. -/
noncomputable section
open Filter
open scoped BigOperators
namespace TheoremT.Continuum

def moserLogWeight (B c : ℝ) (k : ℕ) : ℝ :=
  (Real.log B+2*(k:ℝ)*Real.log c)*(c⁻¹)^k

theorem moserLogWeight_nonneg {B c : ℝ} (hB : 1 ≤ B) (hc : 1 < c) (k : ℕ) :
    0 ≤ moserLogWeight B c k := by
  have hB' := Real.log_nonneg hB
  have hc' := Real.log_nonneg hc.le
  have hc0 : 0 ≤ c := by linarith
  unfold moserLogWeight; positivity

theorem moserLogWeight_summable {B c : ℝ} (hc : 1 < c) :
    Summable (moserLogWeight B c) := by
  have hc0 : 0 < c := by linarith
  have hi0 : 0 ≤ c⁻¹ := inv_nonneg.mpr hc0.le
  have hi1 : c⁻¹ < 1 := (inv_lt_one₀ hc0).mpr hc
  have hin : ‖c⁻¹‖ < 1 := by rwa [Real.norm_eq_abs,abs_of_nonneg hi0]
  have hgeo := summable_geometric_of_lt_one hi0 hi1
  have hlin : Summable (fun k : ℕ => (k:ℝ)*(c⁻¹)^k) := by
    simpa using (summable_norm_pow_mul_geometric_of_norm_lt_one 1 hin).of_norm
  have he : moserLogWeight B c = (fun k : ℕ =>
      Real.log B*(c⁻¹)^k+(2*Real.log c)*((k:ℝ)*(c⁻¹)^k)) := by
    funext k; unfold moserLogWeight; ring
  rw [he]
  exact (hgeo.mul_left (Real.log B)).add (hlin.mul_left (2*Real.log c))

theorem moserLogWeight_partial_sum_le {B c : ℝ} (hB : 1 ≤ B) (hc : 1 < c) (k : ℕ) :
    ∑ j ∈ Finset.range k, moserLogWeight B c j ≤ ∑' j, moserLogWeight B c j :=
  (moserLogWeight_summable hc).sum_le_tsum (Finset.range k)
    (fun j _ => moserLogWeight_nonneg hB hc j)

theorem moser_polynomial_factor_exp {B c : ℝ} (hB : 1 ≤ B) (hc : 1 < c) (k : ℕ) :
    (B*(c^k)^2)^((c^k)⁻¹) = Real.exp (moserLogWeight B c k) := by
  have hB0 : 0 < B := by linarith
  have hc0 : 0 < c := by linarith
  rw [Real.rpow_def_of_pos (by positivity),Real.log_mul hB0.ne' (by positivity),
    Real.log_pow,Real.log_pow]
  congr 1
  unfold moserLogWeight
  rw [inv_pow]
  norm_num only [Nat.cast_ofNat]
  ring
  all_goals simp

#print axioms moserLogWeight_summable
#print axioms moser_polynomial_factor_exp
end TheoremT.Continuum
