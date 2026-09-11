import WeakCoulombNorm_v2
import Mathlib.Data.Nat.Choose.Cast

/-! Spin summation preserves the proved coarse scalar multiplier coefficient.
No additional spin-state factor is introduced. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace TheoremT.Continuum

theorem coulomb_coarse_constant_eq (N : ℕ) (Z : ℝ) :
    2 * (|Z| * (N : ℝ) + (N.choose 2 : ℝ)) =
      (N : ℝ) * (2 * |Z| + (N : ℝ) - 1) := by
  rw [Nat.cast_choose_two]
  ring

/-- A quantitative bound on the full finite fermionic spin ambient space,
before restricting to its antisymmetric subspace. The spin multiplicity costs
no extra factor because its norm is the sum-of-squares norm. -/
theorem coulomb_product_spin_norm_le {N : ℕ} (Z : ℝ)
    (ψ : SpinSpace N) (d : Coordinate N → SpinSpace N)
    (hd : ∀ σ k, WeakPartial (ψ σ) (d k σ) k)
    (v : SpinSpace N)
    (hv : ∀ σ, v σ =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * ψ σ x) :
    ‖v‖ ≤ 2 * (|Z| * (N : ℝ) + (N.choose 2 : ℝ)) *
      Real.sqrt (∑ k : Coordinate N, ‖d k‖^2) := by
  let C : ℝ := 2 * (|Z| * (N : ℝ) + (N.choose 2 : ℝ))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hσ (σ : SpinConfiguration N) :
      ‖v σ‖^2 ≤ C^2 * (∑ k : Coordinate N, ‖d k σ‖^2) := by
    have h := coulomb_product_norm_le Z (ψ σ) (fun k => d k σ) (hd σ) (v σ) (hv σ)
    have hh := pow_le_pow_left₀ (norm_nonneg (v σ)) h 2
    have hDσ : 0 ≤ ∑ k : Coordinate N, ‖d k σ‖^2 :=
      Finset.sum_nonneg (fun k _ => sq_nonneg ‖d k σ‖)
    simpa only [C, mul_pow, Real.sq_sqrt hDσ]
      using hh
  have hsum : ‖v‖^2 ≤ C^2 * (∑ k : Coordinate N, ‖d k‖^2) := by
    calc
      ‖v‖^2 = ∑ σ : SpinConfiguration N, ‖v σ‖^2 := PiLp.norm_sq_eq_of_L2 _ v
      _ ≤ ∑ σ : SpinConfiguration N, C^2 * (∑ k : Coordinate N, ‖d k σ‖^2) :=
        Finset.sum_le_sum (fun σ _ => hσ σ)
      _ = C^2 * (∑ k : Coordinate N, ‖d k‖^2) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp_rw [← PiLp.norm_sq_eq_of_L2]
  have hD : 0 ≤ ∑ k : Coordinate N, ‖d k‖^2 := Finset.sum_nonneg (fun k _ => sq_nonneg ‖d k‖)
  have hs := Real.sq_sqrt hD
  have hn := Real.sqrt_nonneg (∑ k : Coordinate N, ‖d k‖^2)
  change ‖v‖ ≤ C * Real.sqrt (∑ k : Coordinate N, ‖d k‖^2)
  nlinarith [norm_nonneg v, mul_nonneg hC hn]

#print axioms coulomb_coarse_constant_eq
#print axioms coulomb_product_spin_norm_le

end TheoremT.Continuum
