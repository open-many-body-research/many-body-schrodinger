import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Tactic

/-! A genuine Taylor remainder estimate from smoothness and actual Frechet
operator-norm factorial bounds along the segment. No remainder or analyticity
hypothesis is supplied. The weight is bounded by one, retaining a harmless
linear factor in the order. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem factorial_frechet_taylor_remainder_bound (f : E → F) (x y : E)
    {C A : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hsmooth : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ f (x+t • y))
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ k : ℕ,
      ‖iteratedFDeriv ℝ k f (x+t • y)‖ ≤ C*A^k*(k.factorial : ℝ)) (n : ℕ) :
    ‖f (x+y) - ∑ k ∈ Finset.range (n+1),
      (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f x (fun _ => y)‖ ≤
      C*((n : ℝ)+1)*(A*‖y‖)^(n+1) := by
  have htaylor := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := f) (x := x) (y := y) (n := n)
    (fun t ht => (hsmooth t ht).of_le (by simp))
  have hrem : f (x+y) - ∑ k ∈ Finset.range (n+1),
      (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f x (fun _ => y) =
      (n.factorial : ℝ)⁻¹ • ∫ t in (0 : ℝ)..1,
        (1-t)^n • iteratedFDeriv ℝ (n+1) f (x+t • y) (fun _ => y) := by
    rw [htaylor]
    abel
  have hval (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ‖iteratedFDeriv ℝ (n+1) f (x+t • y) (fun _ => y)‖ ≤
        C*A^(n+1)*((n+1).factorial : ℝ)*‖y‖^(n+1) := by
    simpa using ContinuousMultilinearMap.le_of_opNorm_le (hbound t ht (n+1))
      (fun _ => y)
  have hi : ‖∫ t in (0 : ℝ)..1,
      (1-t)^n • iteratedFDeriv ℝ (n+1) f (x+t • y) (fun _ => y)‖ ≤
      C*A^(n+1)*((n+1).factorial : ℝ)*‖y‖^(n+1) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1)
      (f := fun t => (1-t)^n • iteratedFDeriv ℝ (n+1) f (x+t • y) (fun _ => y))
      (C := C*A^(n+1)*((n+1).factorial : ℝ)*‖y‖^(n+1)) (fun t ht => by
        rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
        have htn : 0 ≤ 1-t := by linarith [ht.2]
        have hto : 1-t ≤ 1 := by linarith [ht.1]
        have hweight : (1-t)^n ≤ 1 := pow_le_one₀ htn hto
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg htn n)]
        calc
          _ ≤ 1 * ‖iteratedFDeriv ℝ (n+1) f (x+t • y) (fun _ => y)‖ :=
            mul_le_mul_of_nonneg_right hweight (norm_nonneg _)
          _ ≤ _ := by simpa only [one_mul] using hval t ⟨ht.1.le,ht.2⟩)
    simpa only [sub_zero, abs_one, mul_one] using h
  have hfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [hrem, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  calc
    _ ≤ (n.factorial : ℝ)⁻¹ *
      (C*A^(n+1)*((n+1).factorial : ℝ)*‖y‖^(n+1)) :=
        mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = _ := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_pow]
      field_simp
      <;> ring

end TheoremT.Continuum
