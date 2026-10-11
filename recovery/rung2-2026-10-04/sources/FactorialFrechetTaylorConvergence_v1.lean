import FactorialFrechetSeries_v1
import FactorialFrechetTaylorRemainder_v1

/-! Actual Taylor convergence from smoothness and factorial bounds on the
segment. The remainder is proved in the imported module, not a hypothesis. -/
noncomputable section
open Filter
open scoped BigOperators Topology ContDiff
namespace TheoremT.Continuum
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem factorial_frechet_hasSum_on_segment (f : E → F) (x y : E) {C A : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hq : A*‖y‖ < 1)
    (hsmooth : ∀ t ∈ Set.Icc (0:ℝ) 1, ContDiffAt ℝ ∞ f (x+t • y))
    (hbound : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ k,
      ‖iteratedFDeriv ℝ k f (x+t • y)‖ ≤ C*A^k*(k.factorial : ℝ)) :
    HasSum (fun k => factorialFrechetSeries f x k (fun _ => y)) (f (x+y)) := by
  have hbase : ∀ k, ‖iteratedFDeriv ℝ k f x‖ ≤ C*A^k*(k.factorial : ℝ) := by
    intro k
    simpa only [zero_smul,add_zero] using hbound 0 (by norm_num) k
  have hsum := factorialFrechetSeries_summable_norm f x y hA hq hbase
  have hzero : Tendsto (fun n : ℕ => C*((n:ℝ)+1)*(A*‖y‖)^(n+1)) atTop (𝓝 0) := by
    have hz := (tendsto_self_mul_const_pow_of_lt_one
      (mul_nonneg hA (norm_nonneg y)) hq).comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_apply,Nat.cast_add,Nat.cast_one,mul_zero,mul_assoc] using hz.const_mul C
  have hrem : Tendsto (fun n : ℕ =>
      ‖(∑ k ∈ Finset.range (n+1),factorialFrechetSeries f x k (fun _ => y))-f (x+y)‖)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _) ?_ hzero
    intro n
    rw [norm_sub_rev]
    simpa only [factorialFrechetSeries_apply] using
      factorial_frechet_taylor_remainder_bound f x y hC hA hsmooth hbound n
  have ht : Tendsto (fun n : ℕ =>
      ∑ k ∈ Finset.range (n+1),factorialFrechetSeries f x k (fun _ => y))
      atTop (𝓝 (f (x+y))) := tendsto_iff_norm_sub_tendsto_zero.2 hrem
  exact (hasSum_iff_tendsto_nat_of_summable_norm hsum).2
    ((tendsto_add_atTop_iff_nat 1).1 ht)

#print axioms factorial_frechet_hasSum_on_segment
end TheoremT.Continuum
