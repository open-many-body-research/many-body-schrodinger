import WeightedEigenDerivativeBound_v1
import ExponentialWeightComparison_v1

/-! A cap-independent bound on the actual weighted weak first derivatives of
any Coulomb eigenfunction with exponential L² decay. No binding, gap, or
uniqueness assumption is needed for this transfer. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum

theorem scalar_eigen_exponential_derivative_uniform_bound
    {N : ℕ} {Z E a : ℝ} {f : SpatialL2 N}
    (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    (d : Coordinate N → SpatialL2 N) (hd : ∀ k, WeakPartial f (d k) k)
    (ha : 0 ≤ a)
    (hw : MemLp (fun x => Real.exp (a*smoothConfigurationRadius N x) • f x) 2 volume) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ) (hL : 0 < L) (k : Coordinate N),
      ‖boundedRealMul (boundedExpWeight N a L) (boundedExpWeight_memLp_top N a hL) (d k)‖ ≤ C := by
  let K := 8*(|E|+(2*(|Z| *(N : ℝ)+(N.choose 2 : ℝ)))^2)+6*a^2
  let W := hw.toLp (fun x => Real.exp (a*smoothConfigurationRadius N x) • f x)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨Real.sqrt (K*‖W‖^2),Real.sqrt_nonneg _,fun L hL k => ?_⟩
  apply Real.le_sqrt_of_sq_le
  have hder := scalar_eigen_weighted_derivative_bound hg d hd (boundedExpWeight N a L)
    (boundedExpWeight_contDiff N a hL) (boundedExpWeight_memLp_top N a hL)
    (boundedExpWeight_partial_memLp_top N ha hL) k
  have hgrad := weighted_gradient_integral_bound f (boundedExpWeight N a L)
    (boundedExpWeight_memLp_top N a hL) (boundedExpWeight_partial_memLp_top N ha hL)
    (a^2/2) 0 (fun x => by nlinarith [boundedExpWeight_gradient_sq_le ha hL x])
  have hU := pow_le_pow_left₀ (norm_nonneg _)
    (boundedExpWeight_mul_norm_le a hL f hw) 2
  have hfinal := mul_le_mul_of_nonneg_left hU hK
  dsimp only [K,W] at hfinal ⊢
  nlinarith

#print axioms scalar_eigen_exponential_derivative_uniform_bound
end TheoremT.Continuum
