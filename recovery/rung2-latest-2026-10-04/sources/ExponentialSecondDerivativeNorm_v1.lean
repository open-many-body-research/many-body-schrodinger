import ExponentialDerivativeNorm_v1
import WeightedCoulombLaplacianBound_v1
import WeightedMixedDerivativeBound_v1
import BoundedExponentialSecond_v1

/-! Uniform exponential saturation bounds on every actual ordered weak second
derivative of a Coulomb eigenfunction. All weighted Laplacian and potential
control is proved from the actual eigen-equation and first derivative estimates. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum

theorem scalar_eigen_exponential_second_derivative_uniform_bound
    {N : ℕ} {Z E a : ℝ} {f : SpatialL2 N}
    (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    (d : Coordinate N → SpatialL2 N) (e : Coordinate N → Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    (ha : 0 ≤ a)
    (hw : MemLp (fun x => Real.exp (a*smoothConfigurationRadius N x) • f x) 2 volume) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ) (hL : 0 < L) (k l : Coordinate N),
      ‖boundedRealMul (boundedExpWeight N a L) (boundedExpWeight_memLp_top N a hL) (e k l)‖ ≤ C := by
  obtain ⟨C1,hC1,hfirstnorm⟩ := scalar_eigen_exponential_derivative_uniform_bound hg d hd ha hw
  let C0 := ‖hw.toLp (fun x => Real.exp (a*smoothConfigurationRadius N x) • f x)‖
  have hC0 : 0 ≤ C0 := norm_nonneg _
  let B := a^2+2*a
  let D := 2*(|E| * C0+(2*(|Z| * (N : ℝ)+(N.choose 2 : ℝ)))*
    Real.sqrt ((Fintype.card (Coordinate N) : ℝ)*(C1+a*C0)^2))
  let K := D+((Fintype.card (Coordinate N) : ℝ)+1)*(2*a*C1+B*C0)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hK : 0 ≤ K := by dsimp [K,D,B]; positivity
  refine ⟨K,hK,fun L hL k l => ?_⟩
  have h0 := boundedExpWeight_mul_norm_le a hL f hw
  have hp (x : Configuration N) := boundedExpWeight_pos N a hL x
  have hfirst (x : Configuration N) (i : Coordinate N) :
      |fderiv ℝ (boundedExpWeight N a L) x (coordinateVector i)| ≤
        a*|boundedExpWeight N a L x| := by
    rw [abs_of_pos (hp x)]
    exact boundedExpWeight_partial_abs_le ha hL x i
  have hsecond (x : Configuration N) (i j : Coordinate N) :
      |fderiv ℝ (fun y => fderiv ℝ (boundedExpWeight N a L) y (coordinateVector i))
        x (coordinateVector j)| ≤ B*|boundedExpWeight N a L x| := by
    rw [abs_of_pos (hp x)]
    exact boundedExpWeight_mixed_partial_abs_le ha hL x i j
  have hΔ := scalar_eigen_weighted_laplacian_bound hg d e hd he (boundedExpWeight N a L)
    (boundedExpWeight_contDiff N a hL) (boundedExpWeight_memLp_top N a hL)
    (boundedExpWeight_partial_memLp_top N ha hL) ha hC0 hC1 hfirst h0 (hfirstnorm L hL)
  exact weak_weighted_mixed_bound d e hd he (boundedExpWeight N a L)
    (boundedExpWeight_contDiff N a hL) (boundedExpWeight_memLp_top N a hL)
    (boundedExpWeight_partial_memLp_top N ha hL) (boundedExpWeight_mixed_partial_memLp_top N ha hL)
    ha hB hfirst hsecond h0 (hfirstnorm L hL) hΔ k l

#print axioms scalar_eigen_exponential_second_derivative_uniform_bound
end TheoremT.Continuum
