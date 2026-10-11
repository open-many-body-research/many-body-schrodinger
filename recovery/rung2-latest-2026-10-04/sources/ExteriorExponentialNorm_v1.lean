import ExteriorExponentialGradient_v1
import WeightedMultiplierBound_v1

/-! Uniform actual L² bounds for saturated exterior exponential weights.
The only analytic premise beyond the actual eigen-equation is an explicitly
stated exterior H¹ form coercivity estimate. No decay premise is assumed. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

theorem scalar_eigen_exterior_exponential_uniform_bound
    {N : ℕ} {Z E R δ a : ℝ} {f : SpatialL2 N}
    (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    (hR : 0 < R) (ha : 0 ≤ a) (hgap : a^2 < δ)
    (hcoerc : ∀ (v : SpatialL2 N) (q : ℝ), scalarCoulombH1FormValue N Z v q →
      (∀ᵐ x, ‖x‖ ≤ R → v x = 0) → δ*‖v‖^2 ≤ q-E*‖v‖^2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ) (hL : 0 < L),
      ‖boundedRealMul (exteriorExpWeight N R a L)
        (exteriorExpWeight_memLp_top N R a hL) f‖ ≤ C := by
  obtain ⟨K,hK,hcut⟩ := scaledCutoff_derivative_bound N
  let B := exteriorWeightError N R a K
  have hB : 0 ≤ B := by dsimp [B,exteriorWeightError]; positivity
  refine ⟨Real.sqrt (B*‖f‖^2/(δ-a^2)),Real.sqrt_nonneg _,fun L hL => ?_⟩
  apply Real.le_sqrt_of_sq_le
  apply (le_div_iff₀ (sub_pos.mpr hgap)).mpr
  have h := scalar_eigen_weighted_exterior_bound hg hcoerc
    (exteriorExpWeight N R a L) (exteriorExpWeight_contDiff N R a hL)
    (exteriorExpWeight_memLp_top N R a hL)
    (exteriorExpWeight_partial_memLp_top N hR ha hL)
    (fun x hx => exteriorExpWeight_zero_on_ball hR a L x hx) (a^2) B
    (exteriorExpWeight_gradient_bound hR ha hL hK (hcut R hR))
  nlinarith

#print axioms scalar_eigen_exterior_exponential_uniform_bound
end TheoremT.Continuum
