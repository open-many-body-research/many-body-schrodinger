import HydrogenPolynomialDensityBernstein_v1

/-! Supremum stability and uniform C0 convergence for the explicit finite
Bernstein polynomial used in the derivative identity. -/
noncomputable section
open scoped Polynomial BigOperators unitInterval Topology
open Set Filter
namespace TheoremT.HydrogenPolynomialDensity

theorem bernsteinCombination_eval (n : ℕ) (c : ℕ → ℝ) (x : I) :
    (bernsteinCombination n c).eval (x : ℝ) =
      ∑ k : Fin (n + 1), c k * bernstein n k x := by
  simp only [bernsteinCombination, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, bernstein, Polynomial.toContinuousMapOn_apply,
    Polynomial.toContinuousMap_apply]
  exact (Fin.sum_univ_eq_sum_range _ _).symm

/-- Positive Bernstein weights of total mass one do not enlarge a coefficient error. -/
theorem bernsteinCombination_sup_stability (n : ℕ) (c d : ℕ → ℝ) {δ : ℝ}
    (h : ∀ k ≤ n, |c k - d k| ≤ δ) (x : I) :
    |(bernsteinCombination n c).eval (x : ℝ) -
      (bernsteinCombination n d).eval (x : ℝ)| ≤ δ := by
  rw [bernsteinCombination_eval, bernsteinCombination_eval, ← Finset.sum_sub_distrib]
  calc
    |∑ k : Fin (n + 1), (c k * bernstein n k x - d k * bernstein n k x)|
      ≤ ∑ k : Fin (n + 1), |c k * bernstein n k x - d k * bernstein n k x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin (n + 1), |c k - d k| * bernstein n k x := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← sub_mul, abs_mul, abs_of_nonneg bernstein_nonneg]
    _ ≤ ∑ k : Fin (n + 1), δ * bernstein n k x := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right (h k k.is_le) bernstein_nonneg
    _ = δ := by rw [← Finset.mul_sum, bernstein.probability, mul_one]

theorem gridBernsteinPolynomial_eval (n : ℕ) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc 0 1)) (x : I) :
    (gridBernsteinPolynomial n f).eval (x : ℝ) =
      bernsteinApproximation n
        ⟨fun x : I => f x, continuousOn_iff_continuous_domRestrict.mp hf⟩ x := by
  rw [gridBernsteinPolynomial, bernsteinCombination_eval, bernsteinApproximation.apply]
  apply Finset.sum_congr rfl
  intro k _
  change f ((k : ℕ) / (n : ℝ)) * bernstein n k x =
    bernstein n k x * f ((k : ℕ) / (n : ℝ))
  exact mul_comm _ _

/-- Uniform convergence of the actual coefficient-defined Bernstein polynomials. -/
theorem gridBernsteinPolynomial_uniform {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ x ∈ Icc (0 : ℝ) 1,
      |(gridBernsteinPolynomial n f).eval x - f x| < ε := by
  let F : C(I, ℝ) :=
    ⟨fun x : I => f x, continuousOn_iff_continuous_domRestrict.mp hf⟩
  have h := (Metric.tendsto_nhds.mp (bernsteinApproximation_uniform F)) ε hε
  filter_upwards [h] with n hn x hx
  have hn' : ‖bernsteinApproximation n F - F‖ < ε := by
    simpa only [dist_eq_norm] using hn
  have hp := (ContinuousMap.norm_coe_le_norm (bernsteinApproximation n F - F)
    (⟨x, hx⟩ : I)).trans_lt hn'
  rw [show (gridBernsteinPolynomial n f).eval x = bernsteinApproximation n F
    (⟨x, hx⟩ : I) from gridBernsteinPolynomial_eval n f hf (⟨x, hx⟩ : I)]
  have hFx : F (⟨x, hx⟩ : I) = f x := rfl
  simpa only [ContinuousMap.sub_apply, Real.norm_eq_abs, hFx] using hp

end TheoremT.HydrogenPolynomialDensity

#print axioms TheoremT.HydrogenPolynomialDensity.bernsteinCombination_sup_stability
#print axioms TheoremT.HydrogenPolynomialDensity.gridBernsteinPolynomial_uniform
