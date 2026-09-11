import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.CompactOpen
import Mathlib.Tactic

/-! Uniform Bernstein approximation over a compact family of real functions.
The polynomial expression is the actual finite sum of sampled function values.
The proof uses Banach-valued Bernstein approximation and two supremum-norm
evaluation bounds. -/

noncomputable section
open Filter
open scoped unitInterval Topology BigOperators
namespace TheoremT.HydrogenPolynomialDensityFamilyC0

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

def familyBernstein (F : C(X × I, ℝ)) (n : ℕ) (y : X) (x : I) : ℝ :=
  ∑ k : Fin (n + 1), bernstein n k x * F (y, bernstein.z k)

/-- One degree threshold works simultaneously for all parameters and all
points of the unit interval. No continuity-modulus or approximation premise
is supplied: continuity of `F` is encoded by its actual continuous-map type. -/
theorem familyBernstein_uniform (F : C(X × I, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ y : X, ∀ x : I,
      |familyBernstein F n y x - F (y, x)| < ε := by
  let fc : C(I, C(X, ℝ)) := (F.comp ContinuousMap.prodSwap).curry
  have hev := (Metric.tendsto_nhds.mp (bernsteinApproximation_uniform fc)) ε hε
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hev
  refine ⟨n₀, ?_⟩
  intro n hn y x
  have houter := ContinuousMap.dist_apply_le_dist (f := bernsteinApproximation n fc) (g := fc) x
  have hinner := ContinuousMap.dist_apply_le_dist
    (f := bernsteinApproximation n fc x) (g := fc x) y
  have h := (hinner.trans houter).trans_lt (hn₀ n hn)
  simpa [Real.dist_eq, fc, familyBernstein, bernsteinApproximation.apply] using h

omit [CompactSpace X] in
/-- The displayed Bernstein family samples the genuine real grid `k/n`. -/
theorem familyBernstein_grid_formula (F : C(X × I, ℝ)) (n : ℕ) (y : X) (x : I) :
    familyBernstein F n y x =
      ∑ k : Fin (n + 1), (n.choose k : ℝ) * (x : ℝ) ^ (k : ℕ) *
        (1 - (x : ℝ)) ^ (n - (k : ℕ)) * F (y, bernstein.z k) := by
  simp only [familyBernstein, bernstein_apply]

end TheoremT.HydrogenPolynomialDensityFamilyC0

#print axioms TheoremT.HydrogenPolynomialDensityFamilyC0.familyBernstein_uniform
#print axioms TheoremT.HydrogenPolynomialDensityFamilyC0.familyBernstein_grid_formula
