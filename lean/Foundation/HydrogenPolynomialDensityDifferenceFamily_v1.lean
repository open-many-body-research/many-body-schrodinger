import HydrogenPolynomialDensityDifference_v1
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-! Uniform forward-grid slope errors for parameterized C1 slices. -/

noncomputable section
open Set
namespace TheoremT.HydrogenPolynomialDensityDifferenceFamily
open TheoremT.HydrogenPolynomialDensityDifference

/-- A common continuity modulus of actual slice derivatives gives a common
forward-difference convergence index. The parameter type need not be topological. -/
theorem forwardSlope_family_uniform {Y : Type*} {s : Set Y} {f g : Y → ℝ → ℝ}
    (hf : ∀ y ∈ s, ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (f y) (g y x) (Icc 0 1) x)
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ s, ∀ x ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (0 : ℝ) 1,
        |x - z| < δ → |g y x - g y z| < ε)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n → ∀ y ∈ s, ∀ k : ℕ, k ≤ n →
      |forwardSlope (f y) n k - g y ((k : ℝ) / (n : ℝ))| < ε := by
  obtain ⟨δ, hδ, hδg⟩ := hmod ε hε
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (max (1 : ℝ) (1 / δ))
  have hn₀1 : (1 : ℝ) < n₀ := lt_of_le_of_lt (le_max_left _ _) hn₀
  have hn₀nat : 1 ≤ n₀ := by exact_mod_cast hn₀1.le
  refine ⟨n₀, hn₀nat, ?_⟩
  intro n hn y hy k hk
  have hnR : (0 : ℝ) < n := by exact_mod_cast (hn₀nat.trans hn)
  have hnn : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hnδ : 1 / δ < (n : ℝ) :=
    (lt_of_le_of_lt (le_max_right _ _) hn₀).trans_le hnn
  have hsmall : 1 / (n : ℝ) < δ := by
    apply (div_lt_iff₀ hnR).mpr
    have := (div_lt_iff₀ hδ).mp hnδ
    nlinarith
  have hgrid : (k : ℝ) / (n : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_iff₀ hnR).mpr
      simpa using (show (k : ℝ) ≤ n by exact_mod_cast hk)
  obtain ⟨ξ, _, hξ, heq, hnear⟩ := forwardSlope_eq_derivative_near
    (hf y hy) (hn₀nat.trans hn) hk
  rw [heq]
  exact hδg y hy ξ hξ _ hgrid (hnear.trans_lt hsmall)

/-- Compactness of the parameter set and continuity of the actual derivative
on its product with `[0,1]` discharge the common-modulus premise. -/
theorem forwardSlope_compact_family_uniform {Y : Type*} [PseudoMetricSpace Y]
    {s : Set Y} (hs : IsCompact s) {f g : Y → ℝ → ℝ}
    (hf : ∀ y ∈ s, ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (f y) (g y x) (Icc 0 1) x)
    (hg : ContinuousOn (fun p : Y × ℝ => g p.1 p.2) (s ×ˢ Icc (0 : ℝ) 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n → ∀ y ∈ s, ∀ k : ℕ, k ≤ n →
      |forwardSlope (f y) n k - g y ((k : ℝ) / (n : ℝ))| < ε := by
  apply forwardSlope_family_uniform hf ?_ hε
  intro η hη
  have huc := (hs.prod isCompact_Icc).uniformContinuousOn_of_continuous hg
  obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuousOn_iff.mp huc η hη
  refine ⟨δ, hδ, ?_⟩
  intro y hy x hx z hz hxz
  have hdist : dist (y, x) (y, z) < δ := by
    simpa only [Prod.dist_eq, dist_self, Real.dist_eq,
      max_eq_right (abs_nonneg (x - z))] using hxz
  simpa only [Real.dist_eq] using hδg (y, x) ⟨hy, hx⟩ (y, z) ⟨hy, hz⟩ hdist

end TheoremT.HydrogenPolynomialDensityDifferenceFamily

#print axioms TheoremT.HydrogenPolynomialDensityDifferenceFamily.forwardSlope_family_uniform
#print axioms TheoremT.HydrogenPolynomialDensityDifferenceFamily.forwardSlope_compact_family_uniform
