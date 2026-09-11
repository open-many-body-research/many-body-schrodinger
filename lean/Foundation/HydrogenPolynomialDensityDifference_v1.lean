import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic

/-! Forward differences for a genuine continuously differentiable function on
the unit interval.  The intermediate point is supplied by the scalar mean value
theorem, and the uniform error by compactness and continuity of the derivative.
No polynomial approximation or density premise is used. -/

noncomputable section
open Set
namespace TheoremT.HydrogenPolynomialDensityDifference

def forwardSlope (f : ℝ → ℝ) (n k : ℕ) : ℝ :=
  (n + 1 : ℝ) * (f ((k + 1 : ℝ) / (n + 1 : ℝ)) - f ((k : ℝ) / (n + 1 : ℝ)))

/-- Every forward-grid slope is an actual derivative value.  Its intermediate
point lies within `1/n` of the degree-`n` Bernstein sampling point. -/
theorem forwardSlope_eq_derivative_near {f g : ℝ → ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (g x) (Icc 0 1) x)
    {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) :
    ∃ ξ ∈ Ioo ((k : ℝ) / (n + 1 : ℝ)) ((k + 1 : ℝ) / (n + 1 : ℝ)),
      ξ ∈ Icc (0 : ℝ) 1 ∧ forwardSlope f n k = g ξ ∧
        |ξ - (k : ℝ) / (n : ℝ)| ≤ 1 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have ha : 0 ≤ (k : ℝ) / (n + 1 : ℝ) := div_nonneg hk0 hn1.le
  have hb : (k + 1 : ℝ) / (n + 1 : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hn1).mpr
    linarith
  have hab : (k : ℝ) / (n + 1 : ℝ) < (k + 1 : ℝ) / (n + 1 : ℝ) := by
    exact (div_lt_div_iff_of_pos_right hn1).mpr (by linarith)
  have hsub : Icc ((k : ℝ) / (n + 1 : ℝ)) ((k + 1 : ℝ) / (n + 1 : ℝ)) ⊆
      Icc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨ha.trans hx.1, hx.2.trans hb⟩
  have hfc : ContinuousOn f (Icc (0 : ℝ) 1) :=
    fun x hx => (hf x hx).continuousWithinAt
  obtain ⟨ξ, hξ, hmean⟩ := exists_hasDerivAt_eq_slope f g hab (hfc.mono hsub)
    (fun x hx => (hf x (hsub ⟨hx.1.le, hx.2.le⟩)).hasDerivAt
      (Icc_mem_nhds (ha.trans_lt hx.1) (hx.2.trans_le hb)))
  have hξ01 := hsub ⟨hξ.1.le, hξ.2.le⟩
  refine ⟨ξ, hξ, hξ01, ?_, ?_⟩
  · rw [forwardSlope, hmean]
    have hlength : (k + 1 : ℝ) / (n + 1 : ℝ) - (k : ℝ) / (n + 1 : ℝ) =
        1 / (n + 1 : ℝ) := by ring
    rw [hlength]
    simp only [one_div, div_inv_eq_mul]
    ring
  · have hlow : (k : ℝ) < ξ * (n + 1 : ℝ) := (div_lt_iff₀ hn1).mp hξ.1
    have hupp : ξ * (n + 1 : ℝ) < k + 1 := (lt_div_iff₀ hn1).mp hξ.2
    have heq : ((k : ℝ) / (n : ℝ)) * n = k := div_mul_cancel₀ _ hnR.ne'
    have hone : (1 / (n : ℝ)) * n = 1 := div_mul_cancel₀ _ hnR.ne'
    apply abs_le.mpr
    constructor
    · apply (mul_le_mul_iff_left₀ hnR).mp
      nlinarith [hξ01.2]
    · apply (mul_le_mul_iff_left₀ hnR).mp
      nlinarith [hξ01.1]

/-- The entire row of actual forward differences converges uniformly to the
derivative sampled on the degree-`n` grid. -/
theorem forwardSlope_uniform_derivative {f g : ℝ → ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (g x) (Icc 0 1) x)
    (hg : ContinuousOn g (Icc (0 : ℝ) 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ, k ≤ n →
      |forwardSlope f n k - g ((k : ℝ) / (n : ℝ))| < ε := by
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hg
  obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (max (1 : ℝ) (1 / δ))
  have hn₀1 : (1 : ℝ) < n₀ := lt_of_le_of_lt (le_max_left _ _) hn₀
  have hn₀nat : 1 ≤ n₀ := by exact_mod_cast hn₀1.le
  refine ⟨n₀, hn₀nat, ?_⟩
  intro n hn k hk
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
  obtain ⟨ξ, _, hξ, heq, hnear⟩ := forwardSlope_eq_derivative_near hf (hn₀nat.trans hn) hk
  rw [heq]
  have hdist : dist ξ ((k : ℝ) / (n : ℝ)) < δ := by
    simpa only [Real.dist_eq] using hnear.trans_lt hsmall
  simpa only [Real.dist_eq] using hδg ξ hξ _ hgrid hdist

end TheoremT.HydrogenPolynomialDensityDifference

#print axioms TheoremT.HydrogenPolynomialDensityDifference.forwardSlope_eq_derivative_near
#print axioms TheoremT.HydrogenPolynomialDensityDifference.forwardSlope_uniform_derivative
