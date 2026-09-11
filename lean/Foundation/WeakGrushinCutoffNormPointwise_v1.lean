import WeightedFiniteCauchy_v1

/-! Explicit pointwise bounds for the genuine weak Grushin cutoff commutator.
The constants 2 and 8 come from the two-term norm-square inequality and weighted
finite Cauchy, with no spectator-dimension factor. This file proves no integral
estimate; every scalar coefficient is the actual derivative expression. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

def combinedCutoffScalar (c : ℝ) (χ : Space κ → ℝ) (p : Space κ) : ℝ :=
  (∑ i : Fin 4, fderiv ℝ (fun q => fderiv ℝ χ q (yDir i)) p (yDir i)) +
    (c*‖p.1‖^2)*(∑ j : κ, fderiv ℝ (fun q => fderiv ℝ χ q (tDir j)) p (tDir j))

def cutoffGradientWeight (c : ℝ) (χ : Space κ → ℝ) (p : Space κ) : ℝ :=
  (∑ i : Fin 4, (fderiv ℝ χ p (yDir i))^2) +
    (c*‖p.1‖^2)*(∑ j : κ, (fderiv ℝ χ p (tDir j))^2)

def firstJetEnergyDensity (c : ℝ)
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (p : Space κ) : ℝ :=
  (∑ i : Fin 4, ‖d (yDir i) p‖^2) +
    (c*‖p.1‖^2)*(∑ j : κ, ‖d (tDir j) p‖^2)

def cutoffFirstCross (c : ℝ) (χ : Space κ → ℝ)
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (p : Space κ) : ℂ :=
  (∑ i : Fin 4, fderiv ℝ χ p (yDir i) • d (yDir i) p) +
    (c*‖p.1‖^2) • (∑ j : κ, fderiv ℝ χ p (tDir j) • d (tDir j) p)

theorem cutoffGradientWeight_nonneg {c : ℝ} (hc : 0 ≤ c)
    (χ : Space κ → ℝ) (p : Space κ) : 0 ≤ cutoffGradientWeight c χ p := by
  unfold cutoffGradientWeight
  exact add_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (mul_nonneg (mul_nonneg hc (sq_nonneg _)) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

theorem firstJetEnergyDensity_nonneg {c : ℝ} (hc : 0 ≤ c)
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (p : Space κ) :
    0 ≤ firstJetEnergyDensity c d p := by
  unfold firstJetEnergyDensity
  exact add_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (mul_nonneg (mul_nonneg hc (sq_nonneg _)) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

theorem cutoffFirstCross_norm_sq_le {c : ℝ} (hc : 0 ≤ c)
    (χ : Space κ → ℝ) (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ)))
    (p : Space κ) :
    ‖cutoffFirstCross c χ d p‖^2 ≤ cutoffGradientWeight c χ p*firstJetEnergyDensity c d p := by
  let w : Fin 4 ⊕ κ → ℝ := Sum.elim (fun _ => 1) (fun _ => c*‖p.1‖^2)
  let a : Fin 4 ⊕ κ → ℝ := Sum.elim
    (fun i => fderiv ℝ χ p (yDir i)) (fun j => fderiv ℝ χ p (tDir j))
  let z : Fin 4 ⊕ κ → ℂ := Sum.elim (fun i => d (yDir i) p) (fun j => d (tDir j) p)
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    cases i with
    | inl i => exact zero_le_one
    | inr j => exact mul_nonneg hc (sq_nonneg _)
  have h := finite_weighted_cauchy_sq w a z hw
  simpa only [w,a,z,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,one_mul,one_smul,
    mul_smul,← Finset.smul_sum,← Finset.mul_sum,
    cutoffFirstCross,cutoffGradientWeight,firstJetEnergyDensity] using h

theorem cutoff_error_decomposition (c : ℝ) (χ : Space κ → ℝ)
    (f : Lp ℂ 2 (volume : Measure (Space κ)))
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (p : Space κ) :
    cutoffYError χ f d p + (c*‖p.1‖^2) • cutoffTError χ f d p =
      combinedCutoffScalar c χ p • f p + (2 : ℝ) • cutoffFirstCross c χ d p := by
  simp only [cutoffYError,cutoffTError,combinedCutoffScalar,cutoffFirstCross,
    Finset.sum_add_distrib,mul_smul,← Finset.sum_smul,← Finset.smul_sum]
  module

theorem cutoff_error_norm_sq_le {c : ℝ} (hc : 0 ≤ c) (χ : Space κ → ℝ)
    (f : Lp ℂ 2 (volume : Measure (Space κ)))
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (p : Space κ) :
    ‖cutoffYError χ f d p + (c*‖p.1‖^2) • cutoffTError χ f d p‖^2 ≤
      2*|combinedCutoffScalar c χ p|^2*‖f p‖^2 +
        8*cutoffGradientWeight c χ p*firstJetEnergyDensity c d p := by
  rw [cutoff_error_decomposition]
  have h := norm_add_sq_le_twice (combinedCutoffScalar c χ p • f p)
    ((2 : ℝ) • cutoffFirstCross c χ d p)
  have hcross := cutoffFirstCross_norm_sq_le hc χ d p
  have h4 : (2 : ℝ)^2 = 4 := by norm_num
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,h4] at h
  simp only [sq_abs]
  nlinarith

#print axioms cutoffGradientWeight_nonneg
#print axioms firstJetEnergyDensity_nonneg
#print axioms cutoffFirstCross_norm_sq_le
#print axioms cutoff_error_decomposition
#print axioms cutoff_error_norm_sq_le
end TheoremT.Continuum.WeakGrushin
