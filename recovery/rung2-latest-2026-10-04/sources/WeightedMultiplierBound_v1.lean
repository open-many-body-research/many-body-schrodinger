import CoulombWeightedEigenIdentity_v1

/-! Convert a pointwise bound on a real weight's squared gradient into an
actual weighted eigenfunction norm estimate on an exterior coercive region. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
namespace TheoremT.Continuum

theorem integrable_boundedRealMul_norm_sq_integrand {N : ℕ}
    (χ : Configuration N → ℝ) (hm : MemLp χ ⊤ volume) (f : SpatialL2 N) :
    Integrable (fun x => (χ x)^2 * ‖f x‖^2) volume := by
  have hmem : MemLp (fun x => χ x • f x) 2 volume := (Lp.memLp f).smul hm
  simpa only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] using
    (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem

theorem weighted_gradient_integral_bound {N : ℕ} (f : SpatialL2 N)
    (χ : Configuration N → ℝ) (hm : MemLp χ ⊤ volume)
    (hdm : ∀ k : Coordinate N,
      MemLp (fun x => fderiv ℝ χ x (coordinateVector k)) ⊤ volume)
    (A B : ℝ)
    (hbound : ∀ x, (1/2 : ℝ) * (∑ k : Coordinate N,
      (fderiv ℝ χ x (coordinateVector k))^2) ≤ A*(χ x)^2 + B) :
    (1/2 : ℝ) * (∑ k : Coordinate N,
      ‖boundedRealMul (fun x => fderiv ℝ χ x (coordinateVector k)) (hdm k) f‖^2) ≤
      A * ‖boundedRealMul χ hm f‖^2 + B*‖f‖^2 := by
  have hi (k : Coordinate N) := integrable_boundedRealMul_norm_sq_integrand
    (fun x => fderiv ℝ χ x (coordinateVector k)) (hdm k) f
  have hiχ := integrable_boundedRealMul_norm_sq_integrand χ hm f
  have hif := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hleft := (integrable_finsetSum Finset.univ (fun k _ => hi k)).const_mul (1/2 : ℝ)
  have hright := (hiχ.const_mul A).add (hif.const_mul B)
  have h := integral_mono_ae hleft hright (Eventually.of_forall (fun x => ?_))
  · simp only [Pi.add_apply] at h
    simp only [integral_const_mul,integral_add (hiχ.const_mul A) (hif.const_mul B),
      integral_finsetSum Finset.univ (fun k _ => hi k)] at h
    simp_rw [boundedRealMul_norm_sq_integral]
    rw [spatialL2_norm_sq_integral f]
    exact h
  · have h := mul_le_mul_of_nonneg_right (hbound x) (sq_nonneg ‖f x‖)
    change (1/2 : ℝ) * (∑ k : Coordinate N,
      (fderiv ℝ χ x (coordinateVector k))^2 * ‖f x‖^2) ≤
      A*((χ x)^2*‖f x‖^2)+B*‖f x‖^2
    rw [← Finset.sum_mul]
    nlinarith

theorem scalar_eigen_weighted_exterior_bound {N : ℕ} {Z E R δ : ℝ} {f : SpatialL2 N}
    (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    (hcoerc : ∀ (v : SpatialL2 N) (q : ℝ), scalarCoulombH1FormValue N Z v q →
      (∀ᵐ x, ‖x‖ ≤ R → v x = 0) → δ*‖v‖^2 ≤ q-E*‖v‖^2)
    (χ : Configuration N → ℝ) (hχ : ContDiff ℝ ∞ χ) (hm : MemLp χ ⊤ volume)
    (hdm : ∀ k : Coordinate N,
      MemLp (fun x => fderiv ℝ χ x (coordinateVector k)) ⊤ volume)
    (hzero : ∀ x, ‖x‖ ≤ R → χ x = 0) (A B : ℝ)
    (hbound : ∀ x, (1/2 : ℝ) * (∑ k : Coordinate N,
      (fderiv ℝ χ x (coordinateVector k))^2) ≤ A*(χ x)^2+B) :
    (δ-A) * ‖boundedRealMul χ hm f‖^2 ≤ B*‖f‖^2 := by
  have hv : ∀ᵐ x, ‖x‖ ≤ R → boundedRealMul χ hm f x = 0 := by
    filter_upwards [boundedRealMul_ae χ hm f] with x hx
    intro hr
    rw [hx,hzero x hr,zero_smul]
  have hc := hcoerc _ _ (scalar_eigen_weighted_form_value hg χ hχ hm hdm) hv
  have hi := weighted_gradient_integral_bound f χ hm hdm A B hbound
  linarith

#print axioms weighted_gradient_integral_bound
#print axioms scalar_eigen_weighted_exterior_bound
end TheoremT.Continuum
