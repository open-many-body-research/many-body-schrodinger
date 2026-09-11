import GenericCompactDivergenceTests_v1
import GenericFirstCutoffPairing_v1

/-!
A compact-test Laplacian equation with actual L2 plus divergence-of-L2 forcing
is the corresponding tempered-distribution equation. This is the weak H1
bootstrap input; no derivative of the unknown is presumed in this passage.
-/
noncomputable section
open MeasureTheory Filter TemperedDistribution
open scoped SchwartzMap Laplacian LineDeriv ContDiff Topology BigOperators
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem generic_distribution_laplacian_divergence_of_compact_real_tests
    {ι : Type*} [Fintype ι] (f a : Lp ℂ 2 (volume : Measure E))
    (b : ι → Lp ℂ 2 (volume : Measure E)) (v : ι → E)
    (h : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, Δ φ x • f x) = (∫ x, φ x • a x) - ∑ i, ∫ x, fderiv ℝ φ x (v i) • b i x) :
    Δ (f : 𝓢'(E,ℂ)) = (a : 𝓢'(E,ℂ)) + ∑ i, ∂_{v i} (b i : 𝓢'(E,ℂ)) := by
  classical
  ext φ
  let basis := stdOrthonormalBasis ℝ E
  let u (n : ℕ) : E → ℂ := fun x => genericScaledCutoff E ((n : ℝ)+1) x • φ x
  have hu (n : ℕ) : ContDiff ℝ ∞ (u n) := (genericScaledCutoff_contDiff E _).smul φ.smooth'
  have hc (n : ℕ) : HasCompactSupport (u n) := (genericScaledCutoff_compact E (by positivity)).smul_right
  have hd (n : ℕ) (q : E) : ContDiff ℝ ∞ (fun x => fderiv ℝ (u n) x q) :=
    ((hu n).fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hi (n : ℕ) (q : E) : Integrable
      (fun x => fderiv ℝ (fun y => fderiv ℝ (u n) y q) x q * f x) volume :=
    generic_compact_lp_product_integrable f
      (((hd n q).continuous_fderiv (by simp)).clm_apply continuous_const)
      (((hc n).fderiv_apply ℝ q).fderiv_apply ℝ q)
  have heq (n : ℕ) :
      (∑ k, ∫ x, fderiv ℝ (fun y => fderiv ℝ (u n) y (basis k)) x (basis k) * f x) =
      (∫ x, u n x * a x) - ∑ i, ∫ x, fderiv ℝ (u n) x (v i) * b i x := by
    have hh := generic_compact_divergence_complex_test f a b v h (hu n) (hc n)
    simp only [smul_eq_mul] at hh
    rw [← hh]
    simp_rw [generic_compact_laplacian_directional_sum (hu n) (hc n) basis, Finset.sum_mul]
    exact (integral_finset_sum _ (fun k _ => hi n (basis k))).symm
  have hleft := tendsto_finset_sum Finset.univ (fun k _ =>
    generic_schwartz_cutoff_second_pairing_limit φ f (basis k))
  have hright := (generic_schwartz_cutoff_pairing_limit φ a).sub
    (tendsto_finset_sum Finset.univ (fun i _ => generic_schwartz_cutoff_first_pairing_limit φ (b i) (v i)))
  have hright' : Tendsto (fun n : ℕ =>
      ∑ k, ∫ x, fderiv ℝ (fun y => fderiv ℝ (u n) y (basis k)) x (basis k) * f x) atTop
      (𝓝 ((∫ x, φ x*a x) - ∑ i, ∫ x, fderiv ℝ φ x (v i)*b i x)) :=
    hright.congr' (Eventually.of_forall (fun n => (heq n).symm))
  have hlim := tendsto_nhds_unique hleft hright'
  have hD (q : E) : ((∂_{q} φ : 𝓢(E,ℂ)) : E → ℂ) = (fun y => fderiv ℝ φ y q) := by
    funext y; exact SchwartzMap.lineDerivOp_apply_eq_fderiv q φ y
  have hiφ (q : E) : Integrable (fun x => fderiv ℝ (fun y => fderiv ℝ φ y q) x q*f x) volume := by
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv,hD] using
      generic_schwartz_lp_product_integrable (∂_{q} (∂_{q} φ)) f
  have hlap : (∫ x, (Δ φ) x*f x) =
      ∑ k, ∫ x, fderiv ℝ (fun y => fderiv ℝ φ y (basis k)) x (basis k)*f x := by
    rw [SchwartzMap.laplacian_eq_sum basis]
    simp only [SchwartzMap.sum_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv,hD,Finset.sum_mul]
    exact integral_finset_sum _ (fun k _ => hiφ (basis k))
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    TemperedDistribution.laplacian_apply_apply, TemperedDistribution.lineDerivOp_apply_apply,
    Lp.toTemperedDistribution_apply, SchwartzMap.neg_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul, neg_mul, integral_neg]
  simpa only [Finset.sum_neg_distrib, sub_eq_add_neg] using hlap.trans hlim

#print axioms generic_distribution_laplacian_divergence_of_compact_real_tests
end TheoremT.Continuum
