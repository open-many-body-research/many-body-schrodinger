import GenericCompactLaplacianTests_v1
import GenericSchwartzCutoffPairing_v1

/-!
Compact real test identities imply the actual tempered-distribution Laplacian
equation on an arbitrary finite-dimensional real inner-product space. The
compact-to-Schwartz passage is proved by scaled cutoffs and L2 pairings;
no elliptic regularity, derivative witnesses, or test-density premise is assumed.
-/
noncomputable section
open MeasureTheory Filter TemperedDistribution
open scoped SchwartzMap Laplacian LineDeriv ContDiff Topology BigOperators
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem generic_distribution_laplacian_of_compact_real_tests
    (f w : Lp ℂ 2 (volume : Measure E))
    (h : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, φ x • w x) = ∫ x, Δ φ x • f x) :
    Δ (f : 𝓢'(E,ℂ)) = (w : 𝓢'(E,ℂ)) := by
  classical
  ext φ
  let b := stdOrthonormalBasis ℝ E
  let u (n : ℕ) : E → ℂ := fun x => genericScaledCutoff E ((n : ℝ)+1) x • φ x
  have hu (n : ℕ) : ContDiff ℝ ∞ (u n) := (genericScaledCutoff_contDiff E _).smul φ.smooth'
  have hc (n : ℕ) : HasCompactSupport (u n) := (genericScaledCutoff_compact E (by positivity)).smul_right
  have hd (n : ℕ) (v : E) : ContDiff ℝ ∞ (fun x => fderiv ℝ (u n) x v) :=
    ((hu n).fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hi (n : ℕ) (v : E) : Integrable
      (fun x => fderiv ℝ (fun y => fderiv ℝ (u n) y v) x v * f x) volume :=
    generic_compact_lp_product_integrable f
      (((hd n v).continuous_fderiv (by simp)).clm_apply continuous_const)
      (((hc n).fderiv_apply ℝ v).fderiv_apply ℝ v)
  have heq (n : ℕ) : (∫ x, u n x * w x) =
      ∑ k, ∫ x, fderiv ℝ (fun y => fderiv ℝ (u n) y (b k)) x (b k) * f x := by
    have hh := generic_compact_laplacian_complex_test f w h (hu n) (hc n)
    simp only [smul_eq_mul] at hh
    rw [hh]
    simp_rw [generic_compact_laplacian_directional_sum (hu n) (hc n) b, Finset.sum_mul]
    exact integral_finset_sum _ (fun k _ => hi n (b k))
  have hleft := generic_schwartz_cutoff_pairing_limit φ w
  have hright := tendsto_finset_sum Finset.univ (fun k _ =>
    generic_schwartz_cutoff_second_pairing_limit φ f (b k))
  have hright' : Tendsto (fun n : ℕ => ∫ x, u n x*w x) atTop
      (𝓝 (∑ k, ∫ x, fderiv ℝ (fun y => fderiv ℝ φ y (b k)) x (b k)*f x)) :=
    hright.congr' (Eventually.of_forall (fun n => (heq n).symm))
  have hlim := tendsto_nhds_unique hleft hright'
  have hD (v : E) : ((∂_{v} φ : 𝓢(E,ℂ)) : E → ℂ) = (fun y => fderiv ℝ φ y v) := by
    funext y; exact SchwartzMap.lineDerivOp_apply_eq_fderiv v φ y
  have hiφ (v : E) : Integrable (fun x => fderiv ℝ (fun y => fderiv ℝ φ y v) x v*f x) volume := by
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv,hD] using
      generic_schwartz_lp_product_integrable (∂_{v} (∂_{v} φ)) f
  have hlap : (∫ x, (Δ φ) x*f x) =
      ∑ k, ∫ x, fderiv ℝ (fun y => fderiv ℝ φ y (b k)) x (b k)*f x := by
    rw [SchwartzMap.laplacian_eq_sum b]
    simp only [SchwartzMap.sum_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv,hD,Finset.sum_mul]
    exact integral_finset_sum _ (fun k _ => hiφ (b k))
  rw [TemperedDistribution.laplacian_apply_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  simp only [smul_eq_mul]
  exact hlap.trans hlim.symm

theorem generic_weak_second_jets_of_compact_laplacian_tests
    (f w : Lp ℂ 2 (volume : Measure E))
    (h : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, φ x • w x) = ∫ x, Δ φ x • f x) :
    ∃ d : E → Lp ℂ 2 (volume : Measure E),
      (∀ v, WeakL2Directional f (d v) v) ∧
      ∀ v q : E, ∃ e : Lp ℂ 2 (volume : Measure E), WeakL2Directional (d v) e q :=
  exists_weakL2_first_and_second_jets_of_distribution_laplacian f w
    (generic_distribution_laplacian_of_compact_real_tests f w h)

#print axioms generic_distribution_laplacian_of_compact_real_tests
#print axioms generic_weak_second_jets_of_compact_laplacian_tests
end TheoremT.Continuum
