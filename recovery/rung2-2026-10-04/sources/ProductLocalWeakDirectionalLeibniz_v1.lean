import WeakGrushinPotentialDerivativeTest_v1
import WeakGrushinPotentialDerivativeLocalL2_v1
import GrushinLocalPotentialL2_v1
import GrushinLocalL2Extension_v1

/-! A genuine local weak directional product rule for raw locally L2 data.
No global representative, global derivative, or H2 assumption is required.
The direction is arbitrary in the ordinary finite-dimensional product space.
All test integrals are proved integrable using compact restrictions. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology
namespace TheoremT.Continuum
variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

theorem product_raw_locallyL2_compact_smul_integrable
    {Ω : Set (Y × T)} {f : Y × T → ℂ}
    (hf : ProductLocallyL2On f Ω) {θ : Y × T → ℝ}
    (hθ : Continuous θ) (hcθ : HasCompactSupport θ) (hsθ : tsupport θ ⊆ Ω) :
    Integrable (fun p => θ p • f p) volume := by
  let G := restrictedL2Extension (tsupport θ) hcθ.measurableSet f (hf _ hcθ hsθ)
  have hi : Integrable (fun p => θ p • G p) volume :=
    ((Lp.memLp G).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport hθ hcθ
  apply hi.congr
  filter_upwards [restrictedL2Extension_ae_on (tsupport θ) hcθ.measurableSet f
    (hf _ hcθ hsθ)] with p hp
  by_cases hmem : p ∈ tsupport θ
  · rw [show G p = f p from hp hmem]
  · simp only [image_eq_zero_of_notMem_tsupport hmem, zero_smul]

theorem product_smooth_coefficient_locallyL2_raw
    {Ω : Set (Y × T)} (_hΩ : IsOpen Ω) {B : Y × T → ℝ}
    (hB : ContDiffOn ℝ ∞ B Ω) {f : Y × T → ℂ}
    (hf : ProductLocallyL2On f Ω) :
    ProductLocallyL2On (fun p => B p • f p) Ω :=
  product_locallyL2On_smul_of_continuousOn hB.continuousOn hf

theorem product_local_directional_leibniz_locallyL2_raw
    {Ω : Set (Y × T)} (hΩ : IsOpen Ω) {B : Y × T → ℝ}
    (hB : ContDiffOn ℝ ∞ B Ω) {f d : Y × T → ℂ}
    (hf : ProductLocallyL2On f Ω) (hd : ProductLocallyL2On d Ω) (v : Y × T) :
    ProductLocallyL2On (fun p => B p • d p + fderiv ℝ B p v • f p) Ω := by
  intro K hK hKΩ
  obtain ⟨hmB,hmD⟩ := smooth_coefficient_and_directional_memLp_top_restrict_compact
    (μ := volume) hΩ hK hKΩ hB v
  exact ((hd K hK hKΩ).smul hmB).add ((hf K hK hKΩ).smul hmD)

theorem product_local_weak_directional_potential_test
    {Ω : Set (Y × T)} (hΩ : IsOpen Ω) {B : Y × T → ℝ}
    (hB : ContDiffOn ℝ ∞ B Ω) {f d : Y × T → ℂ} {v : Y × T}
    (hf : ProductLocallyL2On f Ω) (hd : ProductLocallyL2On d Ω)
    (hD : ∀ ψ : Y × T → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω → (∫ p, ψ p • d p) = -(∫ p, fderiv ℝ ψ p v • f p))
    {φ : Y × T → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ω) :
    Integrable (fun p => φ p • (B p • d p + fderiv ℝ B p v • f p)) volume ∧
    Integrable (fun p => fderiv ℝ φ p v • (B p • f p)) volume ∧
    (∫ p, φ p • (B p • d p + fderiv ℝ B p v • f p)) =
      -(∫ p, fderiv ℝ φ p v • (B p • f p)) := by
  have hBon (p : Y × T) (hp : p ∈ Ω) : ContDiffAt ℝ ∞ B p :=
    hB.contDiffAt (hΩ.mem_nhds hp)
  have hφB : ContDiff ℝ ∞ (fun p => φ p * B p) :=
    smooth_mul_of_smooth_on_tsupport hφ (fun p hp => hBon p (hs hp))
  have hφDB : ContDiff ℝ ∞ (fun p => φ p * fderiv ℝ B p v) :=
    smooth_mul_of_smooth_on_tsupport hφ
      (fun p hp => local_contDiffAt_directional_derivative (hBon p (hs hp)) v)
  have hDφ : ContDiff ℝ ∞ (fun p => fderiv ℝ φ p v) :=
    (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hDφB : ContDiff ℝ ∞ (fun p => fderiv ℝ φ p v * B p) :=
    smooth_mul_of_smooth_on_tsupport hDφ
      (fun p hp => hBon p (hs (tsupport_fderiv_apply_subset ℝ v hp)))
  have h1 : Integrable (fun p => (φ p * B p) • d p) volume :=
    product_raw_locallyL2_compact_smul_integrable hd hφB.continuous hc.mul_right
      (tsupport_mul_subset_left.trans hs)
  have h2 : Integrable (fun p => (φ p * fderiv ℝ B p v) • f p) volume :=
    product_raw_locallyL2_compact_smul_integrable hf hφDB.continuous hc.mul_right
      (tsupport_mul_subset_left.trans hs)
  have h3 : Integrable (fun p => (fderiv ℝ φ p v * B p) • f p) volume :=
    product_raw_locallyL2_compact_smul_integrable hf hDφB.continuous
      (hc.fderiv_apply ℝ v).mul_right
      (tsupport_mul_subset_left.trans ((tsupport_fderiv_apply_subset ℝ v).trans hs))
  have hw := hD (fun p => φ p * B p) hφB hc.mul_right
    (tsupport_mul_subset_left.trans hs)
  have he : (∫ p, fderiv ℝ (fun q => φ q * B q) p v • f p) =
      (∫ p, (φ p * fderiv ℝ B p v) • f p) +
      (∫ p, (fderiv ℝ φ p v * B p) • f p) := by
    simp_rw [local_potential_test_fderiv_product hΩ hB hφ hs, add_smul]
    exact integral_add h2 h3
  rw [he] at hw
  refine ⟨?_,?_,?_⟩
  · simp only [smul_add, ← mul_smul]
    exact h1.fun_add h2
  · simpa only [← mul_smul] using h3
  · simp only [smul_add, ← mul_smul]
    rw [integral_add h1 h2, hw]
    abel

theorem product_local_weak_directional_leibniz
    {Ω : Set (Y × T)} (hΩ : IsOpen Ω) {B : Y × T → ℝ}
    (hB : ContDiffOn ℝ ∞ B Ω) {f d : Y × T → ℂ} {v : Y × T}
    (hf : ProductLocallyL2On f Ω) (hd : ProductLocallyL2On d Ω)
    (hD : ∀ ψ : Y × T → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω → (∫ p, ψ p • d p) = -(∫ p, fderiv ℝ ψ p v • f p)) :
    ProductLocallyL2On (fun p => B p • f p) Ω ∧
    ProductLocallyL2On (fun p => B p • d p + fderiv ℝ B p v • f p) Ω ∧
    ∀ φ : Y × T → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      Integrable (fun p => φ p • (B p • d p + fderiv ℝ B p v • f p)) volume ∧
      Integrable (fun p => fderiv ℝ φ p v • (B p • f p)) volume ∧
      (∫ p, φ p • (B p • d p + fderiv ℝ B p v • f p)) =
        -(∫ p, fderiv ℝ φ p v • (B p • f p)) := by
  refine ⟨product_smooth_coefficient_locallyL2_raw hΩ hB hf,
    product_local_directional_leibniz_locallyL2_raw hΩ hB hf hd v, ?_⟩
  intro φ hφ hc hs
  exact product_local_weak_directional_potential_test hΩ hB hf hd hD hφ hc hs

#print axioms product_raw_locallyL2_compact_smul_integrable
#print axioms product_smooth_coefficient_locallyL2_raw
#print axioms product_local_directional_leibniz_locallyL2_raw
#print axioms product_local_weak_directional_potential_test
#print axioms product_local_weak_directional_leibniz
end TheoremT.Continuum
