import LocalProductDirectionalWeakUnique_v1
import ProductLocalEllipticH2_v1

/-! Genuine local first and same-coordinate second weak jets imply local H2.
This is a qualitative reconstruction from the actual full Laplacian test
identity. It neither assumes mixed derivatives nor a derivative norm bound. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
namespace TheoremT.Continuum
variable {Y T ι κ : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T] [Fintype ι] [Fintype κ]

theorem ProductLocalWeakDirectional.second_same_test
    {Ω : Set (Y × T)} {f d e : Y × T → ℂ} {v : Y × T}
    (hd : ProductLocalWeakDirectional Ω f d v)
    (he : ProductLocalWeakDirectional Ω d e v)
    {φ : Y × T → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Ω) :
    (∫ p, fderiv ℝ (fun q => fderiv ℝ φ q v) p v • f p) = ∫ p, φ p • e p := by
  have hD : ContDiff ℝ ∞ (fun p => fderiv ℝ φ p v) :=
    (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  rw [he.2.2 φ hφ hcφ hsφ,hd.2.2 _ hD (hcφ.fderiv_apply ℝ v)
    ((tsupport_fderiv_apply_subset ℝ v).trans hsφ),neg_neg]

theorem product_local_weakH2_of_diagonal_jets
    (bY : OrthonormalBasis ι ℝ Y) (bT : OrthonormalBasis κ ℝ T)
    {Ω : Set (Y × T)} (hΩ : IsOpen Ω) (f : Y × T → ℂ)
    (dY eY : ι → Y × T → ℂ) (dT eT : κ → Y × T → ℂ)
    (hf : ProductLocallyL2On f Ω)
    (hY : ∀ i, ProductLocalWeakDirectional Ω f (dY i) (bY i,0))
    (hYY : ∀ i, ProductLocalWeakDirectional Ω (dY i) (eY i) (bY i,0))
    (hT : ∀ j, ProductLocalWeakDirectional Ω f (dT j) (0,bT j))
    (hTT : ∀ j, ProductLocalWeakDirectional Ω (dT j) (eT j) (0,bT j)) :
    ProductLocalWeakH2On f Ω := by
  let w : Y × T → ℂ := fun p => (∑ i,eY i p)+(∑ j,eT j p)
  have hw : ProductLocallyL2On w Ω := by
    intro K hK hs
    exact (memLp_finsetSum _ (fun i _ => (hYY i).2.1 K hK hs)).add
      (memLp_finsetSum _ (fun j _ => (hTT j).2.1 K hK hs))
  apply product_local_elliptic_h2_on bY bT hΩ f w hf hw
  intro φ hφ hcφ hsφ
  have hiY (i : ι) : Integrable (fun p =>
      fderiv ℝ (fun q => fderiv ℝ φ q (bY i,0)) p (bY i,0) • f p) := by
    apply product_raw_locallyL2_compact_smul_integrable hf
    · exact (((hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply
        contDiff_const).continuous_fderiv (by simp)).clm_apply continuous_const
    · exact (hcφ.fderiv_apply ℝ (bY i,0)).fderiv_apply ℝ (bY i,0)
    · exact (tsupport_fderiv_apply_subset ℝ (bY i,0)).trans
        ((tsupport_fderiv_apply_subset ℝ (bY i,0)).trans hsφ)
  have hiT (j : κ) : Integrable (fun p =>
      fderiv ℝ (fun q => fderiv ℝ φ q (0,bT j)) p (0,bT j) • f p) := by
    apply product_raw_locallyL2_compact_smul_integrable hf
    · exact (((hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply
        contDiff_const).continuous_fderiv (by simp)).clm_apply continuous_const
    · exact (hcφ.fderiv_apply ℝ (0,bT j)).fderiv_apply ℝ (0,bT j)
    · exact (tsupport_fderiv_apply_subset ℝ (0,bT j)).trans
        ((tsupport_fderiv_apply_subset ℝ (0,bT j)).trans hsφ)
  have ieY (i : ι) := ((hYY i).test_integrable hφ hcφ hsφ).1
  have ieT (j : κ) := ((hTT j).test_integrable hφ hcφ hsφ).1
  simp only [productFactorLaplacian,w,add_smul,Finset.sum_smul,smul_add,Finset.smul_sum]
  rw [integral_add (integrable_finset_sum _ (fun i _ => hiY i))
      (integrable_finset_sum _ (fun j _ => hiT j)),
    integral_add (integrable_finset_sum _ (fun i _ => ieY i))
      (integrable_finset_sum _ (fun j _ => ieT j)),
    integral_finset_sum _ (fun i _ => hiY i),integral_finset_sum _ (fun j _ => hiT j),
    integral_finset_sum _ (fun i _ => ieY i),integral_finset_sum _ (fun j _ => ieT j)]
  congr 1
  · exact Finset.sum_congr rfl (fun i _ => (hY i).second_same_test (hYY i) hφ hcφ hsφ)
  · exact Finset.sum_congr rfl (fun j _ => (hT j).second_same_test (hTT j) hφ hcφ hsφ)

end TheoremT.Continuum
