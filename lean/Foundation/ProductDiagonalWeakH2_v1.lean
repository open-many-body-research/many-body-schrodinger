import ProductCompactLaplacianConverse_v2
import WeakProductSecondTest_v1

/-! Genuine first and same-coordinate second L2 derivatives in the two factor
orthonormal bases imply all genuine ordered weak H2 derivatives on the actual
ordinary product. Mixed derivatives are constructed by the verified Fourier
Laplacian gain, not assumed. This is an existence theorem, not an algorithm. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
namespace TheoremT.Continuum
variable {Y T ι κ I : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]
  [Fintype ι] [Fintype κ] [Fintype I]

theorem product_finite_diagonal_trace_test
    {f : Lp ℂ 2 (volume : Measure (Y × T))}
    (v : I → Y × T) (d e : I → Lp ℂ 2 (volume : Measure (Y × T)))
    (hd : ∀ i, WeakProductL2Directional f (d i) (v i))
    (he : ∀ i, WeakProductL2Directional (d i) (e i) (v i))
    {φ : Y × T → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) :
    (∫ p, φ p • (∑ i, e i) p) =
      ∫ p, (∑ i, fderiv ℝ (fun q => fderiv ℝ φ q (v i)) p (v i)) • f p := by
  classical
  have ie (i : I) : Integrable (fun p => φ p • e i p) :=
    ((Lp.memLp (e i)).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      hφ.continuous hcφ
  have hD (i : I) : ContDiff ℝ ∞ (fun p => fderiv ℝ φ p (v i)) :=
    (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have id (i : I) : Integrable
      (fun p => fderiv ℝ (fun q => fderiv ℝ φ q (v i)) p (v i) • f p) :=
    ((Lp.memLp f).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      (((hD i).continuous_fderiv (by simp)).clm_apply continuous_const)
      ((hcφ.fderiv_apply ℝ (v i)).fderiv_apply ℝ (v i))
  calc
    _ = ∫ p, ∑ i, φ p • e i p := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ e] with p hp
      rw [hp,Finset.smul_sum]
    _ = ∑ i, ∫ p, φ p • e i p := integral_finsetSum _ (fun i _ => ie i)
    _ = ∑ i, ∫ p, fderiv ℝ (fun q => fderiv ℝ φ q (v i)) p (v i) • f p := by
      apply Finset.sum_congr rfl
      intro i _
      exact weakProduct_second_same_test (hd i) (he i) hφ hcφ
    _ = ∫ p, ∑ i, fderiv ℝ (fun q => fderiv ℝ φ q (v i)) p (v i) • f p :=
      (integral_finsetSum _ (fun i _ => id i)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with p
      rw [Finset.sum_smul]

def productBasisDirection (bY : OrthonormalBasis ι ℝ Y) (bT : OrthonormalBasis κ ℝ T) :
    ι ⊕ κ → Y × T := Sum.elim (fun i => (bY i,0)) (fun j => (0,bT j))

theorem product_coordinate_diagonal_laplacian_test
    (bY : OrthonormalBasis ι ℝ Y) (bT : OrthonormalBasis κ ℝ T)
    {f : Lp ℂ 2 (volume : Measure (Y × T))}
    (d e : ι ⊕ κ → Lp ℂ 2 (volume : Measure (Y × T)))
    (hd : ∀ i, WeakProductL2Directional f (d i) (productBasisDirection bY bT i))
    (he : ∀ i, WeakProductL2Directional (d i) (e i) (productBasisDirection bY bT i))
    {φ : Y × T → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) :
    (∫ p, φ p • (∑ i, e i) p) = ∫ p, productFactorLaplacian bY bT φ p • f p := by
  simpa only [Fintype.sum_sum_type,productBasisDirection,Sum.elim_inl,Sum.elim_inr,
    productFactorLaplacian] using product_finite_diagonal_trace_test
      (productBasisDirection bY bT) d e hd he hφ hcφ

theorem product_weakH2_of_coordinate_diagonal_jets
    (bY : OrthonormalBasis ι ℝ Y) (bT : OrthonormalBasis κ ℝ T)
    {f : Lp ℂ 2 (volume : Measure (Y × T))}
    (d e : ι ⊕ κ → Lp ℂ 2 (volume : Measure (Y × T)))
    (hd : ∀ i, WeakProductL2Directional f (d i) (productBasisDirection bY bT i))
    (he : ∀ i, WeakProductL2Directional (d i) (e i) (productBasisDirection bY bT i)) :
    ∃ a : (Y × T) → Lp ℂ 2 (volume : Measure (Y × T)),
    ∃ b : (Y × T) → (Y × T) → Lp ℂ 2 (volume : Measure (Y × T)),
      (∀ v, WeakProductL2Directional f (a v) v) ∧
      ∀ v w, WeakProductL2Directional (a v) (b v w) w := by
  obtain ⟨a,ha,hb⟩ := product_weak_second_jets_of_compact_factor_laplacian_tests bY bT f
    (∑ i, e i) (fun φ hφ hcφ => product_coordinate_diagonal_laplacian_test bY bT d e hd he hφ hcφ)
  choose b hb using hb
  exact ⟨a,b,ha,hb⟩

end TheoremT.Continuum
