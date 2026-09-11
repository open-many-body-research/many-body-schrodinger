import GenericCompactLaplacianTests_v1
import SecondDirectionalSmul_v1

noncomputable section
open MeasureTheory
open scoped Laplacian ContDiff
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem generic_real_compact_laplacian_continuous_compact
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Continuous (Δ φ) ∧ HasCompactSupport (Δ φ) := by
  have he : Δ φ = fun x => ∑ k, fderiv ℝ
      (fun y => fderiv ℝ φ y (stdOrthonormalBasis ℝ E k)) x (stdOrthonormalBasis ℝ E k) :=
    funext (generic_compact_laplacian_directional_sum hφ hc (stdOrthonormalBasis ℝ E))
  rw [he]
  have hd (v : E) : ContDiff ℝ ∞ (fun y => fderiv ℝ φ y v) :=
    (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  constructor
  · exact continuous_finset_sum _ (fun k _ => ((hd _).continuous_fderiv (by simp)).clm_apply continuous_const)
  · have he2 : (fun x => ∑ k, fderiv ℝ
        (fun y => fderiv ℝ φ y (stdOrthonormalBasis ℝ E k)) x (stdOrthonormalBasis ℝ E k)) =
        ∑ k, (fun x => fderiv ℝ (fun y => fderiv ℝ φ y (stdOrthonormalBasis ℝ E k)) x
          (stdOrthonormalBasis ℝ E k)) := by
      funext x; simp
    rw [he2]
    exact HasCompactSupport.finset_sum
      (fun k _ => (hc.fderiv_apply ℝ (stdOrthonormalBasis ℝ E k)).fderiv_apply ℝ (stdOrthonormalBasis ℝ E k))

theorem generic_compact_laplacian_support_subset
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Function.support (Δ φ) ⊆ tsupport φ := by
  intro x hx
  by_contra hn
  apply hx
  rw [generic_compact_laplacian_directional_sum hφ hc (stdOrthonormalBasis ℝ E)]
  apply Finset.sum_eq_zero
  intro k hk
  apply image_eq_zero_of_notMem_tsupport (f := fun z => fderiv ℝ
    (fun y => fderiv ℝ φ y (stdOrthonormalBasis ℝ E k)) z (stdOrthonormalBasis ℝ E k))
  intro hm
  exact hn ((tsupport_fderiv_apply_subset ℝ (stdOrthonormalBasis ℝ E k))
    ((tsupport_fderiv_apply_subset ℝ (stdOrthonormalBasis ℝ E k)) hm))

theorem generic_compact_laplacian_mul
    {η φ : E → ℝ} (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (x : E) :
    Δ (fun y => η y * φ y) x =
      Δ η x * φ x + 2 * (∑ i, fderiv ℝ η x (b i) * fderiv ℝ φ x (b i)) +
        η x * Δ φ x := by
  rw [generic_compact_laplacian_directional_sum (hη.mul hφ) (hcη.mul_right) b,
    generic_compact_laplacian_directional_sum hη hcη b,
    generic_compact_laplacian_directional_sum hφ hcφ b]
  have he (i : ι) := second_same_directional_smul hη hφ x (b i)
  simp only [smul_eq_mul] at he
  simp_rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, mul_assoc,
    ← Finset.mul_sum]

#print axioms generic_real_compact_laplacian_continuous_compact
#print axioms generic_compact_laplacian_support_subset
#print axioms generic_compact_laplacian_mul
end TheoremT.Continuum
