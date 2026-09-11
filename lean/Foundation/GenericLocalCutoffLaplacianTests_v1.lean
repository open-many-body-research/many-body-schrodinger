import GenericCutoffLaplacianDivergenceTests_v1
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! The first local elliptic bootstrap only requires L² on the actual compact
cutoff support. Functions outside this support are not assumed integrable.
The functions appearing below are actual measurable indicator extensions. -/
noncomputable section
open MeasureTheory Filter
open scoped Laplacian ContDiff
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def genericIndicatorL2 (S : Set E) (hS : MeasurableSet S) (f : E → ℂ)
    (hf : MemLp f 2 (volume.restrict S)) : Lp ℂ 2 (volume : Measure E) :=
  ((memLp_indicator_iff_restrict hS).mpr hf).toLp (S.indicator f)

theorem genericIndicatorL2_smul_ae
    (S : Set E) (hS : MeasurableSet S) (f : E → ℂ)
    (hf : MemLp f 2 (volume.restrict S)) (θ : E → ℝ)
    (hsθ : Function.support θ ⊆ S) :
    (fun x => θ x • genericIndicatorL2 S hS f hf x) =ᵐ[volume]
      (fun x => θ x • f x) := by
  have he : genericIndicatorL2 S hS f hf =ᵐ[volume] S.indicator f :=
    MemLp.coeFn_toLp _
  filter_upwards [he] with x hx
  rw [hx]
  by_cases hm : x ∈ S
  · rw [Set.indicator_of_mem hm]
  · have hz : θ x = 0 := by
      by_contra hn
      exact hm (hsθ hn)
    simp [hz]

theorem genericIndicatorL2_test
    (S : Set E) (hS : MeasurableSet S) (f : E → ℂ)
    (hf : MemLp f 2 (volume.restrict S)) (θ : E → ℝ)
    (hsθ : Function.support θ ⊆ S) :
    (∫ x, θ x • genericIndicatorL2 S hS f hf x) = ∫ x, θ x • f x :=
  integral_congr_ae (genericIndicatorL2_smul_ae S hS f hf θ hsθ)

theorem generic_local_cutoff_laplacian_divergence_tests
    {Ω : Set E} (f w : E → ℂ)
    (h : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x, Δ φ x • f x) = ∫ x, φ x • w x)
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ Ω)
    (hf : MemLp f 2 (volume.restrict (tsupport χ)))
    (hw : MemLp w 2 (volume.restrict (tsupport χ)))
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    ∃ U A : Lp ℂ 2 (volume : Measure E), ∃ B : ι → Lp ℂ 2 (volume : Measure E),
      U =ᵐ[volume] (fun x => χ x • f x) ∧
      A =ᵐ[volume] (fun x => χ x • w x - Δ χ x • f x) ∧
      (∀ i, B i =ᵐ[volume] (fun x => (2 * fderiv ℝ χ x (b i)) • f x)) ∧
      ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        (∫ x, Δ φ x • U x) =
          (∫ x, φ x • A x) - ∑ i, ∫ x, fderiv ℝ φ x (b i) • B i x := by
  have hK : MeasurableSet (tsupport χ) := (isClosed_tsupport χ).measurableSet
  let F := genericIndicatorL2 (tsupport χ) hK f hf
  let W := genericIndicatorL2 (tsupport χ) hK w hw
  have hFW : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ tsupport χ →
      (∫ x, Δ φ x • F x) = ∫ x, φ x • W x := by
    intro φ hφ hcφ hsφ
    rw [genericIndicatorL2_test _ hK f hf (Δ φ)
      ((generic_compact_laplacian_support_subset hφ hcφ).trans hsφ),
      genericIndicatorL2_test _ hK w hw φ ((subset_tsupport φ).trans hsφ)]
    exact h φ hφ hcφ (hsφ.trans hsχ)
  obtain ⟨U,A,B,hU,hA,hB,ht⟩ := generic_cutoff_laplacian_divergence_test_witnesses
    F W hFW hχ hcχ (Set.Subset.refl _) b
  have hχF := genericIndicatorL2_smul_ae _ hK f hf χ (subset_tsupport χ)
  have hχW := genericIndicatorL2_smul_ae _ hK w hw χ (subset_tsupport χ)
  have hΔF := genericIndicatorL2_smul_ae _ hK f hf (Δ χ)
    (generic_compact_laplacian_support_subset hχ hcχ)
  refine ⟨U,A,B,hU.trans hχF,?_,?_,ht⟩
  · filter_upwards [hA,hχW,hΔF] with x hx hwx hfx
    exact hx.trans (congrArg₂ (fun z t : ℂ => z-t) hwx hfx)
  · intro i
    have hd : Function.support (fun x => 2 * fderiv ℝ χ x (b i)) ⊆ tsupport χ := by
      intro x hx
      apply tsupport_fderiv_apply_subset ℝ (b i)
      apply subset_tsupport (fun z => fderiv ℝ χ z (b i))
      intro hz
      exact hx (by simp [hz])
    exact (hB i).trans (genericIndicatorL2_smul_ae _ hK f hf _ hd)

#print axioms genericIndicatorL2_smul_ae
#print axioms genericIndicatorL2_test
#print axioms generic_local_cutoff_laplacian_divergence_tests
end TheoremT.Continuum
