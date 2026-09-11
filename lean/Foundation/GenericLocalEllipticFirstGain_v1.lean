import GenericLocalCutoffLaplacianTests_v1
import GenericDistributionDivergenceConverse_v1
import GenericNegativeSobolevGain_v1

/-! Genuine first local elliptic gain from L² data. The inputs are a compact-test
equation Δf=w near a smooth compact cutoff and L² on that cutoff's support.
The output is the actual cutoff function in L², with its exact distribution
Laplacian in divergence form and actual weak first derivatives in all directions.
No input weak derivative, differentiability, or Sobolev density is assumed.
The subsequent nested-cutoff H² gain is a separate theorem. -/
noncomputable section
open MeasureTheory Filter TemperedDistribution
open scoped Laplacian LineDeriv SchwartzMap ContDiff
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem generic_local_cutoff_laplacian_distribution
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
      Δ (U : 𝓢'(E, ℂ)) = (A : 𝓢'(E, ℂ)) +
        ∑ i, ∂_{b i} (B i : 𝓢'(E, ℂ)) := by
  obtain ⟨U,A,B,hU,hA,hB,ht⟩ := generic_local_cutoff_laplacian_divergence_tests
    f w h hχ hcχ hsχ hf hw b
  exact ⟨U,A,B,hU,hA,hB,
    generic_distribution_laplacian_divergence_of_compact_real_tests U A B b ht⟩

theorem generic_local_elliptic_first_gain
    {Ω : Set E} (f w : E → ℂ)
    (h : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x, Δ φ x • f x) = ∫ x, φ x • w x)
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ Ω)
    (hf : MemLp f 2 (volume.restrict (tsupport χ)))
    (hw : MemLp w 2 (volume.restrict (tsupport χ))) :
    ∃ U : Lp ℂ 2 (volume : Measure E), ∃ d : E → Lp ℂ 2 (volume : Measure E),
      U =ᵐ[volume] (fun x => χ x • f x) ∧ ∀ v, WeakL2Directional U (d v) v := by
  obtain ⟨U,A,B,hU,_,_,hΔ⟩ := generic_local_cutoff_laplacian_distribution
    f w h hχ hcχ hsχ hf hw (stdOrthonormalBasis ℝ E)
  obtain ⟨d,hd⟩ := weakL2_first_jets_of_l2_laplacian_divergence
    (stdOrthonormalBasis ℝ E) U A B hΔ
  exact ⟨U,d,hU,hd⟩

#print axioms generic_local_cutoff_laplacian_distribution
#print axioms generic_local_elliptic_first_gain
end TheoremT.Continuum
