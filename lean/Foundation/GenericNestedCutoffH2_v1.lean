import GenericH1MultiplierDivergenceGain_v1
import GenericLocalEllipticFirstGain_v1

/-! Two-cutoff local H2 gain. First derivatives of the input are derived from
its local L2 Laplacian; the inner cutoff then has an actual L2 Laplacian.
The supplied plateau cutoffs and local integrability are geometric/data
hypotheses, not assumptions of the desired weak derivatives. -/
noncomputable section
open MeasureTheory Filter TemperedDistribution
open scoped Laplacian LineDeriv SchwartzMap ContDiff
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem generic_nested_cutoff_h2
    {Ω : Set E} (f w : E → ℂ)
    (h : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x, Δ φ x • f x) = ∫ x, φ x • w x)
    {η χ : E → ℝ} (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ Ω)
    (hf : MemLp f 2 (volume.restrict (tsupport η)))
    (hw : MemLp w 2 (volume.restrict (tsupport η)))
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hplateau : ∀ x ∈ tsupport χ, η x = 1) :
    ∃ U : Lp ℂ 2 (volume : Measure E),
      U =ᵐ[volume] (fun x => χ x • f x) ∧ HasWeakL2Order U 2 := by
  have hsub : tsupport χ ⊆ tsupport η := by
    intro x hx
    apply subset_tsupport η
    rw [Function.mem_support,hplateau x hx]
    norm_num
  have hfχ : MemLp f 2 (volume.restrict (tsupport χ)) :=
    hf.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hwχ : MemLp w 2 (volume.restrict (tsupport χ)) :=
    hw.mono_measure (Measure.restrict_mono hsub le_rfl)
  obtain ⟨F,d,hF,hd⟩ := generic_local_elliptic_first_gain
    f w h hη hcη hsη hf hw
  let b := stdOrthonormalBasis ℝ E
  obtain ⟨U,A,B,hU,_,hB,hΔ⟩ := generic_local_cutoff_laplacian_distribution
    f w h hχ hcχ (hsub.trans hsη) hfχ hwχ b
  let θ := fun i x => 2 * fderiv ℝ χ x (b i)
  have hθ (i) : ContDiff ℝ ∞ (θ i) :=
    contDiff_const.mul ((hχ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const)
  have hcθ (i) : HasCompactSupport (θ i) := (hcχ.fderiv_apply ℝ (b i)).mul_left
  have hm (i) : MemLp (θ i) ⊤ volume :=
    (hθ i).continuous.memLp_top_of_hasCompactSupport (hcθ i) volume
  have hDm (i) : MemLp (fun x => fderiv ℝ (θ i) x (b i)) ⊤ volume :=
    (((hθ i).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      ((hcθ i).fderiv_apply ℝ (b i)) volume
  have hb (i) : B i = genericBoundedRealMul (θ i) (hm i) F := by
    apply Lp.ext
    filter_upwards [hB i,genericBoundedRealMul_ae (θ i) (hm i) F,hF] with x hx hy hf
    rw [hy,hf]
    change B i x = θ i x • (η x • f x)
    change B i x = θ i x • f x at hx
    rw [hx]
    by_cases ht : θ i x = 0
    · simp [ht]
    · have hk : x ∈ tsupport χ := by
        apply tsupport_fderiv_apply_subset ℝ (b i)
        apply subset_tsupport (fun z => fderiv ℝ χ z (b i))
        intro hz
        exact ht (by simp [θ,hz])
      rw [hplateau x hk,one_smul]
  refine ⟨U,hU,?_⟩
  apply generic_h2_of_h1_multiplier_divergence b U A F d hd θ hθ hm hDm
  simpa only [hb] using hΔ

#print axioms generic_nested_cutoff_h2
end TheoremT.Continuum
