import ProductCompactTestTransport_v2

/-! Exact transport of local L2 data and compact-test Laplacian equations from
an ordinary Cartesian product to its Euclidean WithLp 2 copy. The actual
product Lebesgue measure is preserved; no regularity of the data is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff Laplacian
namespace TheoremT.Continuum
variable {Y T ι κ : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]
  [Fintype ι] [Fintype κ]

theorem product_local_memLp_euclidean_pullback
    (f : Y × T → ℂ) (Ω : Set (Y × T))
    (hf : ∀ K : Set (Y × T), IsCompact K → K ⊆ Ω →
      MemLp f 2 (volume.restrict K)) :
    ∀ K : Set (WithLp 2 (Y × T)), IsCompact K → K ⊆ WithLp.ofLp ⁻¹' Ω →
      MemLp (f ∘ WithLp.ofLp) 2 (volume.restrict K) := by
  intro K hK hs
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ Y T
  have heK : IsCompact (WithLp.ofLp '' K) := hK.image e.continuous
  have heΩ : WithLp.ofLp '' K ⊆ Ω := by
    rintro p ⟨q,hq,rfl⟩
    exact hs hq
  exact (hf _ heK heΩ).comp_measurePreserving
    ((WithLp.volume_preserving_ofLp Y T).restrict_image_emb
      e.toHomeomorph.measurableEmbedding K)

theorem product_local_factor_tests_euclidean_pullback
    (bY : OrthonormalBasis ι ℝ Y) (bT : OrthonormalBasis κ ℝ T)
    (f w : Y × T → ℂ) (Ω : Set (Y × T))
    (h : ∀ φ : Y × T → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω →
      (∫ p, productFactorLaplacian bY bT φ p • f p) = ∫ p, φ p • w p) :
    ∀ ψ : WithLp 2 (Y × T) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ WithLp.ofLp ⁻¹' Ω →
      (∫ q, Δ ψ q • (f ∘ WithLp.ofLp) q) =
        ∫ q, ψ q • (w ∘ WithLp.ofLp) q := by
  intro ψ hψ hcψ hsψ
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ Y T
  have hφ : ContDiff ℝ ∞ (ψ ∘ WithLp.toLp 2) := hψ.comp e.symm.contDiff
  have hcφ : HasCompactSupport (ψ ∘ WithLp.toLp 2) :=
    hcψ.comp_homeomorph e.symm.toHomeomorph
  have hsφ : tsupport (ψ ∘ WithLp.toLp 2) ⊆ Ω := by
    intro p hp
    have hp' := tsupport_comp_subset_preimage ψ e.symm.continuous hp
    have hh := hsψ hp'
    change WithLp.ofLp (WithLp.toLp 2 p) ∈ Ω at hh
    simpa only [WithLp.ofLp_toLp] using hh
  have hleft := (WithLp.volume_preserving_ofLp Y T).integral_comp
    e.toHomeomorph.measurableEmbedding
    (fun p => productFactorLaplacian bY bT (ψ ∘ WithLp.toLp 2) p • f p)
  have hright := (WithLp.volume_preserving_ofLp Y T).integral_comp
    e.toHomeomorph.measurableEmbedding
    (fun p => ψ (WithLp.toLp 2 p) • w p)
  calc
    _ = ∫ p, productFactorLaplacian bY bT (ψ ∘ WithLp.toLp 2) p • f p := by
      simpa only [product_factor_laplacian_euclidean_pullback bY bT hψ hcψ,
        WithLp.toLp_ofLp, Function.comp_apply] using hleft
    _ = ∫ p, ψ (WithLp.toLp 2 p) • w p := h _ hφ hcφ hsφ
    _ = _ := by
      simpa only [WithLp.toLp_ofLp, Function.comp_apply] using hright.symm

#print axioms product_local_memLp_euclidean_pullback
#print axioms product_local_factor_tests_euclidean_pullback
end TheoremT.Continuum
