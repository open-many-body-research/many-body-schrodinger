import GenericLocalEllipticH2_v1
import ProductLocalEllipticTransport_v1

/-! Local elliptic H2 gain on the ordinary product, with its maximum norm and
actual product Lebesgue measure. Local L2 data and the actual factor-coordinate
Laplacian compact-test equation imply all first and ordered second L2 weak
jets of every smooth compact cutoff. No input derivative witnesses are assumed.
The witnesses are mathematical existence results, not an executable algorithm. -/
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

def ProductLocallyL2On (f : Y × T → ℂ) (Ω : Set (Y × T)) : Prop :=
  ∀ K : Set (Y × T), IsCompact K → K ⊆ Ω → MemLp f 2 (volume.restrict K)

def ProductLocalWeakH2On (f : Y × T → ℂ) (Ω : Set (Y × T)) : Prop :=
  ∀ χ : Y × T → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ Ω →
    ∃ U : Lp ℂ 2 (volume : Measure (Y × T)),
    ∃ d : (Y × T) → Lp ℂ 2 (volume : Measure (Y × T)),
      U =ᵐ[volume] (fun p => χ p • f p) ∧
      (∀ v, WeakProductL2Directional U (d v) v) ∧
      ∀ v q : Y × T, ∃ e : Lp ℂ 2 (volume : Measure (Y × T)),
        WeakProductL2Directional (d v) e q

theorem product_local_elliptic_h2_cutoff
    (bY : OrthonormalBasis ι ℝ Y) (bT : OrthonormalBasis κ ℝ T)
    {Ω : Set (Y × T)} (hΩ : IsOpen Ω) (f w : Y × T → ℂ)
    (hf : ProductLocallyL2On f Ω) (hw : ProductLocallyL2On w Ω)
    (h : ∀ φ : Y × T → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω →
      (∫ p, productFactorLaplacian bY bT φ p • f p) = ∫ p, φ p • w p)
    {χ : Y × T → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ Ω) :
    ∃ U : Lp ℂ 2 (volume : Measure (Y × T)),
    ∃ d : (Y × T) → Lp ℂ 2 (volume : Measure (Y × T)),
      U =ᵐ[volume] (fun p => χ p • f p) ∧
      (∀ v, WeakProductL2Directional U (d v) v) ∧
      ∀ v q : Y × T, ∃ e : Lp ℂ 2 (volume : Measure (Y × T)),
        WeakProductL2Directional (d v) e q := by
  let c := WithLp.prodContinuousLinearEquiv 2 ℝ Y T
  have hΩE : IsOpen (WithLp.ofLp ⁻¹' Ω) := hΩ.preimage c.continuous
  have hfE : GenericLocallyL2On (f ∘ WithLp.ofLp) (WithLp.ofLp ⁻¹' Ω) :=
    product_local_memLp_euclidean_pullback f Ω hf
  have hwE : GenericLocallyL2On (w ∘ WithLp.ofLp) (WithLp.ofLp ⁻¹' Ω) :=
    product_local_memLp_euclidean_pullback w Ω hw
  have hχE : ContDiff ℝ ∞ (χ ∘ WithLp.ofLp) := hχ.comp c.contDiff
  have hcχE : HasCompactSupport (χ ∘ WithLp.ofLp) :=
    hcχ.comp_homeomorph c.toHomeomorph
  have hsχE : tsupport (χ ∘ WithLp.ofLp (p := 2)) ⊆ WithLp.ofLp ⁻¹' Ω := by
    intro q hq
    exact hsχ (tsupport_comp_subset_preimage χ c.continuous hq)
  obtain ⟨U,d,hU,hd,hdd⟩ := generic_local_elliptic_h2_jets hΩE
    (f ∘ WithLp.ofLp) (w ∘ WithLp.ofLp) hfE hwE
    (product_local_factor_tests_euclidean_pullback bY bT f w Ω h) hχE hcχE hsχE
  refine ⟨productEuclideanUnlift U,
    (fun v => productEuclideanUnlift (d (WithLp.toLp 2 v))), ?_, ?_, ?_⟩
  · filter_upwards [productEuclideanUnlift_ae U,
      (WithLp.volume_preserving_toLp Y T).quasiMeasurePreserving.ae hU] with p hp hq
    simpa only [Function.comp_apply,WithLp.ofLp_toLp] using hp.trans hq
  · intro v
    exact weakProductL2Directional_of_euclidean (hd (WithLp.toLp 2 v))
  · intro v q
    obtain ⟨e,he⟩ := hdd (WithLp.toLp 2 v) (WithLp.toLp 2 q)
    exact ⟨productEuclideanUnlift e,weakProductL2Directional_of_euclidean he⟩

theorem product_local_elliptic_h2_on
    (bY : OrthonormalBasis ι ℝ Y) (bT : OrthonormalBasis κ ℝ T)
    {Ω : Set (Y × T)} (hΩ : IsOpen Ω) (f w : Y × T → ℂ)
    (hf : ProductLocallyL2On f Ω) (hw : ProductLocallyL2On w Ω)
    (h : ∀ φ : Y × T → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω →
      (∫ p, productFactorLaplacian bY bT φ p • f p) = ∫ p, φ p • w p) :
    ProductLocalWeakH2On f Ω := by
  intro χ hχ hcχ hsχ
  exact product_local_elliptic_h2_cutoff bY bT hΩ f w hf hw h hχ hcχ hsχ

#print axioms product_local_elliptic_h2_cutoff
#print axioms product_local_elliptic_h2_on
end TheoremT.Continuum
