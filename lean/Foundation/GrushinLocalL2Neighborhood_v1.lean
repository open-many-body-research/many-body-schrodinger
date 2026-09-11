import GrushinLocalL2Extension_v1
import Mathlib.Topology.MetricSpace.Thickening

/-! Every compact target inside an open Grushin domain has an open neighborhood
on which actual compactly restricted L2 representatives satisfy the same PDE.
The separate integrability lemmas justify the raw local-data test integrals.
Neighborhood and Lp selection are existence results, not executable numerics. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum
variable {T : Type*} [NormedAddCommGroup T] [InnerProductSpace ℝ T]
  [FiniteDimensional ℝ T] [MeasurableSpace T] [BorelSpace T]
variable {κ : Type*} [Fintype κ]

theorem product_locallyL2_compact_smul_integrable
    {Ω : Set (KSSpace × T)} (f : KSSpace × T → ℂ)
    (hf : ProductLocallyL2On f Ω) {θ : KSSpace × T → ℝ}
    (hθ : Continuous θ) (hcθ : HasCompactSupport θ) (hsθ : tsupport θ ⊆ Ω) :
    Integrable (fun p => θ p • f p) := by
  let G := restrictedL2Extension (tsupport θ) hcθ.measurableSet f (hf _ hcθ hsθ)
  have hi : Integrable (fun p => θ p • G p) :=
    ((Lp.memLp G).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport hθ hcθ
  apply hi.congr
  filter_upwards [restrictedL2Extension_ae_on (tsupport θ) hcθ.measurableSet f
    (hf _ hcθ hsθ)] with p hp
  by_cases hmem : p ∈ tsupport θ
  · rw [show G p = f p from hp hmem]
  · simp only [image_eq_zero_of_notMem_tsupport hmem, zero_smul]

theorem grushin_local_l2_test_integrable
    (c : ℝ) (b : OrthonormalBasis κ ℝ T) {Ω : Set (KSSpace × T)}
    (rawG rawh : KSSpace × T → ℂ)
    (hG : ProductLocallyL2On rawG Ω) (hh : ProductLocallyL2On rawh Ω)
    {φ : KSSpace × T → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Ω) :
    Integrable (fun p => splitGrushin c b (fun _ => 0) φ p • rawG p) ∧
    Integrable (fun p => φ p • rawh p) := by
  have hsP : tsupport (splitGrushin c b (fun _ => 0) φ) ⊆ tsupport φ := by
    apply closure_minimal ?_ (isClosed_tsupport φ)
    intro p hp
    by_contra hn
    exact hp (splitGrushin_zero_off_test c b (fun _ => 0) hn)
  exact ⟨product_locallyL2_compact_smul_integrable rawG hG
    (splitGrushin_continuous c b continuous_const hφ)
    (splitGrushin_compact c b (fun _ => 0) hcφ) (hsP.trans hsφ),
    product_locallyL2_compact_smul_integrable rawh hh hφ.continuous hcφ hsφ⟩

omit [MeasurableSpace T] [BorelSpace T] in
theorem product_compact_intermediate_neighborhood
    {K₀ Ω : Set (KSSpace × T)} (hK₀ : IsCompact K₀) (hΩ : IsOpen Ω) (hs : K₀ ⊆ Ω) :
    ∃ K : Set (KSSpace × T), IsCompact K ∧ K ⊆ Ω ∧
      ∃ U : Set (KSSpace × T), IsOpen U ∧ K₀ ⊆ U ∧ U ⊆ K := by
  obtain ⟨δ, hδ, hδΩ⟩ := hK₀.exists_cthickening_subset_open hΩ hs
  exact ⟨Metric.cthickening δ K₀, hK₀.cthickening, hδΩ,
    Metric.thickening δ K₀, Metric.isOpen_thickening,
    Metric.self_subset_thickening hδ K₀, Metric.thickening_subset_cthickening δ K₀⟩

theorem grushin_local_l2_neighborhood
    (c : ℝ) (b : OrthonormalBasis κ ℝ T)
    {K₀ Ω : Set (KSSpace × T)} (hK₀ : IsCompact K₀) (hΩ : IsOpen Ω) (hs : K₀ ⊆ Ω)
    (rawG rawh : KSSpace × T → ℂ)
    (hG : ProductLocallyL2On rawG Ω) (hh : ProductLocallyL2On rawh Ω)
    (hweak : ∀ φ : KSSpace × T → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c b (fun _ => 0) φ p • rawG p) = ∫ p, φ p • rawh p) :
    ∃ K U : Set (KSSpace × T), IsCompact K ∧ K ⊆ Ω ∧ IsOpen U ∧ K₀ ⊆ U ∧ U ⊆ K ∧
    ∃ G h : Lp ℂ 2 (volume : Measure (KSSpace × T)),
      (∀ᵐ p ∂volume, p ∈ K → G p = rawG p ∧ h p = rawh p) ∧
      (∀ᵐ p ∂volume, p ∉ K → G p = 0 ∧ h p = 0) ∧
      ‖G‖ ^ 2 = (∫ p in K, ‖rawG p‖ ^ 2) ∧
      ‖h‖ ^ 2 = (∫ p in K, ‖rawh p‖ ^ 2) ∧
      ∀ φ : KSSpace × T → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ U →
        (∫ p, splitGrushin c b (fun _ => 0) φ p • G p) = ∫ p, φ p • h p := by
  obtain ⟨K, hK, hKΩ, U, hU, hK₀U, hUK⟩ :=
    product_compact_intermediate_neighborhood hK₀ hΩ hs
  exact ⟨K, U, hK, hKΩ, hU, hK₀U, hUK,
    grushin_local_l2_extension c b hK hKΩ hUK rawG rawh hG hh hweak⟩

#print axioms grushin_local_l2_test_integrable
#print axioms grushin_local_l2_neighborhood
end TheoremT.Continuum
