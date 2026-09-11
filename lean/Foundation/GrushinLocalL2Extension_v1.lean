import GrushinTestSupport_v1
import ProductLocalEllipticH2_v1
import ActualL2IntegralCauchy_v1

/-! Compact restriction of genuine local L2 data to global L2 representatives.
The Grushin test equation is preserved on every interior test region by locality
of the test operator. No derivative of the discontinuous indicator is used.
All norms are those of actual L2 classes for product Lebesgue measure. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum

section Restriction
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def restrictedL2Extension (K : Set X) (hK : MeasurableSet K) (f : X → ℂ)
    (hf : MemLp f 2 (μ.restrict K)) : Lp ℂ 2 μ :=
  ((memLp_indicator_iff_restrict hK).mpr hf).toLp (K.indicator f)

theorem restrictedL2Extension_ae (K : Set X) (hK : MeasurableSet K) (f : X → ℂ)
    (hf : MemLp f 2 (μ.restrict K)) :
    restrictedL2Extension K hK f hf =ᵐ[μ] K.indicator f :=
  MemLp.coeFn_toLp _

theorem restrictedL2Extension_ae_on (K : Set X) (hK : MeasurableSet K) (f : X → ℂ)
    (hf : MemLp f 2 (μ.restrict K)) :
    ∀ᵐ x ∂μ, x ∈ K → restrictedL2Extension K hK f hf x = f x := by
  filter_upwards [restrictedL2Extension_ae K hK f hf] with x hx hmem
  simpa only [Set.indicator_of_mem hmem] using hx

theorem restrictedL2Extension_ae_off (K : Set X) (hK : MeasurableSet K) (f : X → ℂ)
    (hf : MemLp f 2 (μ.restrict K)) :
    ∀ᵐ x ∂μ, x ∉ K → restrictedL2Extension K hK f hf x = 0 := by
  filter_upwards [restrictedL2Extension_ae K hK f hf] with x hx hmem
  simpa only [Set.indicator_of_notMem hmem] using hx

theorem restrictedL2Extension_norm_sq (K : Set X) (hK : MeasurableSet K) (f : X → ℂ)
    (hf : MemLp f 2 (μ.restrict K)) :
    ‖restrictedL2Extension K hK f hf‖ ^ 2 = ∫ x in K, ‖f x‖ ^ 2 ∂μ := by
  rw [restrictedL2Extension, actual_l2_toLp_norm_sq_integral, ← integral_indicator hK]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    by_cases hx : x ∈ K <;> simp [hx])
end Restriction

variable {T : Type*} [NormedAddCommGroup T] [InnerProductSpace ℝ T]
  [FiniteDimensional ℝ T] [MeasurableSpace T] [BorelSpace T]
variable {κ : Type*} [Fintype κ]

theorem grushin_compact_tests_congr_ae_on
    (c : ℝ) (b : OrthonormalBasis κ ℝ T) (B : KSSpace × T → ℝ)
    {K : Set (KSSpace × T)} {G h rawG rawh : KSSpace × T → ℂ}
    (heq : ∀ᵐ p ∂volume, p ∈ K → G p = rawG p ∧ h p = rawh p)
    {φ : KSSpace × T → ℝ} (hs : tsupport φ ⊆ K) :
    (∫ p, splitGrushin c b B φ p • G p) =
      (∫ p, splitGrushin c b B φ p • rawG p) ∧
    (∫ p, φ p • h p) = ∫ p, φ p • rawh p := by
  constructor
  · apply integral_congr_ae
    filter_upwards [heq] with p hp
    by_cases hmem : p ∈ K
    · rw [(hp hmem).1]
    · have hoff : p ∉ tsupport φ := fun h => hmem (hs h)
      simp only [splitGrushin_zero_off_test c b B hoff, zero_smul]
  · apply integral_congr_ae
    filter_upwards [heq] with p hp
    by_cases hmem : p ∈ K
    · rw [(hp hmem).2]
    · have hoff : p ∉ tsupport φ := fun h => hmem (hs h)
      simp only [image_eq_zero_of_notMem_tsupport hoff, zero_smul]

theorem grushin_local_l2_extension
    (c : ℝ) (b : OrthonormalBasis κ ℝ T)
    {Ω K U : Set (KSSpace × T)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hUK : U ⊆ K)
    (rawG rawh : KSSpace × T → ℂ)
    (hG : ProductLocallyL2On rawG Ω) (hh : ProductLocallyL2On rawh Ω)
    (hweak : ∀ φ : KSSpace × T → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c b (fun _ => 0) φ p • rawG p) = ∫ p, φ p • rawh p) :
    ∃ G h : Lp ℂ 2 (volume : Measure (KSSpace × T)),
      (∀ᵐ p ∂volume, p ∈ K → G p = rawG p ∧ h p = rawh p) ∧
      (∀ᵐ p ∂volume, p ∉ K → G p = 0 ∧ h p = 0) ∧
      ‖G‖ ^ 2 = (∫ p in K, ‖rawG p‖ ^ 2) ∧
      ‖h‖ ^ 2 = (∫ p in K, ‖rawh p‖ ^ 2) ∧
      ∀ φ : KSSpace × T → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ U →
        (∫ p, splitGrushin c b (fun _ => 0) φ p • G p) = ∫ p, φ p • h p := by
  let G := restrictedL2Extension K hK.measurableSet rawG (hG K hK hKΩ)
  let h := restrictedL2Extension K hK.measurableSet rawh (hh K hK hKΩ)
  have hon : ∀ᵐ p ∂volume, p ∈ K → G p = rawG p ∧ h p = rawh p := by
    filter_upwards [restrictedL2Extension_ae_on K hK.measurableSet rawG (hG K hK hKΩ),
      restrictedL2Extension_ae_on K hK.measurableSet rawh (hh K hK hKΩ)] with p hp hq hmem
    exact ⟨hp hmem, hq hmem⟩
  have hoff : ∀ᵐ p ∂volume, p ∉ K → G p = 0 ∧ h p = 0 := by
    filter_upwards [restrictedL2Extension_ae_off K hK.measurableSet rawG (hG K hK hKΩ),
      restrictedL2Extension_ae_off K hK.measurableSet rawh (hh K hK hKΩ)] with p hp hq hmem
    exact ⟨hp hmem, hq hmem⟩
  refine ⟨G, h, hon, hoff,
    restrictedL2Extension_norm_sq K hK.measurableSet rawG (hG K hK hKΩ),
    restrictedL2Extension_norm_sq K hK.measurableSet rawh (hh K hK hKΩ), ?_⟩
  intro φ hφ hcφ hsφ
  have htests := grushin_compact_tests_congr_ae_on c b (fun _ => 0) hon
    (hsφ.trans hUK)
  rw [htests.1, htests.2]
  exact hweak φ hφ hcφ (hsφ.trans (hUK.trans hKΩ))

#print axioms grushin_local_l2_extension
end TheoremT.Continuum
