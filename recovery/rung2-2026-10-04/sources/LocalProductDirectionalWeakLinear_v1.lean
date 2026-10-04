import LocalProductDirectionalWeakAlgebra_v1

/-! Linear operations and local almost-everywhere replacement for genuine
bundled local weak derivatives in arbitrary constant product directions.
Local L2 and compact-test integrability follow from the bundled premises. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
namespace TheoremT.Continuum
variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

theorem ProductLocalWeakDirectional.zero (Ω : Set (Y × T)) (v : Y × T) :
    ProductLocalWeakDirectional Ω (fun _ => 0) (fun _ => 0) v := by
  refine ⟨(fun K _ _ => by simp),(fun K _ _ => by simp),?_⟩
  intro φ _ _ _
  simp

theorem ProductLocalWeakDirectional.add
    {Ω : Set (Y × T)} {f g df dg : Y × T → ℂ} {v : Y × T}
    (hD : ProductLocalWeakDirectional Ω f df v)
    (hE : ProductLocalWeakDirectional Ω g dg v) :
    ProductLocalWeakDirectional Ω (fun p => f p + g p) (fun p => df p + dg p) v := by
  refine ⟨(fun K hK hs => (hD.1 K hK hs).add (hE.1 K hK hs)),
    (fun K hK hs => (hD.2.1 K hK hs).add (hE.2.1 K hK hs)),?_⟩
  intro φ hφ hcφ hsφ
  obtain ⟨hid,hif⟩ := hD.test_integrable hφ hcφ hsφ
  obtain ⟨hie,hig⟩ := hE.test_integrable hφ hcφ hsφ
  simp only [smul_add]
  rw [integral_add hid hie,integral_add hif hig,
    hD.2.2 φ hφ hcφ hsφ,hE.2.2 φ hφ hcφ hsφ]
  abel

theorem ProductLocalWeakDirectional.neg
    {Ω : Set (Y × T)} {f d : Y × T → ℂ} {v : Y × T}
    (hD : ProductLocalWeakDirectional Ω f d v) :
    ProductLocalWeakDirectional Ω (fun p => -f p) (fun p => -d p) v := by
  refine ⟨(fun K hK hs => (hD.1 K hK hs).neg),
    (fun K hK hs => (hD.2.1 K hK hs).neg),?_⟩
  intro φ hφ hcφ hsφ
  simpa only [smul_neg,integral_neg,neg_neg] using
    congrArg Neg.neg (hD.2.2 φ hφ hcφ hsφ)

theorem ProductLocalWeakDirectional.sub
    {Ω : Set (Y × T)} {f g df dg : Y × T → ℂ} {v : Y × T}
    (hD : ProductLocalWeakDirectional Ω f df v)
    (hE : ProductLocalWeakDirectional Ω g dg v) :
    ProductLocalWeakDirectional Ω (fun p => f p - g p) (fun p => df p - dg p) v := by
  simpa only [sub_eq_add_neg] using hD.add hE.neg

theorem ProductLocalWeakDirectional.const_smul
    {Ω : Set (Y × T)} {f d : Y × T → ℂ} {v : Y × T}
    (hD : ProductLocalWeakDirectional Ω f d v) (a : ℝ) :
    ProductLocalWeakDirectional Ω (fun p => a • f p) (fun p => a • d p) v := by
  refine ⟨(fun K hK hs => (hD.1 K hK hs).const_smul a),
    (fun K hK hs => (hD.2.1 K hK hs).const_smul a),?_⟩
  intro φ hφ hcφ hsφ
  simpa only [smul_neg,← integral_smul,smul_comm a] using
    congrArg (fun z : ℂ => a • z) (hD.2.2 φ hφ hcφ hsφ)

theorem ProductLocalWeakDirectional.finset_sum
    {ι : Type*} {Ω : Set (Y × T)} {v : Y × T}
    (s : Finset ι) (f d : ι → Y × T → ℂ)
    (hD : ∀ i ∈ s, ProductLocalWeakDirectional Ω (f i) (d i) v) :
    ProductLocalWeakDirectional Ω (fun p => ∑ i ∈ s, f i p) (fun p => ∑ i ∈ s, d i p) v := by
  classical
  revert hD
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simpa only [Finset.sum_empty] using ProductLocalWeakDirectional.zero Ω v
  | @insert i s hi ih =>
    intro hD
    have hI := hD i (Finset.mem_insert_self i s)
    have hS := ih (fun j hj => hD j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using hI.add hS

theorem ProductLocalWeakDirectional.congr_ae_local
    {Ω : Set (Y × T)} {f d g e : Y × T → ℂ} {v : Y × T}
    (hD : ProductLocalWeakDirectional Ω f d v)
    (hfg : ∀ᵐ p ∂volume, p ∈ Ω → f p = g p)
    (hde : ∀ᵐ p ∂volume, p ∈ Ω → d p = e p) :
    ProductLocalWeakDirectional Ω g e v := by
  have hfgK (K : Set (Y × T)) (hK : IsCompact K) (hs : K ⊆ Ω) :
      f =ᵐ[volume.restrict K] g := by
    apply (ae_restrict_iff' hK.measurableSet).2
    filter_upwards [hfg] with p hp hpin
    exact hp (hs hpin)
  have hdeK (K : Set (Y × T)) (hK : IsCompact K) (hs : K ⊆ Ω) :
      d =ᵐ[volume.restrict K] e := by
    apply (ae_restrict_iff' hK.measurableSet).2
    filter_upwards [hde] with p hp hpin
    exact hp (hs hpin)
  refine ⟨(fun K hK hs => (memLp_congr_ae (hfgK K hK hs)).mp (hD.1 K hK hs)),
    (fun K hK hs => (memLp_congr_ae (hdeK K hK hs)).mp (hD.2.1 K hK hs)),?_⟩
  intro φ hφ hcφ hsφ
  calc
    (∫ p, φ p • e p) = ∫ p, φ p • d p := by
      apply integral_congr_ae
      filter_upwards [hde] with p hp
      by_cases ht : p ∈ tsupport φ
      · rw [hp (hsφ ht)]
      · simp only [image_eq_zero_of_notMem_tsupport ht,zero_smul]
    _ = -(∫ p, fderiv ℝ φ p v • f p) := hD.2.2 φ hφ hcφ hsφ
    _ = -(∫ p, fderiv ℝ φ p v • g p) := by
      apply congrArg Neg.neg
      apply integral_congr_ae
      filter_upwards [hfg] with p hp
      by_cases ht : p ∈ tsupport φ
      · rw [hp (hsφ ht)]
      · simp only [fderiv_of_notMem_tsupport ℝ ht,ContinuousLinearMap.zero_apply,zero_smul]

end TheoremT.Continuum
