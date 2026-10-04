import ManyBody.S8.Internal.HigherYRegularity

/-!
# Higher regularity of all first directions

The spectator equation and bootstrap are proved for arbitrary spectator
directions.  Weak derivative uniqueness joins them to the Y bootstrap, proving
joint local H² of every first directional derivative of an actual homogeneous
solution with genuine joint H² data.  No third derivatives are assumed.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin

namespace ManyBody.S8
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem weak_grushin_homogeneous_spectator_direction_equation
    (c : ℝ) {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {B : Space κ → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    {U d : Lp ℂ 2 (volume : Measure (Space κ))} (v : EuclideanSpace ℝ κ)
    (hD : WeakProductL2Directional U d (0, v))
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis B φ p • U p) = 0) :
    ProductLocallyL2On (fun p => -(fderiv ℝ B p (0, v) • U p)) Ω ∧
    ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis B φ p • d p) =
        ∫ p, φ p • -(fderiv ℝ B p (0, v) • U p) := by
  have hUl : ProductLocallyL2On (U : Space κ → ℂ) Ω :=
    fun _ _ _ => (Lp.memLp U).mono_measure Measure.restrict_le_self
  have hdl : ProductLocallyL2On (d : Space κ → ℂ) Ω :=
    fun _ _ _ => (Lp.memLp d).mono_measure Measure.restrict_le_self
  have hsource : ProductLocallyL2On
      (fun p => -(fderiv ℝ B p (0, v) • U p)) Ω := by
    intro K hK hKΩ
    have hmD := (smooth_coefficient_and_directional_memLp_top_restrict_compact
      (μ := volume) hΩ hK hKΩ hB (0, v)).2
    exact (((Lp.memLp U).mono_measure Measure.restrict_le_self).smul hmD).neg
  obtain ⟨hBU, hleibL2, hleib⟩ :=
    weakProduct_spectator_local_potential_leibniz hD hΩ hB
  have hnegBU : ProductLocallyL2On (fun p => -(B p • U p)) Ω :=
    fun K hK hKΩ => (hBU K hK hKΩ).neg
  have hnegLeib : ProductLocallyL2On
      (fun p => -(B p • d p + fderiv ℝ B p (0, v) • U p)) Ω :=
    fun K hK hKΩ => (hleibL2 K hK hKΩ).neg
  have hzero : ProductLocallyL2On (fun _ : Space κ => (0 : ℂ)) Ω :=
    fun _ _ _ => MemLp.zero
  have hBasis : (EuclideanSpace.basisFun κ ℝ : κ → EuclideanSpace ℝ κ) =
      oscillatorBasis := by
    funext k
    exact EuclideanSpace.basisFun_apply κ ℝ k
  have hP0 : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • U p) =
        ∫ p, φ p • -(B p • U p) := by
    have hz : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
        (∫ p, splitGrushin c (EuclideanSpace.basisFun κ ℝ) B φ p • U p) =
          ∫ p, φ p • (0 : ℂ) := by
      intro φ hφ hcφ hsφ
      simpa only [hBasis, smul_zero, integral_zero] using hP φ hφ hcφ hsφ
    simpa only [hBasis, zero_sub] using
      (grushin_local_potential_reduction_iff c (EuclideanSpace.basisFun κ ℝ)
        hB.continuousOn U (fun _ => 0) hUl hzero).mp hz
  have hhD : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, φ p • -(B p • d p + fderiv ℝ B p (0, v) • U p)) =
        -(∫ p, fderiv ℝ φ p (0, v) • -(B p • U p)) := by
    intro φ hφ hcφ hsφ
    simpa only [tDir, smul_neg, integral_neg, neg_neg] using
      congrArg Neg.neg (hleib φ hφ hcφ hsφ).2.2
  have hdiff := weak_grushin_spectator_differentiate c
    (fun p => -(B p • U p))
    (fun p => -(B p • d p + fderiv ℝ B p (0, v) • U p))
    hnegBU hnegLeib v hD hP0 hhD
  refine ⟨hsource, ?_⟩
  intro φ hφ hcφ hsφ
  have hiff := grushin_local_potential_test_iff c (EuclideanSpace.basisFun κ ℝ)
    hB.continuousOn d (fun p => -(fderiv ℝ B p (0, v) • U p))
    hdl hsource hφ hcφ hsφ
  rw [hBasis] at hiff
  apply hiff.mpr
  convert hdiff φ hφ hcφ hsφ using 1
  congr 1
  funext p
  rw [neg_add, sub_eq_add_neg, add_comm]


#print axioms weak_grushin_homogeneous_spectator_direction_equation

theorem homogeneous_grushin_spectator_direction_local_h2
    {c : ℝ} (hc : 0 < c) {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {B : Space κ → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    {U : Lp ℂ 2 (volume : Measure (Space κ))}
    {d : Lp ℂ 2 (volume : Measure (Space κ))}
    {dt : κ → Lp ℂ 2 (volume : Measure (Space κ))}
    (v : EuclideanSpace ℝ κ) (hD : WeakProductL2Directional U d (0, v))
    (hd : ∀ j, WeakProductL2Directional U (dt j) (tDir j))
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis B φ p • U p) = 0) :
    ProductLocalWeakH2On (d : Space κ → ℂ) Ω := by
  intro χ hχ hcχ hχΩ
  let A : Space κ → ℝ := fun p => fderiv ℝ B p (0, v)
  let g : Space κ → ℂ := fun p => -(A p • U p)
  let k (l : κ) : Space κ → ℂ :=
    fun p => -(A p • dt l p + fderiv ℝ A p (tDir l) • U p)
  have hA : ContDiffOn ℝ ∞ A Ω := by
    intro p hp
    exact (local_contDiffAt_directional_derivative (hB.contDiffAt (hΩ.mem_nhds hp))
      (0, v)).contDiffWithinAt
  obtain ⟨hg, hPj⟩ := weak_grushin_homogeneous_spectator_direction_equation c hΩ hB v hD hP
  have hk : ∀ l, ProductLocallyL2On (k l) Ω := by
    intro l K hK hKΩ
    have hh := product_spectator_potential_leibniz_locallyL2 hΩ hA U (dt l) (oscillatorBasis l)
    exact (hh K hK hKΩ).neg
  have hgD : ∀ l, ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, φ p • k l p) = -(∫ p, fderiv ℝ φ p (tDir l) • g p) := by
    intro l φ hφ hcφ hsφ
    have hh := (weakProduct_directional_local_potential_test (hd l) hΩ hA hφ hcφ hsφ).2.2
    simpa only [k, g, tDir, smul_neg, integral_neg, neg_neg] using congrArg Neg.neg hh
  obtain ⟨η, hη, hcη, hsη, V, hV, hχV, hVO, hη1⟩ :=
    exists_outer_plateau hcχ hΩ hχΩ
  obtain ⟨K, C, hK, hηK, hKΩ, hC, hgain⟩ :=
    local_weak_grushin_potential_cutoff_gain hc hΩ hη hcη hsη
  have hdl : ProductLocallyL2On (d : Space κ → ℂ) Ω :=
    fun _ _ _ => (Lp.memLp (d)).mono_measure Measure.restrict_le_self
  obtain ⟨Wouter, gy, gt, hyy, hWouter, _, _, _, hgy, hgt, hhyy⟩ :=
    hgain B (d) g hB.continuousOn hdl hg hPj
  have hPouter : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∫ p, splitGrushin c oscillatorBasis B φ p • Wouter p) = ∫ p, φ p • g p := by
    intro φ hφ hcφ hsφ
    calc
      _ = ∫ p, splitGrushin c oscillatorBasis B φ p • d p := by
        apply integral_congr_ae
        filter_upwards [hWouter] with p hp
        by_cases ht : p ∈ tsupport φ
        · rw [hp, hη1 p (hsφ ht), one_smul]
        · rw [splitGrushin_zero_off_test c oscillatorBasis B ht]
          simp only [zero_smul]
      _ = _ := hPj φ hφ hcφ (hsφ.trans hVO)
  have hgV : ProductLocallyL2On g V := fun K hK hKV => hg K hK (hKV.trans hVO)
  have hkV : ∀ l, ProductLocallyL2On (k l) V :=
    fun l K hK hKV => hk l K hK (hKV.trans hVO)
  have hgDV : ∀ l, ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∫ p, φ p • k l p) = -(∫ p, fderiv ℝ φ p (tDir l) • g p) :=
    fun l φ hφ hcφ hsφ => hgD l φ hφ hcφ (hsφ.trans hVO)
  obtain ⟨W, a, b, hW, ha, hb⟩ := local_inhomogeneous_grushin_joint_cutoff_h2
    hc hV (hB.mono hVO) hχ hcχ hχV hgy hgt hhyy g k hgV hkV hgDV hPouter
  refine ⟨W, a, ?_, ha, fun v w => ⟨b v w, hb v w⟩⟩
  filter_upwards [hW, hWouter] with p hp hw
  rw [hp]
  by_cases ht : p ∈ tsupport χ
  · rw [hw, hη1 p (hχV ht), one_smul]
  · simp only [image_eq_zero_of_notMem_tsupport ht, zero_smul]


#print axioms homogeneous_grushin_spectator_direction_local_h2
omit [DecidableEq κ] in
theorem product_local_weakH2_congr_ae
    {Ω : Set (Space κ)} {f g : Space κ → ℂ}
    (hf : ProductLocalWeakH2On f Ω) (hfg : f =ᵐ[volume] g) :
    ProductLocalWeakH2On g Ω := by
  intro χ hχ hcχ hχΩ
  obtain ⟨U, d, hU, hd, he⟩ := hf χ hχ hcχ hχΩ
  refine ⟨U, d, ?_, hd, he⟩
  filter_upwards [hU, hfg] with p hp hq
  exact hp.trans (congrArg (fun z : ℂ => χ p • z) hq)

omit [DecidableEq κ] in
theorem product_local_weakH2_add
    {Ω : Set (Space κ)} {f g : Space κ → ℂ}
    (hf : ProductLocalWeakH2On f Ω) (hg : ProductLocalWeakH2On g Ω) :
    ProductLocalWeakH2On (fun p => f p + g p) Ω := by
  intro χ hχ hcχ hχΩ
  obtain ⟨U, d, hU, hd, he⟩ := hf χ hχ hcχ hχΩ
  obtain ⟨V, a, hV, ha, hb⟩ := hg χ hχ hcχ hχΩ
  refine ⟨U + V, (fun v => d v + a v), ?_, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_add U V, hU, hV] with p hp hq hr
    rw [hp, Pi.add_apply, hq, hr, smul_add]
  · intro v
    exact weak_product_directional_add (hd v) (ha v)
  · intro v w
    obtain ⟨e, he⟩ := he v w
    obtain ⟨b, hb⟩ := hb v w
    exact ⟨e + b, weak_product_directional_add he hb⟩

omit [DecidableEq κ] in
theorem weak_product_direction_sum
    {U dv dw : Lp ℂ 2 (volume : Measure (Space κ))} {v w : Space κ}
    (hv : WeakProductL2Directional U dv v)
    (hw : WeakProductL2Directional U dw w) :
    WeakProductL2Directional U (dv + dw) (v + w) := by
  intro φ hφ hcφ
  have hDφ (z : Space κ) : ContDiff ℝ ∞ (fun p => fderiv ℝ φ p z) :=
    (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).clm_apply contDiff_const
  have hint (f : Lp ℂ 2 (volume : Measure (Space κ)))
      {ψ : Space κ → ℝ} (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) :
      Integrable (fun p => ψ p • f p) :=
    ((Lp.memLp f).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport hψ hcψ
  have hl :
      (∫ p, φ p • (dv + dw) p) = (∫ p, φ p • dv p) + ∫ p, φ p • dw p := by
    calc
      _ = ∫ p, φ p • dv p + φ p • dw p := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add dv dw] with p hp
        rw [hp, Pi.add_apply, smul_add]
      _ = _ := integral_add (hint dv hφ.continuous hcφ) (hint dw hφ.continuous hcφ)
  have hr :
      (∫ p, fderiv ℝ φ p (v + w) • U p) =
        (∫ p, fderiv ℝ φ p v • U p) + ∫ p, fderiv ℝ φ p w • U p := by
    simp_rw [map_add, add_smul]
    exact integral_add
      (hint U (hDφ v).continuous (hcφ.fderiv_apply ℝ v))
      (hint U (hDφ w).continuous (hcφ.fderiv_apply ℝ w))
  rw [hl, hr, hv φ hφ hcφ, hw φ hφ hcφ]
  abel

theorem homogeneous_grushin_first_direction_local_h2
    {c : ℝ} (hc : 0 < c) {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {B : Space κ → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    {U : Lp ℂ 2 (volume : Measure (Space κ))}
    {a : Space κ → Lp ℂ 2 (volume : Measure (Space κ))}
    {b : Space κ → Space κ → Lp ℂ 2 (volume : Measure (Space κ))}
    (ha : ∀ v, WeakProductL2Directional U (a v) v)
    (hb : ∀ v w, WeakProductL2Directional (a v) (b v w) w)
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis B φ p • U p) = 0) :
    ∀ v, ProductLocalWeakH2On (a v : Space κ → ℂ) Ω := by
  intro v
  have hY := homogeneous_grushin_first_y_local_h2 hc hΩ hB v.1 (ha (v.1, 0))
    (fun j => ha (tDir j)) (fun j => hb (tDir j) (tDir j)) hP
  have hT := homogeneous_grushin_spectator_direction_local_h2 hc hΩ hB v.2
    (ha (0, v.2)) (fun j => ha (tDir j)) hP
  have hsum := weak_product_direction_sum (ha (v.1, 0)) (ha (0, v.2))
  have hv : ((v.1, (0 : EuclideanSpace ℝ κ)) + ((0 : KSSpace), v.2)) = v := by
    ext <;> simp
  rw [hv] at hsum
  have heq : a v = a (v.1, 0) + a (0, v.2) :=
    weakProductL2Directional_unique (ha v) hsum
  rw [heq]
  exact product_local_weakH2_congr_ae (product_local_weakH2_add hY hT)
    (Lp.coeFn_add (a (v.1, 0)) (a (0, v.2))).symm

#print axioms product_local_weakH2_congr_ae
#print axioms product_local_weakH2_add
#print axioms weak_product_direction_sum
#print axioms homogeneous_grushin_first_direction_local_h2

end ManyBody.S8

