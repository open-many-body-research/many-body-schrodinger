import LocalWeakYLaplacianRecovery_v1
import CompactWeakGrushinYOutputBounds_v1
import LocalWeakGrushinExplicitCutoffOutput_v1
import GrushinLocalL2Extension_v1
import GrushinLocalL2Neighborhood_v1

/-! Quantitative Y recovery from the actual negative Y-Laplacian equation.
Genuine raw local spectator jets supply preliminary joint weak H2 regularity.
The final Y estimates depend only on the solution and forcing norms and the
two supplied cutoffs; spectator derivative norms do not enter the bounds.
The compact restriction set is selected before the raw data and its jets. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem local_y_laplacian_explicit_recovery
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {χ η : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hηΩ : tsupport η ⊆ Ω)
    {W : Set (Space κ)} (hW : IsOpen W) (hχW : tsupport χ ⊆ W)
    (hη1 : ∀ p ∈ W, η p = 1)
    (M A L D Q : ℝ) (hL0 : 0 ≤ L) (_hD0 : 0 ≤ D) (_hQ0 : 0 ≤ Q)
    (hM : ∀ p, |χ p| ≤ M)
    (hA : ∀ p ∈ tsupport χ, |combinedCutoffScalar 0 χ p| ≤ A)
    (hL : ∀ p ∈ tsupport χ, cutoffGradientWeight 0 χ p ≤ L)
    (hD : ∀ p, (η p)^2 ≤ D) (hQ : ∀ p, grushinCutoffWeight 0 η p ≤ Q) :
    ∃ K V : Set (Space κ),
      IsCompact K ∧ K ⊆ Ω ∧ IsOpen V ∧ tsupport η ⊆ V ∧ V ⊆ K ∧ tsupport χ ⊆ K ∧
      ∀ (rawf rawH : Space κ → ℂ) (dT eT : κ → Space κ → ℂ),
        ProductLocallyL2On rawf Ω → ProductLocallyL2On rawH Ω →
        (∀ j, ProductLocallyL2On (dT j) Ω) →
        (∀ j, ProductLocallyL2On (eT j) Ω) →
        (∀ j, LocalSpectatorD Ω rawf (dT j) j) →
        (∀ j, LocalSpectatorD Ω (dT j) (eT j) j) →
        (∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
          (∫ p, splitGrushin 0 oscillatorBasis (fun _ => 0) φ p • rawf p) =
            ∫ p, φ p • rawH p) →
        let F : ℝ := ∫ p in K, ‖rawf p‖^2
        let H : ℝ := ∫ p in K, ‖rawH p‖^2
        let J : ℝ := (4*A^2+16*L*(D/2+Q))*F+(2*M^2+8*L*D)*H
        ∃ U : Lp ℂ 2 (volume : Measure (Space κ)),
        ∃ gy : Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
        ∃ hyy : Fin 4 → Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
          U =ᵐ[volume] (fun p => χ p • rawf p) ∧ ‖U‖^2 ≤ M^2*F ∧
          (∑ i, ‖gy i‖^2) ≤ 2*(M^2*F)+(3/4 : ℝ)*J ∧
          (∑ i, ∑ j, ‖hyy i j‖^2) ≤ (3/2 : ℝ)*J ∧
          (∀ i, WeakProductL2Directional U (gy i) (yDir i)) ∧
          ∀ i j, WeakProductL2Directional (gy i) (hyy i j) (yDir j) := by
  obtain ⟨K,hK,hKΩ,V,hV,hηV,hVK⟩ :=
    product_compact_intermediate_neighborhood hcη hΩ hηΩ
  have hχη : tsupport χ ⊆ tsupport η := by
    intro p hp
    apply subset_tsupport η
    change η p ≠ 0
    rw [hη1 p (hχW hp)]
    norm_num
  have hχK : tsupport χ ⊆ K := hχη.trans (hηV.trans hVK)
  refine ⟨K,V,hK,hKΩ,hV,hηV,hVK,hχK,?_⟩
  intro rawf rawH dT eT hf hH hdL2 heL2 hd he hP
  dsimp only
  have hRawH2 : ProductLocalWeakH2On rawf Ω :=
    local_y_laplacian_h2_of_spectator_jets hΩ rawf rawH dT eT hf hH hdL2 heL2 hd he hP
  have hBasis : (EuclideanSpace.basisFun κ ℝ : κ → EuclideanSpace ℝ κ) = oscillatorBasis := by
    funext j
    exact EuclideanSpace.basisFun_apply κ ℝ j
  obtain ⟨f,h,hon,_,hfn,hhn,hPV⟩ :=
    grushin_local_l2_extension 0 (EuclideanSpace.basisFun κ ℝ) hK hKΩ hVK
      rawf rawH hf hH (by simpa only [hBasis] using hP)
  rw [hBasis] at hPV
  have hfH2 : ProductLocalWeakH2On (f : Space κ → ℂ) V := by
    intro ζ hζ hcζ hsζ
    obtain ⟨U,d,hU,hd,hdd⟩ := hRawH2 ζ hζ hcζ (hsζ.trans (hVK.trans hKΩ))
    refine ⟨U,d,?_,hd,hdd⟩
    filter_upwards [hU,hon] with p hp hq
    rw [hp]
    by_cases ht : p ∈ tsupport ζ
    · rw [(hq (hVK (hsζ ht))).1]
    · simp only [image_eq_zero_of_notMem_tsupport ht,zero_smul]
  obtain ⟨U,H,a,b,hU,ha,hb,hUs,_,hTests,hUn,hHn⟩ :=
    local_weakH2_explicit_cutoff_output (by norm_num : (0 : ℝ) ≤ 0)
      hV hχ hcχ hη hcη hηV hW hχW hη1 M A L D Q hL0 hM hA hL hD hQ f h hfH2 hPV
  have hBounds := compact_weakH2_y_output_bounds (by norm_num : (0 : ℝ) ≤ 0)
    a b ha hb hcχ.isCompact hUs hTests
  have hraw : U =ᵐ[volume] (fun p => χ p • rawf p) := by
    filter_upwards [hU,hon] with p hp hq
    rw [hp]
    by_cases ht : p ∈ tsupport χ
    · rw [(hq (hχK ht)).1]
    · simp only [image_eq_zero_of_notMem_tsupport ht,zero_smul]
  rw [hfn] at hUn
  rw [hfn,hhn] at hHn
  refine ⟨U,(fun i => a (yDir i)),(fun i j => b (yDir i) (yDir j)),
    hraw,hUn,?_,?_,(fun i => ha (yDir i)),(fun i j => hb (yDir i) (yDir j))⟩
  · exact hBounds.1.trans (add_le_add
      (mul_le_mul_of_nonneg_left hUn (by norm_num : (0 : ℝ) ≤ 2))
      (mul_le_mul_of_nonneg_left hHn (by norm_num : (0 : ℝ) ≤ 3/4)))
  · exact hBounds.2.trans
      (mul_le_mul_of_nonneg_left hHn (by norm_num : (0 : ℝ) ≤ 3/2))

end TheoremT.Continuum.WeakGrushin
