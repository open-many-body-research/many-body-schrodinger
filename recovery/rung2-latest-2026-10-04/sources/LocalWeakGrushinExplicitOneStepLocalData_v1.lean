import LocalWeakGrushinExplicitOneStep_v1

/-! The explicit rough one-step estimate for raw locally L2 data.
The compact restriction region and its open interior test region are selected
before the raw input and forcing. Indicator extensions preserve the local PDE;
the exact squared-norm identities retain both explicit coefficients of J.
No new extremum, input derivative, or global L2 hypothesis is introduced. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem local_weak_grushin_explicit_one_step_local_data {c : ℝ} (hc : 0 < c)
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {χ η : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hηΩ : tsupport η ⊆ Ω)
    {W : Set (Space κ)} (hW : IsOpen W) (hχW : tsupport χ ⊆ W)
    (hη1 : ∀ p ∈ W, η p = 1)
    (M A B D Q : ℝ) (hB0 : 0 ≤ B) (hD0 : 0 ≤ D) (hQ0 : 0 ≤ Q)
    (hM : ∀ p, |χ p| ≤ M)
    (hA : ∀ p ∈ tsupport χ, |combinedCutoffScalar c χ p| ≤ A)
    (hB : ∀ p ∈ tsupport χ, cutoffGradientWeight c χ p ≤ B)
    (hD : ∀ p, (η p)^2 ≤ D) (hQ : ∀ p, grushinCutoffWeight c η p ≤ Q) :
    ∃ K V : Set (Space κ),
      IsCompact K ∧ K ⊆ Ω ∧ IsOpen V ∧ tsupport η ⊆ V ∧ V ⊆ K ∧ tsupport χ ⊆ K ∧
      ∀ rawG rawh : Space κ → ℂ,
        ProductLocallyL2On rawG Ω → ProductLocallyL2On rawh Ω →
        (∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
          (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • rawG p) =
            ∫ p, φ p • rawh p) →
        let F : ℝ := ∫ p in K, ‖rawG p‖^2
        let H : ℝ := ∫ p in K, ‖rawh p‖^2
        let J : ℝ := (4*A^2+16*B*(D/2+Q))*F+(2*M^2+8*B*D)*H
        ∃ U : Lp ℂ 2 (volume : Measure (Space κ)),
        ∃ gy : Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
        ∃ gt : κ → Lp ℂ 2 (volume : Measure (Space κ)),
        ∃ hyy : Fin 4 → Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
          U =ᵐ[volume] (fun p => χ p • rawG p) ∧ ‖U‖^2 ≤ M^2*F ∧
          (∑ i, ‖gy i‖^2) ≤ 2*(M^2*F)+(3/4 : ℝ)*J ∧
          (∑ j, ‖gt j‖^2) ≤ J/(16*c) ∧
          (∑ i, ∑ j, ‖hyy i j‖^2) ≤ (3/2 : ℝ)*J ∧
          (∀ i, WeakProductL2Directional U (gy i) (yDir i)) ∧
          (∀ j, WeakProductL2Directional U (gt j) (tDir j)) ∧
          ∀ i j, WeakProductL2Directional (gy i) (hyy i j) (yDir j) := by
  obtain ⟨K, hK, hKΩ, V, hV, hηV, hVK⟩ :=
    product_compact_intermediate_neighborhood hcη hΩ hηΩ
  have hχη : tsupport χ ⊆ tsupport η := by
    intro p hp
    apply subset_tsupport η
    change η p ≠ 0
    rw [hη1 p (hχW hp)]
    norm_num
  have hχK : tsupport χ ⊆ K := hχη.trans (hηV.trans hVK)
  refine ⟨K, V, hK, hKΩ, hV, hηV, hVK, hχK, ?_⟩
  intro rawG rawh hG hh hP
  dsimp only
  have hBasis : (EuclideanSpace.basisFun κ ℝ : κ → EuclideanSpace ℝ κ) = oscillatorBasis := by
    funext j
    exact EuclideanSpace.basisFun_apply κ ℝ j
  obtain ⟨G, h, hon, _, hGn, hhn, hPV⟩ :=
    grushin_local_l2_extension c (EuclideanSpace.basisFun κ ℝ) hK hKΩ hVK
      rawG rawh hG hh (by simpa only [hBasis] using hP)
  rw [hBasis] at hPV
  obtain ⟨U, gy, gt, hyy, hU, hUn, hY, hT, hYY, hgy, hgt, hhyy⟩ :=
    local_weak_grushin_explicit_one_step hc hV hχ hcχ hη hcη hηV hW hχW hη1
      M A B D Q hB0 hD0 hQ0 hM hA hB hD hQ G h hPV
  have hraw : U =ᵐ[volume] (fun p => χ p • rawG p) := by
    filter_upwards [hU, hon] with p hp hq
    rw [hp]
    by_cases hmem : p ∈ K
    · rw [(hq hmem).1]
    · have hoff : p ∉ tsupport χ := fun ht => hmem (hχK ht)
      simp only [image_eq_zero_of_notMem_tsupport hoff, zero_smul]
  rw [hGn] at hUn
  rw [hGn, hhn] at hY hT hYY
  exact ⟨U, gy, gt, hyy, hraw, hUn, hY, hT, hYY, hgy, hgt, hhyy⟩

#print axioms local_weak_grushin_explicit_one_step_local_data
end TheoremT.Continuum.WeakGrushin
