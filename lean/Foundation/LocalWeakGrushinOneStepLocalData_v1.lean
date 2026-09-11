import LocalWeakGrushinOneStep_v1

/-! Actual local weak Grushin gain for raw locally L2 data. The compact region
and its constant are fixed before the input and forcing functions. Output jets
are genuine weak derivatives of the cutoff of the raw input; no input derivative
or global input L2 premise is introduced by the indicator extension. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem local_weak_grushin_cutoff_one_step_local_data {c : ℝ} (hc : 0 < c)
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {χ : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ Ω) :
    ∃ K : Set (Space κ), ∃ C : ℝ,
      IsCompact K ∧ tsupport χ ⊆ K ∧ K ⊆ Ω ∧ 0 ≤ C ∧
      ∀ rawG rawh : Space κ → ℂ,
        ProductLocallyL2On rawG Ω → ProductLocallyL2On rawh Ω →
        (∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
          (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • rawG p) =
            ∫ p, φ p • rawh p) →
        let F : ℝ := ∫ p in K, ‖rawG p‖ ^ 2
        let M : ℝ := ∫ p in K, ‖rawh p‖ ^ 2
        ∃ U : Lp ℂ 2 (volume : Measure (Space κ)),
        ∃ gy : Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
        ∃ gt : κ → Lp ℂ 2 (volume : Measure (Space κ)),
        ∃ hyy : Fin 4 → Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
          U =ᵐ[volume] (fun p => χ p • rawG p) ∧
          (∑ i, ‖gy i‖ ^ 2) ≤ 2 * (C * F) + (3/4 : ℝ) * (C * (F + M)) ∧
          (∑ j, ‖gt j‖ ^ 2) ≤ (C * (F + M)) / (16 * c) ∧
          (∑ i, ∑ j, ‖hyy i j‖ ^ 2) ≤ (3/2 : ℝ) * (C * (F + M)) ∧
          (∀ i, WeakProductL2Directional U (gy i) (yDir i)) ∧
          (∀ j, WeakProductL2Directional U (gt j) (tDir j)) ∧
          ∀ i j, WeakProductL2Directional (gy i) (hyy i j) (yDir j) := by
  obtain ⟨K, hK, hKΩ, V, hV, hχV, hVK⟩ :=
    product_compact_intermediate_neighborhood hcχ hΩ hχΩ
  obtain ⟨C, hC, hgain⟩ := local_weak_grushin_cutoff_one_step hc hV hχ hcχ hχV
  refine ⟨K, C, hK, hχV.trans hVK, hKΩ, hC, ?_⟩
  intro rawG rawh hG hh hP
  dsimp only
  have hBasis : (EuclideanSpace.basisFun κ ℝ : κ → EuclideanSpace ℝ κ) = oscillatorBasis := by
    funext j
    exact EuclideanSpace.basisFun_apply κ ℝ j
  obtain ⟨G, h, hon, _, hGn, hhn, hPV⟩ :=
    grushin_local_l2_extension c (EuclideanSpace.basisFun κ ℝ) hK hKΩ hVK
      rawG rawh hG hh (by simpa only [hBasis] using hP)
  rw [hBasis] at hPV
  obtain ⟨U, gy, gt, hyy, hU, hY, hT, hYY, hgy, hgt, hhyy⟩ := hgain G h hPV
  have hraw : U =ᵐ[volume] (fun p => χ p • rawG p) := by
    filter_upwards [hU, hon] with p hp hq
    rw [hp]
    by_cases hmem : p ∈ K
    · rw [(hq hmem).1]
    · have hoff : p ∉ tsupport χ := fun h => hmem (hVK (hχV h))
      simp only [image_eq_zero_of_notMem_tsupport hoff, zero_smul]
  rw [hGn, hhn] at hY hT hYY
  exact ⟨U, gy, gt, hyy, hraw, hY, hT, hYY, hgy, hgt, hhyy⟩

#print axioms local_weak_grushin_cutoff_one_step_local_data
end TheoremT.Continuum.WeakGrushin
