import PhysicalSpectatorReindex_v1
import GrushinRectangularBoxGeometry_v1
import KSFixedChartPatch_v1

/-! Exact physical inclusion of the canonical seven-coordinate boxes into
the fixed compact coefficient region. The displayed width bound includes the
required initialization width 1/64. No equality of spectator index types is
assumed: the existing physical linear isometry is used explicitly. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum
open WeakGrushin

theorem rectangularClosedBox_t_norm (a : Space (Fin 3)) {ry rt : ℝ}
    (hrt : 0 ≤ rt) {p : Space (Fin 3)}
    (hp : p ∈ rectangularClosedBox a ry rt) : ‖p.2-a.2‖ ≤ 2*rt := by
  have hsq : ‖p.2-a.2‖^2 ≤ 3*rt^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ i : Fin 3, rt^2 := Finset.sum_le_sum (fun i _ => by
        have hi : |p.2 i-a.2 i| ≤ rt := hp (.inr i)
        simpa only [sq_abs,PiLp.sub_apply] using pow_le_pow_left₀ (abs_nonneg _) hi 2)
      _ = _ := by simp
  nlinarith [norm_nonneg (p.2-a.2)]

theorem physical_rectangularClosedBox_subset_fixed_chart
    (t0 : SpectatorConfiguration (0 : Fin 2)) {ry rt : ℝ}
    (hry : 0 ≤ ry) (hrt : 0 ≤ rt) (hy : ry ≤ (1/8 : ℝ)) (ht : rt ≤ (1/8 : ℝ)) :
    physicalSpectatorReindex ⁻¹'
      rectangularClosedBox (0,pairCenterEquiv t0) ry rt ⊆ ksFixedChartRegion t0 := by
  intro q hq
  have hyq := rectangularClosedBox_y_norm (0,pairCenterEquiv t0) hry hq
  have htq := rectangularClosedBox_t_norm (0,pairCenterEquiv t0) hrt hq
  change ‖q.1 - 0‖ ≤ 2*ry at hyq
  change ‖pairCenterEquiv q.2 - pairCenterEquiv t0‖ ≤ 2*rt at htq
  rw [sub_zero] at hyq
  rw [← map_sub,pairCenterEquiv.norm_map] at htq
  rw [ksFixedChartRegion_mem_iff]
  constructor <;> linarith

theorem physical_rectangularOpenBox_subset_fixed_chart
    (t0 : SpectatorConfiguration (0 : Fin 2)) {ry rt : ℝ}
    (hry : 0 ≤ ry) (hrt : 0 ≤ rt) (hy : ry ≤ (1/8 : ℝ)) (ht : rt ≤ (1/8 : ℝ)) :
    physicalSpectatorReindex ⁻¹'
      rectangularOpenBox (0,pairCenterEquiv t0) ry rt ⊆ ksFixedChartRegion t0 := by
  intro q hq
  apply physical_rectangularClosedBox_subset_fixed_chart t0 hry hrt hy ht
  exact rectangularOpenBox_subset_closedBox (0,pairCenterEquiv t0) ry rt hq

theorem physical_rectangularOpenBox_coefficient_patches
    {t0 : SpectatorConfiguration (0 : Fin 2)} (ht0 : ‖t0‖ = 1) {ry rt : ℝ}
    (hry : 0 ≤ ry) (hrt : 0 ≤ rt) (hy : ry ≤ (1/8 : ℝ)) (ht : rt ≤ (1/8 : ℝ)) :
    (physicalSpectatorReindex ⁻¹' rectangularOpenBox (0,pairCenterEquiv t0) ry rt ⊆
      nuclearKSCoefficientPatch (0 : Fin 2)) ∧
    (physicalSpectatorReindex ⁻¹' rectangularOpenBox (0,pairCenterEquiv t0) ry rt ⊆
      pairKSCoefficientPatch) := by
  have h := physical_rectangularOpenBox_subset_fixed_chart t0 hry hrt hy ht
  exact ⟨h.trans (ksFixedChartRegion_subset_nuclear_patch ht0),
    h.trans (ksFixedChartRegion_subset_pair_patch ht0)⟩

theorem physical_initialization_box_coefficient_patches
    {t0 : SpectatorConfiguration (0 : Fin 2)} (ht0 : ‖t0‖ = 1) :
    (physicalSpectatorReindex ⁻¹' rectangularOpenBox (0,pairCenterEquiv t0) (1/64) (1/64) ⊆
      nuclearKSCoefficientPatch (0 : Fin 2)) ∧
    (physicalSpectatorReindex ⁻¹' rectangularOpenBox (0,pairCenterEquiv t0) (1/64) (1/64) ⊆
      pairKSCoefficientPatch) :=
  physical_rectangularOpenBox_coefficient_patches ht0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

#print axioms rectangularClosedBox_t_norm
#print axioms physical_rectangularClosedBox_subset_fixed_chart
#print axioms physical_rectangularOpenBox_subset_fixed_chart
#print axioms physical_rectangularOpenBox_coefficient_patches
#print axioms physical_initialization_box_coefficient_patches
end TheoremT.Continuum
