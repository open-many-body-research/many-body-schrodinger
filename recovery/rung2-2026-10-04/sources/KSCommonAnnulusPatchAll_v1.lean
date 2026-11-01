import KSCommonAnnulusPatch_v1
import PhysicalSpectatorReindexAll_v1
import PhysicalFixedChartBoxInclusion_v1
import PhysicalH12ConcreteStepGeometry_v1

/-! A compact coefficient annulus for either selected electron in N=2.
Each region uses its actual spectator configuration. Physical coordinate boxes
are pulled back by the existing physicalSpectatorReindexAt i isometry.
-/
noncomputable section
namespace TheoremT.Continuum
open WeakGrushin

def ksCommonAnnulusRegionAt (i : Fin 2) : Set (NuclearKSSpace i) :=
  Metric.closedBall (0 : KSSpace) (1/4 : ℝ) ×ˢ
    (Metric.closedBall (0 : SpectatorConfiguration i) (5/4 : ℝ) ∩
      {t | (3/4 : ℝ) ≤ ‖t‖})

theorem ksCommonAnnulusRegionAt_zero :
    ksCommonAnnulusRegionAt (0 : Fin 2) = ksCommonAnnulusRegion := rfl

theorem ksCommonAnnulusRegionAt_mem_iff (i : Fin 2) (q : NuclearKSSpace i) :
    q ∈ ksCommonAnnulusRegionAt i ↔
      ‖q.1‖ ≤ (1/4 : ℝ) ∧ (3/4 : ℝ) ≤ ‖q.2‖ ∧ ‖q.2‖ ≤ (5/4 : ℝ) := by
  simp [ksCommonAnnulusRegionAt, Metric.mem_closedBall, dist_eq_norm, and_comm]

theorem ksCommonAnnulusRegionAt_isCompact (i : Fin 2) :
    IsCompact (ksCommonAnnulusRegionAt i) :=
  (isCompact_closedBall (0 : KSSpace) (1/4 : ℝ)).prod
    ((isCompact_closedBall (0 : SpectatorConfiguration i) (5/4 : ℝ)).inter_right
      (isClosed_le continuous_const continuous_norm))

theorem ksCommonAnnulusRegionAt_zero_center_mem (i : Fin 2)
    {t0 : SpectatorConfiguration i} (ht0 : ‖t0‖ = 1) :
    ((0 : KSSpace),t0) ∈ ksCommonAnnulusRegionAt i := by
  rw [ksCommonAnnulusRegionAt_mem_iff]
  simp [ht0]
  norm_num

theorem nuclearKSLift_other_position_at (i : Fin 2) (q : NuclearKSSpace i) :
    position (nuclearKSLift i q) i.rev = twoElectronSpectatorPositionEquiv i q.2 := by
  ext k
  exact configurationReassemble_spectator i (ksMap q.1) q.2
    ⟨(i.rev,k),by change i.rev ≠ i; fin_cases i <;> decide⟩

theorem twoElectron_other_eq_rev {i j : Fin 2} (hj : j ≠ i) : j = i.rev := by
  fin_cases i <;> fin_cases j <;> simp_all

theorem ksCommonAnnulusRegionAt_ks_radius (i : Fin 2)
    {q : NuclearKSSpace i} (hq : q ∈ ksCommonAnnulusRegionAt i) :
    ‖ksMap q.1‖ ≤ (1/16 : ℝ) := by
  have hy := ((ksCommonAnnulusRegionAt_mem_iff i q).mp hq).1
  calc
    ‖ksMap q.1‖ = ‖q.1‖^2 := ksMap_norm _
    _ ≤ (1/4 : ℝ)^2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
    _ = (1/16 : ℝ) := by norm_num

theorem ksCommonAnnulusRegionAt_other_radius (i : Fin 2)
    {q : NuclearKSSpace i} (hq : q ∈ ksCommonAnnulusRegionAt i)
    {j : Fin 2} (hj : j ≠ i) :
    (3/4 : ℝ) ≤ ‖position (nuclearKSLift i q) j‖ := by
  rw [twoElectron_other_eq_rev hj, nuclearKSLift_other_position_at,
    (twoElectronSpectatorPositionEquiv i).norm_map]
  exact ((ksCommonAnnulusRegionAt_mem_iff i q).mp hq).2.1

theorem ksCommonAnnulusRegionAt_selected_pair_radius (i : Fin 2)
    {q : NuclearKSSpace i} (hq : q ∈ ksCommonAnnulusRegionAt i)
    {j : Fin 2} (hj : j ≠ i) :
    (11/16 : ℝ) ≤ ‖position (nuclearKSLift i q) i - position (nuclearKSLift i q) j‖ := by
  have ht := ((ksCommonAnnulusRegionAt_mem_iff i q).mp hq).2.1
  have hy := ksCommonAnnulusRegionAt_ks_radius i hq
  have hn := norm_sub_norm_le (twoElectronSpectatorPositionEquiv i q.2) (ksMap q.1)
  rw [(twoElectronSpectatorPositionEquiv i).norm_map] at hn
  rw [twoElectron_other_eq_rev hj, nuclearKSLift_selected_position,
    nuclearKSLift_other_position_at, norm_sub_rev]
  linarith

theorem ksCommonAnnulusRegionAt_pair_radius (i : Fin 2)
    {q : NuclearKSSpace i} (hq : q ∈ ksCommonAnnulusRegionAt i)
    {j k : Fin 2} (hjk : j ≠ k) :
    (11/16 : ℝ) ≤ ‖position (nuclearKSLift i q) j - position (nuclearKSLift i q) k‖ := by
  by_cases hj : j = i
  · subst j
    exact ksCommonAnnulusRegionAt_selected_pair_radius i hq hjk.symm
  · have hk : k = i := by
      by_contra hki
      exact hjk ((twoElectron_other_eq_rev hj).trans (twoElectron_other_eq_rev hki).symm)
    subst k
    rw [norm_sub_rev]
    exact ksCommonAnnulusRegionAt_selected_pair_radius i hq hj

theorem ksCommonAnnulusRegionAt_subset_nuclear_patch (i : Fin 2) :
    ksCommonAnnulusRegionAt i ⊆ nuclearKSCoefficientPatch i := by
  intro q hq
  constructor
  · intro j hj
    exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num)
      (ksCommonAnnulusRegionAt_other_radius i hq hj))
  · intro j k hjk
    exact sub_ne_zero.mp (norm_pos_iff.mp (lt_of_lt_of_le (by norm_num)
      (ksCommonAnnulusRegionAt_pair_radius i hq hjk)))

theorem ksCommonAnnulusRegionAt_image_norm (i : Fin 2)
    {q : NuclearKSSpace i} (hq : q ∈ ksCommonAnnulusRegionAt i) :
    ‖nuclearKSLift i q‖ < 2 := by
  obtain ⟨hy, _, ht⟩ := (ksCommonAnnulusRegionAt_mem_iff i q).mp hq
  exact nuclearKSLift_norm_lt_two i q hy ht

theorem physical_rectangularClosedBox_subset_commonAnnulusAt (i : Fin 2)
    {t : Position} (ht : ‖t‖ = 1) {ry rt : ℝ}
    (hry : 0 ≤ ry) (hrt : 0 ≤ rt) (hy : ry ≤ (1/8 : ℝ)) (htw : rt ≤ (1/8 : ℝ)) :
    physicalSpectatorReindexAt i ⁻¹' rectangularClosedBox (0,t) ry rt ⊆
      ksCommonAnnulusRegionAt i := by
  intro q hq
  have hyq := rectangularClosedBox_y_norm (0,t) hry hq
  have htq := rectangularClosedBox_t_norm (0,t) hrt hq
  change ‖q.1 - 0‖ ≤ 2*ry at hyq
  change ‖twoElectronSpectatorPositionEquiv i q.2 - t‖ ≤ 2*rt at htq
  rw [sub_zero] at hyq
  have hu := norm_sub_norm_le (twoElectronSpectatorPositionEquiv i q.2) t
  have hl := norm_sub_norm_le t (twoElectronSpectatorPositionEquiv i q.2)
  rw [norm_sub_rev] at hl
  rw [ht, (twoElectronSpectatorPositionEquiv i).norm_map] at hu hl
  rw [ksCommonAnnulusRegionAt_mem_iff]
  exact ⟨by linarith, by linarith, by linarith⟩

theorem physical_rectangularOpenBox_subset_commonAnnulusAt (i : Fin 2)
    {t : Position} (ht : ‖t‖ = 1) {ry rt : ℝ}
    (hry : 0 ≤ ry) (hrt : 0 ≤ rt) (hy : ry ≤ (1/8 : ℝ)) (htw : rt ≤ (1/8 : ℝ)) :
    physicalSpectatorReindexAt i ⁻¹' rectangularOpenBox (0,t) ry rt ⊆
      ksCommonAnnulusRegionAt i := by
  intro q hq
  exact physical_rectangularClosedBox_subset_commonAnnulusAt i ht hry hrt hy htw
    (rectangularOpenBox_subset_closedBox (0,t) ry rt hq)

theorem physical_initialization_box_subset_commonAnnulusAt (i : Fin 2)
    {t : Position} (ht : ‖t‖ = 1) :
    physicalSpectatorReindexAt i ⁻¹' rectangularOpenBox (0,t) (1/64) (1/64) ⊆
      ksCommonAnnulusRegionAt i :=
  physical_rectangularOpenBox_subset_commonAnnulusAt i ht
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem physicalH12ConcreteBox_subset_commonAnnulusAt (i : Fin 2)
    {t : Position} (ht : ‖t‖ = 1) {j : ℝ} (hj : 0 ≤ j) :
    physicalH12ConcreteBox i t j ⊆ ksCommonAnnulusRegionAt i := by
  apply (physicalH12ConcreteBox_antitone i t hj).trans
  rw [physicalH12ConcreteBox_zero]
  exact physical_initialization_box_subset_commonAnnulusAt i ht

theorem physical_initialization_box_nuclear_patchAt (i : Fin 2)
    {t : Position} (ht : ‖t‖ = 1) :
    physicalSpectatorReindexAt i ⁻¹' rectangularOpenBox (0,t) (1/64) (1/64) ⊆
      nuclearKSCoefficientPatch i :=
  (physical_initialization_box_subset_commonAnnulusAt i ht).trans
    (ksCommonAnnulusRegionAt_subset_nuclear_patch i)

end TheoremT.Continuum
