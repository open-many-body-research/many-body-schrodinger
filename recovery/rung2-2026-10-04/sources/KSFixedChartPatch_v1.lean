import PairKSPotential_v1
import NuclearKSPotential_v1
import KSChartImageNorm_v1

/-! A fixed compact two-electron KS chart in the existing spectator space.
The chart is the product of closed balls of radius 1/4 centered at 0 and t0,
where the spectator center has norm 1. It includes the KS collision fiber.
All statements use the existing physical lifts and coefficient patches.
-/
noncomputable section
namespace TheoremT.Continuum

def ksFixedChartRegion (t0 : SpectatorConfiguration (0 : Fin 2)) : Set PairKSSpace :=
  Metric.closedBall (0 : KSSpace) (1/4 : ℝ) ×ˢ Metric.closedBall t0 (1/4 : ℝ)

theorem ksFixedChartRegion_mem_iff
    (t0 : SpectatorConfiguration (0 : Fin 2)) (q : PairKSSpace) :
    q ∈ ksFixedChartRegion t0 ↔ ‖q.1‖ ≤ (1/4 : ℝ) ∧ ‖q.2-t0‖ ≤ (1/4 : ℝ) := by
  simp [ksFixedChartRegion, Metric.mem_closedBall, dist_eq_norm]

theorem ksFixedChartRegion_isCompact (t0 : SpectatorConfiguration (0 : Fin 2)) :
    IsCompact (ksFixedChartRegion t0) :=
  (isCompact_closedBall (0 : KSSpace) (1/4 : ℝ)).prod
    (isCompact_closedBall t0 (1/4 : ℝ))

theorem ksFixedChartRegion_center_mem (t0 : SpectatorConfiguration (0 : Fin 2)) :
    ((0 : KSSpace),t0) ∈ ksFixedChartRegion t0 := by
  rw [ksFixedChartRegion_mem_iff]
  simp

theorem ksFixedChartRegion_spectator_norm
    {t0 : SpectatorConfiguration (0 : Fin 2)} (ht0 : ‖t0‖ = 1)
    {q : PairKSSpace} (hq : q ∈ ksFixedChartRegion t0) :
    (3/4 : ℝ) ≤ ‖q.2‖ ∧ ‖q.2‖ ≤ (5/4 : ℝ) := by
  have ht := ((ksFixedChartRegion_mem_iff t0 q).mp hq).2
  have hu := norm_sub_norm_le q.2 t0
  have hl := norm_sub_norm_le t0 q.2
  rw [norm_sub_rev] at hl
  rw [ht0] at hu hl
  constructor <;> linarith

theorem ksFixedChartRegion_ks_radius
    {t0 : SpectatorConfiguration (0 : Fin 2)}
    {q : PairKSSpace} (hq : q ∈ ksFixedChartRegion t0) :
    ‖ksMap q.1‖ ≤ (1/16 : ℝ) := by
  have hy := ((ksFixedChartRegion_mem_iff t0 q).mp hq).1
  calc
    ‖ksMap q.1‖ = ‖q.1‖^2 := ksMap_norm _
    _ ≤ (1/4 : ℝ)^2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
    _ = (1/16 : ℝ) := by norm_num

theorem ksFixedChartRegion_pair_nuclear_radii
    {t0 : SpectatorConfiguration (0 : Fin 2)} (ht0 : ‖t0‖ = 1)
    {q : PairKSSpace} (hq : q ∈ ksFixedChartRegion t0) :
    (23/32 : ℝ) ≤ ‖position (pairKSLift q) 0‖ ∧
    (23/32 : ℝ) ≤ ‖position (pairKSLift q) 1‖ := by
  have ht := (ksFixedChartRegion_spectator_norm ht0 hq).1
  have hy := ksFixedChartRegion_ks_radius hq
  have hh : ‖(1/2 : ℝ) • ksMap q.1‖ ≤ (1/32 : ℝ) := by
    rw [norm_smul]
    norm_num
    linarith
  have hfirst := norm_sub_norm_le (pairCenterEquiv q.2) (-((1/2 : ℝ) • ksMap q.1))
  simp only [norm_neg, sub_neg_eq_add, pairCenterEquiv.norm_map] at hfirst
  have hsecond := norm_sub_norm_le (pairCenterEquiv q.2) ((1/2 : ℝ) • ksMap q.1)
  rw [pairCenterEquiv.norm_map] at hsecond
  rw [pairKSLift_first, pairKSLift_second]
  constructor <;> linarith

theorem ksFixedChartRegion_subset_pair_patch
    {t0 : SpectatorConfiguration (0 : Fin 2)} (ht0 : ‖t0‖ = 1) :
    ksFixedChartRegion t0 ⊆ pairKSCoefficientPatch := by
  intro q hq
  obtain ⟨h0,h1⟩ := ksFixedChartRegion_pair_nuclear_radii ht0 hq
  exact ⟨norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) h0),
    norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) h1)⟩

theorem nuclearKSLift_zero_other_position (q : NuclearKSSpace (0 : Fin 2)) :
    position (nuclearKSLift (0 : Fin 2) q) 1 = pairCenterEquiv q.2 := by
  ext k
  exact configurationReassemble_spectator (0 : Fin 2) (ksMap q.1) q.2
    ⟨(1,k), by norm_num⟩

theorem ksFixedChartRegion_nuclear_other_radius
    {t0 : SpectatorConfiguration (0 : Fin 2)} (ht0 : ‖t0‖ = 1)
    {q : NuclearKSSpace (0 : Fin 2)} (hq : q ∈ ksFixedChartRegion t0) :
    (3/4 : ℝ) ≤ ‖position (nuclearKSLift (0 : Fin 2) q) 1‖ := by
  rw [nuclearKSLift_zero_other_position, pairCenterEquiv.norm_map]
  exact (ksFixedChartRegion_spectator_norm ht0 hq).1

theorem ksFixedChartRegion_nuclear_pair_radius
    {t0 : SpectatorConfiguration (0 : Fin 2)} (ht0 : ‖t0‖ = 1)
    {q : NuclearKSSpace (0 : Fin 2)} (hq : q ∈ ksFixedChartRegion t0) :
    (11/16 : ℝ) ≤ ‖position (nuclearKSLift (0 : Fin 2) q) 0 -
      position (nuclearKSLift (0 : Fin 2) q) 1‖ := by
  have ht := (ksFixedChartRegion_spectator_norm ht0 hq).1
  have hy := ksFixedChartRegion_ks_radius hq
  have hn := norm_sub_norm_le (pairCenterEquiv q.2) (ksMap q.1)
  rw [pairCenterEquiv.norm_map] at hn
  rw [nuclearKSLift_selected_position, nuclearKSLift_zero_other_position, norm_sub_rev]
  linarith

theorem ksFixedChartRegion_subset_nuclear_patch
    {t0 : SpectatorConfiguration (0 : Fin 2)} (ht0 : ‖t0‖ = 1) :
    ksFixedChartRegion t0 ⊆ nuclearKSCoefficientPatch (0 : Fin 2) := by
  intro q hq
  have hr := ksFixedChartRegion_nuclear_other_radius ht0 hq
  have hd := ksFixedChartRegion_nuclear_pair_radius ht0 hq
  have hother : position (nuclearKSLift (0 : Fin 2) q) 1 ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hr)
  have hpair : position (nuclearKSLift (0 : Fin 2) q) 0 ≠
      position (nuclearKSLift (0 : Fin 2) q) 1 :=
    sub_ne_zero.mp (norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hd))
  constructor
  · intro j hj
    fin_cases j
    · exact False.elim (hj rfl)
    · exact hother
  · intro j k hjk
    fin_cases j <;> fin_cases k
    · exact False.elim (hjk rfl)
    · exact hpair
    · exact hpair.symm
    · exact False.elim (hjk rfl)

theorem ksFixedChartRegion_image_norms
    {t0 : SpectatorConfiguration (0 : Fin 2)} (ht0 : ‖t0‖ = 1)
    {q : PairKSSpace} (hq : q ∈ ksFixedChartRegion t0) :
    ‖nuclearKSLift (0 : Fin 2) q‖ < 2 ∧ ‖pairKSLift q‖ < 2 := by
  have hy := ((ksFixedChartRegion_mem_iff t0 q).mp hq).1
  have ht := (ksFixedChartRegion_spectator_norm ht0 hq).2
  exact ⟨nuclearKSLift_norm_lt_two (0 : Fin 2) q hy ht,
    pairKSLift_norm_lt_two q hy ht⟩

theorem pairKSLift_zero_fiber_collision (t : SpectatorConfiguration (0 : Fin 2)) :
    position (pairKSLift ((0 : KSSpace),t)) 0 =
      position (pairKSLift ((0 : KSSpace),t)) 1 := by
  apply sub_eq_zero.mp
  rw [pairKSLift_difference]
  exact (ksMap_eq_zero_iff 0).mpr rfl

end TheoremT.Continuum
