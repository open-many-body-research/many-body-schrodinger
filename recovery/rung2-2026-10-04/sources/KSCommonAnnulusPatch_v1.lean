import KSFixedChartPatch_v1

/-! One fixed compact coefficient region for all unit spectator centers.
It uses the exact existing two-electron KS lifts and spectator configuration.
The KS zero fiber remains included; only the spectator norm is bounded below.
-/
noncomputable section
namespace TheoremT.Continuum

def ksCommonAnnulusRegion : Set PairKSSpace :=
  Metric.closedBall (0 : KSSpace) (1/4 : ℝ) ×ˢ
    (Metric.closedBall (0 : SpectatorConfiguration (0 : Fin 2)) (5/4 : ℝ) ∩
      {t | (3/4 : ℝ) ≤ ‖t‖})

theorem ksCommonAnnulusRegion_mem_iff (q : PairKSSpace) :
    q ∈ ksCommonAnnulusRegion ↔
      ‖q.1‖ ≤ (1/4 : ℝ) ∧ (3/4 : ℝ) ≤ ‖q.2‖ ∧ ‖q.2‖ ≤ (5/4 : ℝ) := by
  simp [ksCommonAnnulusRegion, Metric.mem_closedBall, dist_eq_norm, and_comm, and_left_comm]

theorem ksCommonAnnulusRegion_isCompact : IsCompact ksCommonAnnulusRegion :=
  (isCompact_closedBall (0 : KSSpace) (1/4 : ℝ)).prod
    ((isCompact_closedBall (0 : SpectatorConfiguration (0 : Fin 2)) (5/4 : ℝ)).inter_right
      (isClosed_le continuous_const continuous_norm))

theorem ksFixedChartRegion_subset_commonAnnulus
    {t0 : SpectatorConfiguration (0 : Fin 2)} (ht0 : ‖t0‖ = 1) :
    ksFixedChartRegion t0 ⊆ ksCommonAnnulusRegion := by
  intro q hq
  exact (ksCommonAnnulusRegion_mem_iff q).mpr
    ⟨((ksFixedChartRegion_mem_iff t0 q).mp hq).1,
      ksFixedChartRegion_spectator_norm ht0 hq⟩

theorem ksCommonAnnulusRegion_zero_center_mem
    {t0 : SpectatorConfiguration (0 : Fin 2)} (ht0 : ‖t0‖ = 1) :
    ((0 : KSSpace),t0) ∈ ksCommonAnnulusRegion :=
  ksFixedChartRegion_subset_commonAnnulus ht0 (ksFixedChartRegion_center_mem t0)

theorem ksCommonAnnulusRegion_ks_radius
    {q : PairKSSpace} (hq : q ∈ ksCommonAnnulusRegion) :
    ‖ksMap q.1‖ ≤ (1/16 : ℝ) := by
  have hy := ((ksCommonAnnulusRegion_mem_iff q).mp hq).1
  calc
    ‖ksMap q.1‖ = ‖q.1‖^2 := ksMap_norm _
    _ ≤ (1/4 : ℝ)^2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
    _ = (1/16 : ℝ) := by norm_num

theorem ksCommonAnnulusRegion_pair_nuclear_radii
    {q : PairKSSpace} (hq : q ∈ ksCommonAnnulusRegion) :
    (23/32 : ℝ) ≤ ‖position (pairKSLift q) 0‖ ∧
    (23/32 : ℝ) ≤ ‖position (pairKSLift q) 1‖ := by
  have ht := ((ksCommonAnnulusRegion_mem_iff q).mp hq).2.1
  have hy := ksCommonAnnulusRegion_ks_radius hq
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

theorem ksCommonAnnulusRegion_subset_pair_patch :
    ksCommonAnnulusRegion ⊆ pairKSCoefficientPatch := by
  intro q hq
  obtain ⟨h0,h1⟩ := ksCommonAnnulusRegion_pair_nuclear_radii hq
  exact ⟨norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) h0),
    norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) h1)⟩

theorem ksCommonAnnulusRegion_nuclear_other_radius
    {q : NuclearKSSpace (0 : Fin 2)} (hq : q ∈ ksCommonAnnulusRegion) :
    (3/4 : ℝ) ≤ ‖position (nuclearKSLift (0 : Fin 2) q) 1‖ := by
  rw [nuclearKSLift_zero_other_position, pairCenterEquiv.norm_map]
  exact ((ksCommonAnnulusRegion_mem_iff q).mp hq).2.1

theorem ksCommonAnnulusRegion_nuclear_pair_radius
    {q : NuclearKSSpace (0 : Fin 2)} (hq : q ∈ ksCommonAnnulusRegion) :
    (11/16 : ℝ) ≤ ‖position (nuclearKSLift (0 : Fin 2) q) 0 -
      position (nuclearKSLift (0 : Fin 2) q) 1‖ := by
  have ht := ((ksCommonAnnulusRegion_mem_iff q).mp hq).2.1
  have hy := ksCommonAnnulusRegion_ks_radius hq
  have hn := norm_sub_norm_le (pairCenterEquiv q.2) (ksMap q.1)
  rw [pairCenterEquiv.norm_map] at hn
  rw [nuclearKSLift_selected_position, nuclearKSLift_zero_other_position, norm_sub_rev]
  linarith

theorem ksCommonAnnulusRegion_subset_nuclear_patch :
    ksCommonAnnulusRegion ⊆ nuclearKSCoefficientPatch (0 : Fin 2) := by
  intro q hq
  have hr := ksCommonAnnulusRegion_nuclear_other_radius hq
  have hd := ksCommonAnnulusRegion_nuclear_pair_radius hq
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

theorem ksCommonAnnulusRegion_image_norms
    {q : PairKSSpace} (hq : q ∈ ksCommonAnnulusRegion) :
    ‖nuclearKSLift (0 : Fin 2) q‖ < 2 ∧ ‖pairKSLift q‖ < 2 := by
  obtain ⟨hy, _, ht⟩ := (ksCommonAnnulusRegion_mem_iff q).mp hq
  exact ⟨nuclearKSLift_norm_lt_two (0 : Fin 2) q hy ht,
    pairKSLift_norm_lt_two q hy ht⟩

end TheoremT.Continuum
