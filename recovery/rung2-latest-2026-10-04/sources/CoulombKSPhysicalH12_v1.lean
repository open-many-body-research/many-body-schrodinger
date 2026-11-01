import CoulombKSPhysicalH12Data_v1
import CoulombKSScaledFiniteReserve_v1
import KSScaledFiveYReserve_v1
import ProductCoordinateWeakHk_v1

/-! Actual scalar Coulomb normalized differences have a full order-twelve
coordinate weak reserve on the fixed terminal physical box. All constants
are chosen on one common compact annulus before the unit spectator center,
representative, dilation and Lipschitz bound. The explicit budget retains
Lipschitz and origin-amplitude factors and asserts no C-infinity or factorial
estimate. Physical nuclear i=0 and pair KS coordinates are unchanged. -/
noncomputable section
open MeasureTheory Metric
open scoped ContDiff NNReal
namespace TheoremT.Continuum
open WeakGrushin

set_option maxHeartbeats 1600000 in
theorem scalar_coulomb_nuclear_zero_physical_coordinate_h12 (Z E C1 C2 : ℝ)
    (hC1 : ∀ x, |deriv Real.smoothTransition x| ≤ C1)
    (hC2 : ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ C2) :
    ∃ KT KY QY : ℝ, 1 ≤ KT ∧ 1 ≤ KY ∧ 0 ≤ QY ∧
      0 ≤ ksH12MixedBudget 4 C1 C2 KT KY QY ∧
      ∀ t0 : SpectatorConfiguration (0 : Fin 2), ‖t0‖ = 1 →
      ∀ f : SpatialL2 2, scalarHamiltonianGraph 2 Z f ((E : ℂ) • f) →
      ∀ g : Configuration 2 → ℂ, Continuous g → (f : Configuration 2 → ℂ) =ᵐ[volume] g →
      ∀ (L : ℝ≥0) (R ε : ℝ), LipschitzOnWith L g (ball 0 R) →
        0 < ε → ε ≤ min 1 (R/4) →
        ProductCoordinateWeakHk
          (physicalSpectatorReindex ⁻¹' rectangularOpenBox (0,pairCenterEquiv t0) (1/128) (1/128))
          (originScaledDifference g ε ∘ (nuclearKSLift (0 : Fin 2))) 12
          (((L : ℝ)^2+‖g 0‖^2)*ksH12MixedBudget 4 C1 C2 KT KY QY) := by
  have hbox : ∀ q ∈ ksCommonAnnulusRegion,
      ‖q.1‖ ≤ (1/4 : ℝ) ∧ ‖q.2‖ ≤ (5/4 : ℝ) := by
    intro q hq
    obtain ⟨hy,_,ht⟩ := (ksCommonAnnulusRegion_mem_iff q).mp hq
    exact ⟨hy,ht⟩
  obtain ⟨KT,hKT,hTgain⟩ := scalar_coulomb_nuclear_scaled_finite_reserve (0 : Fin 2) Z E
    ksCommonAnnulusRegion_isCompact ksCommonAnnulusRegion_subset_nuclear_patch hbox 12
  obtain ⟨KY,QY,hKY,hQY,hYgain⟩ := nuclearKS_scaled_five_y_reserve (0 : Fin 2) Z E
    ksCommonAnnulusRegion_isCompact ksCommonAnnulusRegion_subset_nuclear_patch
  have hKT0 : 0 ≤ KT := le_trans (by norm_num) hKT
  have hCT : 0 ≤ ksH12SpectatorBudget 4 C1 C2 KT :=
    ksH12SpectatorBudget_nonneg (by norm_num) C1 C2 KT hKT0
  have hCY : 0 ≤ ksH12MixedBudget 4 C1 C2 KT KY QY :=
    ksH12MixedBudget_nonneg (by norm_num) C1 C2 KT KY QY hKT0
  refine ⟨KT,KY,QY,hKT,hKY,hQY,hCY,?_⟩
  intro t0 ht0 f hgraph g hg hfg L R ε hLip hε hεlim
  have hε1 : ε ≤ 1 := hεlim.trans (min_le_left _ _)
  have hεR : ε ≤ R/4 := hεlim.trans (min_le_right _ _)
  have hR : 0 < R := by linarith
  let t := pairCenterEquiv t0
  let ΩT := physicalH12ScheduleRegion (0 : Fin 2) t 0
  let ΩY := physicalH12ScheduleRegion (0 : Fin 2) t 24
  let amp : ℝ := (L : ℝ)^2+‖g 0‖^2
  have hamp : 0 ≤ amp := by positivity
  have hTΩ : ΩT 0 ⊆ ksCommonAnnulusRegion := physicalH12Schedule_zero_subset_commonAnnulus ht0 0 0
  have hYΩ : ΩY 0 ⊆ ksCommonAnnulusRegion := physicalH12Schedule_zero_subset_commonAnnulus ht0 24 0
  have hwT : 0 ≤ ksH12CutoffWeight 4 C1 := ksH12CutoffWeight_nonneg (by norm_num) C1
  have hwY : 0 ≤ ksH12CutoffWeight 0 C1 := ksH12CutoffWeight_nonneg (by norm_num) C1
  obtain ⟨_hTr,hT⟩ := hTgain ΩT (physicalH12ScheduleMiddle (0 : Fin 2) t 0)
    (physicalH12ScheduleInnerCutoff (0 : Fin 2) t 0)
    (physicalH12ScheduleEnergyCutoff (0 : Fin 2) t 0)
    (fun _ => 1) (fun _ => ksH12CutoffScalar 4 C1 C2)
    (fun _ => ksH12CutoffWeight 4 C1) (fun _ => 1) (fun _ => ksH12CutoffWeight 4 C1)
    (physical_h12_T12_geometry (0 : Fin 2) t (by norm_num) hC1 hC2)
    (physicalH12ScheduleRegion_measurableSet (0 : Fin 2) t 0 0) hTΩ
    f hgraph g hg hfg L R ε hR hLip hε hε1 hεR
  have hTC : SpectatorFiniteState (ΩT 12) (originScaledDifference g ε ∘ (nuclearKSLift (0 : Fin 2))) 12
      (amp*ksH12SpectatorBudget 4 C1 C2 KT) := by
    apply hT.mono_budget
    exact spectatorIterationBudgetSeq_common_bound 4 _ _ _ _ _ KT (by norm_num)
      (ksH12_source_amplitude_bound KT L (g 0) hTΩ)
      (ksH12_initial_amplitude_bound L (g 0)) 12
      (fun _ _ => hwT) (fun _ _ => by norm_num) (fun _ _ => hwT)
  have hJoin : ΩT 12 = ΩY 0 := physicalH12Schedule_T12_Y5_join (0 : Fin 2) t
  rw [hJoin] at hTC
  have hEq : ∀ φ : PairKSSpace → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ ΩY 0 →
      (∫ p, splitGrushin 4 oscillatorBasis
        (epsilonNuclearKSPotential (0 : Fin 2) ε Z E) φ p •
          (originScaledDifference g ε ∘ (nuclearKSLift (0 : Fin 2))) p) =
      ∫ p, φ p • ((nuclearKSPotential (0 : Fin 2) Z (ε*E)) p • (-g 0)) := by
    intro φ hφ hc hs
    have he := (scalar_coulomb_epsilon_nuclear_KS_difference_weak (0 : Fin 2) hε hgraph hg hfg hφ hc
      (hs.trans (hYΩ.trans ksCommonAnnulusRegion_subset_nuclear_patch))).2.2
    have hBasis : (spectatorBasis : SpectatorCoordinate (0 : Fin 2) →
        SpectatorConfiguration (0 : Fin 2)) = oscillatorBasis := by
      funext j
      simp only [spectatorBasis,oscillatorBasis,EuclideanSpace.single,PiLp.single]
    rw [hBasis] at he
    simpa only [Function.comp_apply,Complex.real_smul,smul_neg,mul_neg] using he
  obtain ⟨_hYr,hY⟩ := hYgain ΩY (physicalH12ScheduleMiddle (0 : Fin 2) t 24)
    (physicalH12ScheduleInnerCutoff (0 : Fin 2) t 24)
    (physicalH12ScheduleEnergyCutoff (0 : Fin 2) t 24)
    (fun _ => 1) (fun _ => ksH12CutoffScalar 0 C1 C2)
    (fun _ => ksH12CutoffWeight 0 C1) (fun _ => 1) (fun _ => ksH12CutoffWeight 0 C1)
    (physical_h12_Y5_geometry (0 : Fin 2) t hC1 hC2)
    (fun k _ => physicalH12ScheduleRegion_isOpen (0 : Fin 2) t 24 (k+1)) hYΩ
    ε hε.le hε1 (g 0) (originScaledDifference g ε ∘ (nuclearKSLift (0 : Fin 2)))
    (amp*ksH12SpectatorBudget 4 C1 C2 KT) (mul_nonneg hamp hCT) hTC hEq
  rw [twoElectronSpectatorCoordinate_card] at hY
  have hYC : MixedTriangularState (ΩY 5) (originScaledDifference g ε ∘ (nuclearKSLift (0 : Fin 2))) 12 12
      (amp*ksH12MixedBudget 4 C1 C2 KT KY QY) := by
    apply hY.restrict Set.Subset.rfl
    exact mixedYIterationBudgetSeq_common_bound 4 _ _ _ _ _ KY QY 12 3 hamp
      (ksH12_source_amplitude_bound KY L (g 0) hYΩ) le_rfl 5
      (fun _ _ => hwY) (fun _ _ => by norm_num) (fun _ _ => hwY)
  have hEnd : ΩY 5 = physicalSpectatorReindex ⁻¹'
      rectangularOpenBox (0,pairCenterEquiv t0) (1/128) (1/128) := by
    simpa only [physicalSpectatorReindexAt_zero] using
      physicalH12Schedule_terminal (0 : Fin 2) t
  have hW := mixedTriangularState_coordinateWeakHk hYC
  rw [hEnd] at hW
  exact hW

set_option maxHeartbeats 1600000 in
theorem scalar_coulomb_pair_physical_coordinate_h12 (Z E C1 C2 : ℝ)
    (hC1 : ∀ x, |deriv Real.smoothTransition x| ≤ C1)
    (hC2 : ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ C2) :
    ∃ KT KY QY : ℝ, 1 ≤ KT ∧ 1 ≤ KY ∧ 0 ≤ QY ∧
      0 ≤ ksH12MixedBudget 1 C1 C2 KT KY QY ∧
      ∀ t0 : SpectatorConfiguration (0 : Fin 2), ‖t0‖ = 1 →
      ∀ f : SpatialL2 2, scalarHamiltonianGraph 2 Z f ((E : ℂ) • f) →
      ∀ g : Configuration 2 → ℂ, Continuous g → (f : Configuration 2 → ℂ) =ᵐ[volume] g →
      ∀ (L : ℝ≥0) (R ε : ℝ), LipschitzOnWith L g (ball 0 R) →
        0 < ε → ε ≤ min 1 (R/4) →
        ProductCoordinateWeakHk
          (physicalSpectatorReindex ⁻¹' rectangularOpenBox (0,pairCenterEquiv t0) (1/128) (1/128))
          (originScaledDifference g ε ∘ (pairKSLift)) 12
          (((L : ℝ)^2+‖g 0‖^2)*ksH12MixedBudget 1 C1 C2 KT KY QY) := by
  have hbox : ∀ q ∈ ksCommonAnnulusRegion,
      ‖q.1‖ ≤ (1/4 : ℝ) ∧ ‖q.2‖ ≤ (5/4 : ℝ) := by
    intro q hq
    obtain ⟨hy,_,ht⟩ := (ksCommonAnnulusRegion_mem_iff q).mp hq
    exact ⟨hy,ht⟩
  obtain ⟨KT,hKT,hTgain⟩ := scalar_coulomb_pair_scaled_finite_reserve Z E
    ksCommonAnnulusRegion_isCompact ksCommonAnnulusRegion_subset_pair_patch hbox 12
  obtain ⟨KY,QY,hKY,hQY,hYgain⟩ := pairKS_scaled_five_y_reserve Z E
    ksCommonAnnulusRegion_isCompact ksCommonAnnulusRegion_subset_pair_patch
  have hKT0 : 0 ≤ KT := le_trans (by norm_num) hKT
  have hCT : 0 ≤ ksH12SpectatorBudget 1 C1 C2 KT :=
    ksH12SpectatorBudget_nonneg (by norm_num) C1 C2 KT hKT0
  have hCY : 0 ≤ ksH12MixedBudget 1 C1 C2 KT KY QY :=
    ksH12MixedBudget_nonneg (by norm_num) C1 C2 KT KY QY hKT0
  refine ⟨KT,KY,QY,hKT,hKY,hQY,hCY,?_⟩
  intro t0 ht0 f hgraph g hg hfg L R ε hLip hε hεlim
  have hε1 : ε ≤ 1 := hεlim.trans (min_le_left _ _)
  have hεR : ε ≤ R/4 := hεlim.trans (min_le_right _ _)
  have hR : 0 < R := by linarith
  let t := pairCenterEquiv t0
  let ΩT := physicalH12ScheduleRegion (0 : Fin 2) t 0
  let ΩY := physicalH12ScheduleRegion (0 : Fin 2) t 24
  let amp : ℝ := (L : ℝ)^2+‖g 0‖^2
  have hamp : 0 ≤ amp := by positivity
  have hTΩ : ΩT 0 ⊆ ksCommonAnnulusRegion := physicalH12Schedule_zero_subset_commonAnnulus ht0 0 0
  have hYΩ : ΩY 0 ⊆ ksCommonAnnulusRegion := physicalH12Schedule_zero_subset_commonAnnulus ht0 24 0
  have hwT : 0 ≤ ksH12CutoffWeight 1 C1 := ksH12CutoffWeight_nonneg (by norm_num) C1
  have hwY : 0 ≤ ksH12CutoffWeight 0 C1 := ksH12CutoffWeight_nonneg (by norm_num) C1
  obtain ⟨_hTr,hT⟩ := hTgain ΩT (physicalH12ScheduleMiddle (0 : Fin 2) t 0)
    (physicalH12ScheduleInnerCutoff (0 : Fin 2) t 0)
    (physicalH12ScheduleEnergyCutoff (0 : Fin 2) t 0)
    (fun _ => 1) (fun _ => ksH12CutoffScalar 1 C1 C2)
    (fun _ => ksH12CutoffWeight 1 C1) (fun _ => 1) (fun _ => ksH12CutoffWeight 1 C1)
    (physical_h12_T12_geometry (0 : Fin 2) t (by norm_num) hC1 hC2)
    (physicalH12ScheduleRegion_measurableSet (0 : Fin 2) t 0 0) hTΩ
    f hgraph g hg hfg L R ε hR hLip hε hε1 hεR
  have hTC : SpectatorFiniteState (ΩT 12) (originScaledDifference g ε ∘ (pairKSLift)) 12
      (amp*ksH12SpectatorBudget 1 C1 C2 KT) := by
    apply hT.mono_budget
    exact spectatorIterationBudgetSeq_common_bound 1 _ _ _ _ _ KT (by norm_num)
      (ksH12_source_amplitude_bound KT L (g 0) hTΩ)
      (ksH12_initial_amplitude_bound L (g 0)) 12
      (fun _ _ => hwT) (fun _ _ => by norm_num) (fun _ _ => hwT)
  have hJoin : ΩT 12 = ΩY 0 := physicalH12Schedule_T12_Y5_join (0 : Fin 2) t
  rw [hJoin] at hTC
  have hEq : ∀ φ : PairKSSpace → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ ΩY 0 →
      (∫ p, splitGrushin 1 oscillatorBasis
        (epsilonPairKSPotential ε Z E) φ p •
          (originScaledDifference g ε ∘ (pairKSLift)) p) =
      ∫ p, φ p • ((pairKSPotential Z (ε*E)) p • (-g 0)) := by
    intro φ hφ hc hs
    have he := (scalar_coulomb_epsilon_pair_KS_difference_weak hε hgraph hg hfg hφ hc
      (hs.trans (hYΩ.trans ksCommonAnnulusRegion_subset_pair_patch))).2.2
    have hBasis : (spectatorBasis : SpectatorCoordinate (0 : Fin 2) →
        SpectatorConfiguration (0 : Fin 2)) = oscillatorBasis := by
      funext j
      simp only [spectatorBasis,oscillatorBasis,EuclideanSpace.single,PiLp.single]
    rw [hBasis] at he
    simpa only [Function.comp_apply,Complex.real_smul,smul_neg,mul_neg] using he
  obtain ⟨_hYr,hY⟩ := hYgain ΩY (physicalH12ScheduleMiddle (0 : Fin 2) t 24)
    (physicalH12ScheduleInnerCutoff (0 : Fin 2) t 24)
    (physicalH12ScheduleEnergyCutoff (0 : Fin 2) t 24)
    (fun _ => 1) (fun _ => ksH12CutoffScalar 0 C1 C2)
    (fun _ => ksH12CutoffWeight 0 C1) (fun _ => 1) (fun _ => ksH12CutoffWeight 0 C1)
    (physical_h12_Y5_geometry (0 : Fin 2) t hC1 hC2)
    (fun k _ => physicalH12ScheduleRegion_isOpen (0 : Fin 2) t 24 (k+1)) hYΩ
    ε hε.le hε1 (g 0) (originScaledDifference g ε ∘ (pairKSLift))
    (amp*ksH12SpectatorBudget 1 C1 C2 KT) (mul_nonneg hamp hCT) hTC hEq
  rw [twoElectronSpectatorCoordinate_card] at hY
  have hYC : MixedTriangularState (ΩY 5) (originScaledDifference g ε ∘ (pairKSLift)) 12 12
      (amp*ksH12MixedBudget 1 C1 C2 KT KY QY) := by
    apply hY.restrict Set.Subset.rfl
    exact mixedYIterationBudgetSeq_common_bound 1 _ _ _ _ _ KY QY 12 3 hamp
      (ksH12_source_amplitude_bound KY L (g 0) hYΩ) le_rfl 5
      (fun _ _ => hwY) (fun _ _ => by norm_num) (fun _ _ => hwY)
  have hEnd : ΩY 5 = physicalSpectatorReindex ⁻¹'
      rectangularOpenBox (0,pairCenterEquiv t0) (1/128) (1/128) := by
    simpa only [physicalSpectatorReindexAt_zero] using
      physicalH12Schedule_terminal (0 : Fin 2) t
  have hW := mixedTriangularState_coordinateWeakHk hYC
  rw [hEnd] at hW
  exact hW

#print axioms scalar_coulomb_nuclear_zero_physical_coordinate_h12
#print axioms scalar_coulomb_pair_physical_coordinate_h12
end TheoremT.Continuum
