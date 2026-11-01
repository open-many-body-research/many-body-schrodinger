import KSCommonAnnulusPatch_v1
import PhysicalFixedChartBoxInclusion_v1
import PhysicalH12IterationSchedule_v1
import SpectatorFiniteStateBudget_v1
import MixedYIterationBudgetScale_v1

/-! Fixed physical initialization data and explicit composed norm budgets.
The compact annulus and all cutoff constants are independent of the unit
spectator center. The amplitude factor keeps the actual Lipschitz constant
and origin value visible. No computational evaluation of the finite
coefficient constants is asserted. -/
noncomputable section
open MeasureTheory
open scoped ContDiff NNReal
namespace TheoremT.Continuum
open WeakGrushin

def ksCommonAnnulusVolume : ℝ := (volume ksCommonAnnulusRegion).toReal

def ksH12CutoffScalar (c C1 C2 : ℝ) : ℝ :=
  h12CutoffScalarBound c (1/32) C1 C2 h12ConcreteDelta

def ksH12CutoffWeight (c C1 : ℝ) : ℝ :=
  h12CutoffWeightBound c (1/32) C1 h12ConcreteDelta

def ksH12SpectatorBudget (c C1 C2 KT : ℝ) : ℝ :=
  spectatorIterationBudgetSeq c (fun _ => 1) (fun _ => ksH12CutoffScalar c C1 C2)
    (fun _ => ksH12CutoffWeight c C1) (fun _ => 1) (fun _ => ksH12CutoffWeight c C1)
    KT (KT^2*ksCommonAnnulusVolume) (4*ksCommonAnnulusVolume) 12

def ksH12MixedBudget (c C1 C2 KT KY QY : ℝ) : ℝ :=
  mixedYIterationBudgetSeq c (fun _ => 1) (fun _ => ksH12CutoffScalar 0 C1 C2)
    (fun _ => ksH12CutoffWeight 0 C1) (fun _ => 1) (fun _ => ksH12CutoffWeight 0 C1)
    KY QY (KY^2*ksCommonAnnulusVolume) 12 3 (ksH12SpectatorBudget c C1 C2 KT) 5

theorem ksCommonAnnulusVolume_nonneg : 0 ≤ ksCommonAnnulusVolume := ENNReal.toReal_nonneg

theorem ksCommonAnnulusVolume_mono {S : Set PairKSSpace} (hS : S ⊆ ksCommonAnnulusRegion) :
    (volume S).toReal ≤ ksCommonAnnulusVolume :=
  ENNReal.toReal_mono ksCommonAnnulusRegion_isCompact.measure_lt_top.ne (measure_mono hS)

theorem ksH12CutoffWeight_nonneg {c : ℝ} (hc : 0 ≤ c) (C1 : ℝ) :
    0 ≤ ksH12CutoffWeight c C1 :=
  h12CutoffWeightBound_nonneg hc _ _ _

theorem ksH12SpectatorBudget_nonneg {c : ℝ} (hc : 0 < c) (C1 C2 KT : ℝ) (hKT : 0 ≤ KT) :
    0 ≤ ksH12SpectatorBudget c C1 C2 KT := by
  exact spectatorIterationBudgetSeq_nonneg c _ _ _ _ _ KT _ _ hc
    (fun _ => ksH12CutoffWeight_nonneg hc.le C1) (fun _ => by norm_num)
    (fun _ => ksH12CutoffWeight_nonneg hc.le C1) hKT
    (mul_nonneg (sq_nonneg _) ksCommonAnnulusVolume_nonneg)
    (mul_nonneg (by norm_num) ksCommonAnnulusVolume_nonneg) 12

theorem ksH12MixedBudget_nonneg {c : ℝ} (hc : 0 < c) (C1 C2 KT KY QY : ℝ) (hKT : 0 ≤ KT) :
    0 ≤ ksH12MixedBudget c C1 C2 KT KY QY :=
  mixedYIterationBudgetSeq_nonneg c _ _ _ _ _ KY QY _ 12 3
    (ksH12SpectatorBudget_nonneg hc C1 C2 KT hKT) 5

theorem ksH12_source_amplitude_bound (K : ℝ) (L : ℝ≥0) (z : ℂ)
    {S : Set PairKSSpace} (hS : S ⊆ ksCommonAnnulusRegion) :
    K^2*‖z‖^2*(volume S).toReal ≤ ((L : ℝ)^2+‖z‖^2)*(K^2*ksCommonAnnulusVolume) := by
  have hvol := ksCommonAnnulusVolume_mono hS
  have hv := ksCommonAnnulusVolume_nonneg
  calc
    _ ≤ K^2*‖z‖^2*ksCommonAnnulusVolume := by gcongr
    _ ≤ K^2*((L : ℝ)^2+‖z‖^2)*ksCommonAnnulusVolume := by gcongr; nlinarith [sq_nonneg (L : ℝ)]
    _ = _ := by ring

theorem ksH12_initial_amplitude_bound (L : ℝ≥0) (z : ℂ) :
    (2*(L : ℝ))^2*ksCommonAnnulusVolume ≤
      ((L : ℝ)^2+‖z‖^2)*(4*ksCommonAnnulusVolume) := by
  have hv := ksCommonAnnulusVolume_nonneg
  have hh : 0 ≤ 4*‖z‖^2*ksCommonAnnulusVolume := by positivity
  nlinarith

theorem physicalH12Schedule_zero_subset_commonAnnulus
    {t0 : SpectatorConfiguration (0 : Fin 2)} (ht0 : ‖t0‖ = 1) (start k : ℕ) :
    physicalH12ScheduleRegion (0 : Fin 2) (pairCenterEquiv t0) start k ⊆ ksCommonAnnulusRegion := by
  apply (physicalH12ScheduleRegion_subset_initial (0 : Fin 2) (pairCenterEquiv t0) start k).trans
  rw [physicalH12ConcreteBox_zero,physicalSpectatorReindexAt_zero]
  exact (physical_rectangularOpenBox_subset_fixed_chart t0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans
      (ksFixedChartRegion_subset_commonAnnulus ht0)

#print axioms ksCommonAnnulusVolume_nonneg
#print axioms ksCommonAnnulusVolume_mono
#print axioms ksH12CutoffWeight_nonneg
#print axioms ksH12SpectatorBudget_nonneg
#print axioms ksH12MixedBudget_nonneg
#print axioms ksH12_source_amplitude_bound
#print axioms ksH12_initial_amplitude_bound
#print axioms physicalH12Schedule_zero_subset_commonAnnulus
end TheoremT.Continuum
