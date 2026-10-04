import CoulombKSPhysicalH12Data_v1
import KSCommonAnnulusPatchAll_v1

/-! The same finite physical initialization budgets for either selected
nuclear chart, with its own actual product-volume annulus. No identification
of different spectator domains or measures is assumed. -/
noncomputable section
open MeasureTheory
open scoped ContDiff NNReal
namespace TheoremT.Continuum
open WeakGrushin

def ksCommonAnnulusVolumeAt (i : Fin 2) : ℝ :=
  (volume (ksCommonAnnulusRegionAt i)).toReal

def ksH12SpectatorBudgetAt (i : Fin 2) (c C1 C2 KT : ℝ) : ℝ :=
  spectatorIterationBudgetSeq c (fun _ => 1) (fun _ => ksH12CutoffScalar c C1 C2)
    (fun _ => ksH12CutoffWeight c C1) (fun _ => 1) (fun _ => ksH12CutoffWeight c C1)
    KT (KT^2*ksCommonAnnulusVolumeAt i) (4*ksCommonAnnulusVolumeAt i) 12

def ksH12MixedBudgetAt (i : Fin 2) (c C1 C2 KT KY QY : ℝ) : ℝ :=
  mixedYIterationBudgetSeq c (fun _ => 1) (fun _ => ksH12CutoffScalar 0 C1 C2)
    (fun _ => ksH12CutoffWeight 0 C1) (fun _ => 1) (fun _ => ksH12CutoffWeight 0 C1)
    KY QY (KY^2*ksCommonAnnulusVolumeAt i) 12 3
    (ksH12SpectatorBudgetAt i c C1 C2 KT) 5

theorem ksCommonAnnulusVolumeAt_nonneg (i : Fin 2) :
    0 ≤ ksCommonAnnulusVolumeAt i := ENNReal.toReal_nonneg

theorem ksCommonAnnulusVolumeAt_mono (i : Fin 2) {S : Set (NuclearKSSpace i)}
    (hS : S ⊆ ksCommonAnnulusRegionAt i) :
    (volume S).toReal ≤ ksCommonAnnulusVolumeAt i :=
  ENNReal.toReal_mono (ksCommonAnnulusRegionAt_isCompact i).measure_lt_top.ne (measure_mono hS)

theorem ksH12SpectatorBudgetAt_nonneg (i : Fin 2) {c : ℝ} (hc : 0 < c)
    (C1 C2 KT : ℝ) (hKT : 0 ≤ KT) :
    0 ≤ ksH12SpectatorBudgetAt i c C1 C2 KT := by
  exact spectatorIterationBudgetSeq_nonneg c _ _ _ _ _ KT _ _ hc
    (fun _ => ksH12CutoffWeight_nonneg hc.le C1) (fun _ => by norm_num)
    (fun _ => ksH12CutoffWeight_nonneg hc.le C1) hKT
    (mul_nonneg (sq_nonneg _) (ksCommonAnnulusVolumeAt_nonneg i))
    (mul_nonneg (by norm_num) (ksCommonAnnulusVolumeAt_nonneg i)) 12

theorem ksH12MixedBudgetAt_nonneg (i : Fin 2) {c : ℝ} (hc : 0 < c)
    (C1 C2 KT KY QY : ℝ) (hKT : 0 ≤ KT) :
    0 ≤ ksH12MixedBudgetAt i c C1 C2 KT KY QY :=
  mixedYIterationBudgetSeq_nonneg c _ _ _ _ _ KY QY _ 12 3
    (ksH12SpectatorBudgetAt_nonneg i hc C1 C2 KT hKT) 5

theorem ksH12_source_amplitude_bound_at (i : Fin 2) (K : ℝ) (L : ℝ≥0) (z : ℂ)
    {S : Set (NuclearKSSpace i)} (hS : S ⊆ ksCommonAnnulusRegionAt i) :
    K^2*‖z‖^2*(volume S).toReal ≤
      ((L : ℝ)^2+‖z‖^2)*(K^2*ksCommonAnnulusVolumeAt i) := by
  have hvol := ksCommonAnnulusVolumeAt_mono i hS
  have hv := ksCommonAnnulusVolumeAt_nonneg i
  calc
    _ ≤ K^2*‖z‖^2*ksCommonAnnulusVolumeAt i := by gcongr
    _ ≤ K^2*((L : ℝ)^2+‖z‖^2)*ksCommonAnnulusVolumeAt i := by
      gcongr
      nlinarith [sq_nonneg (L : ℝ)]
    _ = _ := by ring

theorem ksH12_initial_amplitude_bound_at (i : Fin 2) (L : ℝ≥0) (z : ℂ) :
    (2*(L : ℝ))^2*ksCommonAnnulusVolumeAt i ≤
      ((L : ℝ)^2+‖z‖^2)*(4*ksCommonAnnulusVolumeAt i) := by
  have hv := ksCommonAnnulusVolumeAt_nonneg i
  have hh : 0 ≤ 4*‖z‖^2*ksCommonAnnulusVolumeAt i := by positivity
  nlinarith

theorem physicalH12Schedule_subset_commonAnnulusAt (i : Fin 2)
    {t0 : SpectatorConfiguration i} (ht0 : ‖t0‖ = 1) (start k : ℕ) :
    physicalH12ScheduleRegion i (twoElectronSpectatorPositionEquiv i t0) start k ⊆
      ksCommonAnnulusRegionAt i := by
  apply physicalH12ConcreteBox_subset_commonAnnulusAt i
  · simpa only [(twoElectronSpectatorPositionEquiv i).norm_map] using ht0
  · positivity

end TheoremT.Continuum
