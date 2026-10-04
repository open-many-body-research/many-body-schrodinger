import PhysicalH12ConcreteStepGeometry_v1

/-! The actual twelve spectator stages followed by five spatial stages.
These geometry arrays use the real selected-electron spectator index for
either i : Fin 2. The spatial stages have cutoff parameter zero, independently
of the physical coefficient retained in the PDE and its iteration budget. -/
noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin

def physicalH12ScheduleRegion (i : Fin 2) (t : EuclideanSpace ℝ (Fin 3))
    (start k : ℕ) : Set (Space (SpectatorCoordinate i)) :=
  physicalH12ConcreteBox i t (start+2*k : ℕ)

def physicalH12ScheduleMiddle (i : Fin 2) (t : EuclideanSpace ℝ (Fin 3))
    (start k : ℕ) : Set (Space (SpectatorCoordinate i)) :=
  physicalH12ConcreteBox i t (start+2*k+1 : ℕ)

def physicalH12ScheduleInnerCutoff (i : Fin 2) (t : EuclideanSpace ℝ (Fin 3))
    (start k : ℕ) : Space (SpectatorCoordinate i) → ℝ :=
  physicalH12ConcreteInnerCutoff i t (start+2*k : ℕ)

def physicalH12ScheduleEnergyCutoff (i : Fin 2) (t : EuclideanSpace ℝ (Fin 3))
    (start k : ℕ) : Space (SpectatorCoordinate i) → ℝ :=
  physicalH12ConcreteEnergyCutoff i t (start+2*k : ℕ)

theorem physicalH12ScheduleRegion_isOpen (i : Fin 2)
    (t : EuclideanSpace ℝ (Fin 3)) (start k : ℕ) :
    IsOpen (physicalH12ScheduleRegion i t start k) :=
  physicalH12ConcreteBox_isOpen i t _

theorem physicalH12ScheduleRegion_measurableSet (i : Fin 2)
    (t : EuclideanSpace ℝ (Fin 3)) (start k : ℕ) :
    MeasurableSet (physicalH12ScheduleRegion i t start k) :=
  (physicalH12ScheduleRegion_isOpen i t start k).measurableSet

theorem physicalH12ScheduleRegion_antitone (i : Fin 2)
    (t : EuclideanSpace ℝ (Fin 3)) (start : ℕ) :
    Antitone (physicalH12ScheduleRegion i t start) := by
  intro k l hkl
  apply physicalH12ConcreteBox_antitone i t
  exact_mod_cast (show start+2*k ≤ start+2*l by omega)

theorem physicalH12ScheduleRegion_subset_initial (i : Fin 2)
    (t : EuclideanSpace ℝ (Fin 3)) (start k : ℕ) :
    physicalH12ScheduleRegion i t start k ⊆ physicalH12ConcreteBox i t 0 := by
  apply physicalH12ConcreteBox_antitone i t
  exact Nat.cast_nonneg _

theorem physical_h12_schedule_geometry (i : Fin 2)
    (t : EuclideanSpace ℝ (Fin 3)) (start n : ℕ) {c C1 C2 : ℝ}
    (hc : 0 ≤ c) (hLast : start+2*n ≤ 34)
    (hC1 : ∀ x, |deriv Real.smoothTransition x| ≤ C1)
    (hC2 : ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ C2) :
    ∀ k, k < n → SpectatorStepGeometry c
      (physicalH12ScheduleRegion i t start k) (physicalH12ScheduleRegion i t start (k+1))
      (physicalH12ScheduleMiddle i t start k)
      (physicalH12ScheduleInnerCutoff i t start k) (physicalH12ScheduleEnergyCutoff i t start k)
      1 (h12CutoffScalarBound c (1/32) C1 C2 h12ConcreteDelta)
      (h12CutoffWeightBound c (1/32) C1 h12ConcreteDelta)
      1 (h12CutoffWeightBound c (1/32) C1 h12ConcreteDelta) := by
  intro k hk
  have hj : (start+2*k : ℕ) ≤ 32 := by omega
  have h := physical_h12_concrete_step_geometry i t hc
    (Nat.cast_nonneg (start+2*k)) (by exact_mod_cast hj) hC1 hC2
  have he : start+2*(k+1) = start+2*k+2 := by omega
  simpa [physicalH12ScheduleRegion,physicalH12ScheduleMiddle,
    physicalH12ScheduleInnerCutoff,physicalH12ScheduleEnergyCutoff,he,Nat.cast_add] using h

theorem physical_h12_T12_geometry (i : Fin 2) (t : EuclideanSpace ℝ (Fin 3))
    {c C1 C2 : ℝ} (hc : 0 ≤ c)
    (hC1 : ∀ x, |deriv Real.smoothTransition x| ≤ C1)
    (hC2 : ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ C2) :
    ∀ k, k < 12 → SpectatorStepGeometry c
      (physicalH12ScheduleRegion i t 0 k) (physicalH12ScheduleRegion i t 0 (k+1))
      (physicalH12ScheduleMiddle i t 0 k)
      (physicalH12ScheduleInnerCutoff i t 0 k) (physicalH12ScheduleEnergyCutoff i t 0 k)
      1 (h12CutoffScalarBound c (1/32) C1 C2 h12ConcreteDelta)
      (h12CutoffWeightBound c (1/32) C1 h12ConcreteDelta)
      1 (h12CutoffWeightBound c (1/32) C1 h12ConcreteDelta) :=
  physical_h12_schedule_geometry i t 0 12 hc (by norm_num) hC1 hC2

theorem physical_h12_Y5_geometry (i : Fin 2) (t : EuclideanSpace ℝ (Fin 3))
    {C1 C2 : ℝ}
    (hC1 : ∀ x, |deriv Real.smoothTransition x| ≤ C1)
    (hC2 : ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ C2) :
    ∀ k, k < 5 → SpectatorStepGeometry 0
      (physicalH12ScheduleRegion i t 24 k) (physicalH12ScheduleRegion i t 24 (k+1))
      (physicalH12ScheduleMiddle i t 24 k)
      (physicalH12ScheduleInnerCutoff i t 24 k) (physicalH12ScheduleEnergyCutoff i t 24 k)
      1 (h12CutoffScalarBound 0 (1/32) C1 C2 h12ConcreteDelta)
      (h12CutoffWeightBound 0 (1/32) C1 h12ConcreteDelta)
      1 (h12CutoffWeightBound 0 (1/32) C1 h12ConcreteDelta) :=
  physical_h12_schedule_geometry i t 24 5 (by norm_num) (by norm_num) hC1 hC2

theorem physicalH12Schedule_T12_Y5_join (i : Fin 2) (t : EuclideanSpace ℝ (Fin 3)) :
    physicalH12ScheduleRegion i t 0 12 = physicalH12ScheduleRegion i t 24 0 := by
  norm_num [physicalH12ScheduleRegion]

theorem physicalH12Schedule_initial (i : Fin 2) (t : EuclideanSpace ℝ (Fin 3)) :
    physicalH12ScheduleRegion i t 0 0 = physicalSpectatorReindexAt i ⁻¹'
      rectangularOpenBox (0,t) (1/64) (1/64) := by
  simpa only [physicalH12ScheduleRegion,Nat.mul_zero,Nat.add_zero,Nat.cast_zero] using
    physicalH12ConcreteBox_zero i t

theorem physicalH12Schedule_terminal (i : Fin 2) (t : EuclideanSpace ℝ (Fin 3)) :
    physicalH12ScheduleRegion i t 24 5 = physicalSpectatorReindexAt i ⁻¹'
      rectangularOpenBox (0,t) (1/128) (1/128) := by
  norm_num only [physicalH12ScheduleRegion,show (24+2*5 : ℕ)=34 by norm_num]
  exact physicalH12ConcreteBox_34 i t

#print axioms physical_h12_T12_geometry
#print axioms physical_h12_Y5_geometry
#print axioms physicalH12Schedule_terminal
end TheoremT.Continuum.WeakGrushin
