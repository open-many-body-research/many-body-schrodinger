import PhysicalSpectatorStepGeometryAll_v1
import GrushinH12ConcreteScheduleArithmetic_v1

/-! Concrete width-1/64 to width-1/128 cutoff geometry, in either actual
two-electron selected spectator space. One step consumes two of the 34 gaps.
The spatial center is zero, so the uniform Y radius is exactly 1/32. -/
noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin

def physicalH12ConcreteBox (i : Fin 2) (t : EuclideanSpace ℝ (Fin 3)) (j : ℝ) :
    Set (Space (SpectatorCoordinate i)) :=
  physicalSpectatorReindexAt i ⁻¹' h12ConcreteBox (0,t) j

def physicalH12ConcreteInnerCutoff (i : Fin 2) (t : EuclideanSpace ℝ (Fin 3))
    (j : ℝ) : Space (SpectatorCoordinate i) → ℝ :=
  h12InnerCutoff (0,t) (h12ConcreteRadius j) (h12ConcreteRadius j) h12ConcreteDelta ∘
    physicalSpectatorReindexAt i

def physicalH12ConcreteEnergyCutoff (i : Fin 2) (t : EuclideanSpace ℝ (Fin 3))
    (j : ℝ) : Space (SpectatorCoordinate i) → ℝ :=
  h12EnergyCutoff (0,t) (h12ConcreteRadius j) (h12ConcreteRadius j) h12ConcreteDelta ∘
    physicalSpectatorReindexAt i

theorem physicalH12ConcreteBox_isOpen (i : Fin 2) (t : EuclideanSpace ℝ (Fin 3))
    (j : ℝ) : IsOpen (physicalH12ConcreteBox i t j) :=
  (h12ConcreteBox_isOpen (0,t) j).preimage (physicalSpectatorReindexAt i).continuous

theorem physicalH12ConcreteBox_measurableSet (i : Fin 2)
    (t : EuclideanSpace ℝ (Fin 3)) (j : ℝ) :
    MeasurableSet (physicalH12ConcreteBox i t j) :=
  (physicalH12ConcreteBox_isOpen i t j).measurableSet

theorem physicalH12ConcreteBox_antitone (i : Fin 2) (t : EuclideanSpace ℝ (Fin 3)) :
    Antitone (physicalH12ConcreteBox i t) := by
  intro j k hjk
  exact Set.preimage_mono (h12ConcreteBox_antitone (0,t) hjk)

theorem physicalH12ConcreteBox_zero (i : Fin 2) (t : EuclideanSpace ℝ (Fin 3)) :
    physicalH12ConcreteBox i t 0 = physicalSpectatorReindexAt i ⁻¹'
      rectangularOpenBox (0,t) (1/64) (1/64) := by
  simp only [physicalH12ConcreteBox,h12ConcreteBox_eq_rectangularOpenBox,
    h12ConcreteRadius_zero]

theorem physicalH12ConcreteBox_34 (i : Fin 2) (t : EuclideanSpace ℝ (Fin 3)) :
    physicalH12ConcreteBox i t 34 = physicalSpectatorReindexAt i ⁻¹'
      rectangularOpenBox (0,t) (1/128) (1/128) := by
  simp only [physicalH12ConcreteBox,h12ConcreteBox_eq_rectangularOpenBox,
    h12ConcreteRadius_34]

theorem physical_h12_concrete_step_geometry (i : Fin 2)
    (t : EuclideanSpace ℝ (Fin 3)) {c C1 C2 j : ℝ}
    (hc : 0 ≤ c) (hj0 : 0 ≤ j) (hj : j ≤ 32)
    (hC1 : ∀ x, |deriv Real.smoothTransition x| ≤ C1)
    (hC2 : ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ C2) :
    SpectatorStepGeometry c (physicalH12ConcreteBox i t j)
      (physicalH12ConcreteBox i t (j+2)) (physicalH12ConcreteBox i t (j+1))
      (physicalH12ConcreteInnerCutoff i t j) (physicalH12ConcreteEnergyCutoff i t j)
      1 (h12CutoffScalarBound c (1/32) C1 C2 h12ConcreteDelta)
      (h12CutoffWeightBound c (1/32) C1 h12ConcreteDelta)
      1 (h12CutoffWeightBound c (1/32) C1 h12ConcreteDelta) := by
  have hS : ‖((0,t) : Space (Fin 3)).1‖+2*h12ConcreteRadius j ≤ (1/32 : ℝ) := by
    have h := h12ConcreteRadius_le_outer hj0
    simp only [norm_zero,zero_add]
    linarith
  have h := physical_h12_spectatorStepGeometryAt i (0,t) hc h12ConcreteDelta_pos
    (h12ConcreteRadius_two_gap hj) (h12ConcreteRadius_two_gap hj) hC1 hC2 hS
  simpa only [physicalH12ConcreteBox,h12ConcreteBox_eq_rectangularOpenBox,
    h12ConcreteRadius_add_two,h12ConcreteRadius_add_one,
    physicalH12ConcreteInnerCutoff,physicalH12ConcreteEnergyCutoff] using h

#print axioms physical_h12_concrete_step_geometry
end TheoremT.Continuum.WeakGrushin
