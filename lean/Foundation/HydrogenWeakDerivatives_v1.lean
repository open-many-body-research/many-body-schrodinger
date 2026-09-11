import HydrogenRadialCalculus_v2
import HydrogenRadialDomination_v1
import ClassicalWeakLimit_v1

/-! The explicit hydrogen radial exponential inhabits the original weak H2
space, with every ordered mixed second weak derivative. The nucleus is handled
by dominated limits of globally smooth positive-radius regularizations. -/
noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

theorem hydrogenSmooth_derivative_profile {δ : ℝ} (hδ : 0 < δ) (Z : ℝ)
    (k : Coordinate 1) (x : Configuration 1) :
    fderiv ℝ (hydrogenSmooth Z δ) x (coordinateVector k) =
      hydrogenRegularizedFirst Z δ k x := by
  rw [hydrogenSmooth_first_derivative hδ]
  rfl

theorem hydrogenSmooth_second_profile {δ : ℝ} (hδ : 0 < δ) (Z : ℝ)
    (k l : Coordinate 1) (x : Configuration 1) :
    fderiv ℝ (fun y => fderiv ℝ (hydrogenSmooth Z δ) y (coordinateVector k))
      x (coordinateVector l) = hydrogenRegularizedSecond Z δ k l x := by
  rw [hydrogenSmooth_mixed_second_derivative hδ]
  simp only [hydrogenRegularizedSecond,
    Real.sq_sqrt (le_of_lt (hydrogenSmooth_denominator_pos hδ x)),
    hydrogenSmooth, hydrogenSmoothReal]

theorem hydrogen_first_weakPartial {Z : ℝ} (hZ : 0 < Z) (k : Coordinate 1) :
    WeakPartial (hydrogenRadialL2 Z hZ) (hydrogenFirstL2 Z hZ k) k := by
  apply weakPartial_of_classical_dominated_limit
    (u := fun n => hydrogenSmooth Z (hydrogenEpsilon n))
    (boundF := fun x => ‖hydrogenRadial Z x‖) (boundG := hydrogenFirstMajorant Z)
    (fun n => (hydrogenSmooth_contDiff (hydrogenEpsilon_pos n) Z).of_le (by norm_num))
    (hydrogenRadial_memLp hZ) (hydrogen_first_memLp hZ k)
    (hydrogenRadial_memLp hZ).norm (hydrogenFirstMajorant_memLp hZ)
  · intro n
    filter_upwards with x
    simp only [hydrogenSmooth, hydrogenSmoothReal, hydrogenRadial, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_norm]
    exact hydrogen_exp_regularized_le x hZ.le (hydrogenEpsilon_pos n).le
  · intro n
    filter_upwards with x
    rw [hydrogenSmooth_derivative_profile (hydrogenEpsilon_pos n)]
    exact (hydrogen_regularized_first_norm_le hZ.le (hydrogenEpsilon_pos n) k x).trans
      (le_abs_self _)
  · exact Eventually.of_forall (hydrogen_profile_tendsto Z)
  · filter_upwards [hydrogen_ae_ne_zero] with x hx
    simpa only [hydrogenSmooth_derivative_profile (hydrogenEpsilon_pos _)] using
      hydrogen_first_tendsto Z k hx

theorem hydrogen_second_weakPartial {Z : ℝ} (hZ : 0 < Z) (k l : Coordinate 1) :
    WeakPartial (hydrogenFirstL2 Z hZ k) (hydrogenSecondL2 Z hZ k l) l := by
  apply weakPartial_of_classical_dominated_limit
    (u := fun n x => fderiv ℝ (hydrogenSmooth Z (hydrogenEpsilon n)) x (coordinateVector k))
    (boundF := hydrogenFirstMajorant Z) (boundG := hydrogenSecondMajorant Z)
    (fun n => (hydrogenSmooth_first_contDiff (hydrogenEpsilon_pos n) Z k).of_le (by norm_num))
    (hydrogen_first_memLp hZ k) (hydrogen_second_memLp hZ k l)
    (hydrogenFirstMajorant_memLp hZ) (hydrogenSecondMajorant_memLp hZ)
  · intro n
    filter_upwards with x
    rw [hydrogenSmooth_derivative_profile (hydrogenEpsilon_pos n)]
    exact (hydrogen_regularized_first_norm_le hZ.le (hydrogenEpsilon_pos n) k x).trans
      (le_abs_self _)
  · intro n
    filter_upwards [hydrogen_ae_ne_zero] with x hx
    rw [hydrogenSmooth_second_profile (hydrogenEpsilon_pos n)]
    exact (hydrogen_regularized_second_norm_le hZ.le (hydrogenEpsilon_pos n).le k l hx).trans
      (le_abs_self _)
  · filter_upwards [hydrogen_ae_ne_zero] with x hx
    simpa only [hydrogenSmooth_derivative_profile (hydrogenEpsilon_pos _)] using
      hydrogen_first_tendsto Z k hx
  · filter_upwards [hydrogen_ae_ne_zero] with x hx
    simpa only [hydrogenSmooth_second_profile (hydrogenEpsilon_pos _)] using
      hydrogen_second_tendsto Z k l hx

theorem hydrogenRadialL2_hasH2 {Z : ℝ} (hZ : 0 < Z) : HasH2 (hydrogenRadialL2 Z hZ) :=
  ⟨hydrogenFirstL2 Z hZ, hydrogen_first_weakPartial hZ,
    fun k l => ⟨hydrogenSecondL2 Z hZ k l, hydrogen_second_weakPartial hZ k l⟩⟩

#print axioms hydrogen_first_weakPartial
#print axioms hydrogen_second_weakPartial
#print axioms hydrogenRadialL2_hasH2
end TheoremT.Continuum
