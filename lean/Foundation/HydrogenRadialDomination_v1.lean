import HydrogenRadialBounds_v1
import HydrogenRadialLimits_v1

/-! Explicit L2 majorants for every first and mixed second hydrogen derivative.
The second-derivative majorant uses the directly proved Coulomb quotient L2,
not a hypothetical Sobolev membership of the radial exponential. -/
noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.Continuum

def hydrogenFirstMajorant (Z : ℝ) (x : Configuration 1) : ℝ :=
  Z * ‖hydrogenRadial Z x‖

def hydrogenSecondMajorant (Z : ℝ) (x : Configuration 1) : ℝ :=
  Z ^ 2 * ‖hydrogenRadial Z x‖ +
    2 * Z * ‖hydrogenRadial Z x / (‖x‖ : ℂ)‖

theorem hydrogenFirstMajorant_memLp {Z : ℝ} (hZ : 0 < Z) :
    MemLp (hydrogenFirstMajorant Z) 2 volume :=
  (hydrogenRadial_memLp hZ).norm.const_mul Z

theorem hydrogenSecondMajorant_memLp {Z : ℝ} (hZ : 0 < Z) :
    MemLp (hydrogenSecondMajorant Z) 2 volume :=
  ((hydrogenRadial_memLp hZ).norm.const_mul (Z ^ 2)).add
    ((hydrogenRadial_div_norm_memLp hZ).norm.const_mul (2 * Z))

theorem hydrogen_regularized_first_norm_le {Z δ : ℝ} (hZ : 0 ≤ Z) (hδ : 0 < δ)
    (k : Coordinate 1) (x : Configuration 1) :
    ‖hydrogenRegularizedFirst Z δ k x‖ ≤ hydrogenFirstMajorant Z x := by
  have hc := hydrogen_regularized_first_coefficient_bound x k hZ hδ
  have he := hydrogen_exp_regularized_le x hZ hδ.le
  simp only [hydrogenRegularizedFirst, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), hydrogenFirstMajorant, hydrogenRadial]
  exact mul_le_mul hc he (Real.exp_pos _).le hZ

theorem hydrogen_regularized_second_norm_le {Z δ : ℝ} (hZ : 0 ≤ Z) (hδ : 0 ≤ δ)
    (k l : Coordinate 1) {x : Configuration 1} (hx : x ≠ 0) :
    ‖hydrogenRegularizedSecond Z δ k l x‖ ≤ hydrogenSecondMajorant Z x := by
  have hc := hydrogen_regularized_second_coefficient_bound x k l hZ hδ hx
  have he := hydrogen_exp_regularized_le x hZ hδ
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hp : 0 ≤ Z ^ 2 + 2 * Z / ‖x‖ := by positivity
  calc
    _ ≤ (Z ^ 2 + 2 * Z / ‖x‖) * Real.exp (-Z * ‖x‖) := by
      simp only [hydrogenRegularizedSecond, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul hc he (Real.exp_pos _).le hp
    _ = _ := by
      simp only [hydrogenSecondMajorant, hydrogenRadial, norm_div, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_norm]
      ring

theorem hydrogen_first_memLp {Z : ℝ} (hZ : 0 < Z) (k : Coordinate 1) :
    MemLp (hydrogenFirst Z k) 2 volume := by
  apply (hydrogenFirstMajorant_memLp hZ).mono' ?_ ?_
  · apply Measurable.aestronglyMeasurable
    unfold hydrogenFirst hydrogenRadial
    fun_prop
  · filter_upwards [hydrogen_ae_ne_zero] with x hx
    apply le_of_tendsto (hydrogen_first_tendsto Z k hx).norm
    exact Eventually.of_forall (fun n =>
      hydrogen_regularized_first_norm_le hZ.le (hydrogenEpsilon_pos n) k x)

theorem hydrogen_second_memLp {Z : ℝ} (hZ : 0 < Z) (k l : Coordinate 1) :
    MemLp (hydrogenSecond Z k l) 2 volume := by
  apply (hydrogenSecondMajorant_memLp hZ).mono' ?_ ?_
  · apply Measurable.aestronglyMeasurable
    unfold hydrogenSecond hydrogenRadial
    fun_prop
  · filter_upwards [hydrogen_ae_ne_zero] with x hx
    apply le_of_tendsto (hydrogen_second_tendsto Z k l hx).norm
    exact Eventually.of_forall (fun n =>
      hydrogen_regularized_second_norm_le hZ.le (hydrogenEpsilon_pos n).le k l hx)

def hydrogenFirstL2 (Z : ℝ) (hZ : 0 < Z) (k : Coordinate 1) : SpatialL2 1 :=
  (hydrogen_first_memLp hZ k).toLp (hydrogenFirst Z k)

def hydrogenSecondL2 (Z : ℝ) (hZ : 0 < Z) (k l : Coordinate 1) : SpatialL2 1 :=
  (hydrogen_second_memLp hZ k l).toLp (hydrogenSecond Z k l)

#print axioms hydrogen_regularized_first_norm_le
#print axioms hydrogen_regularized_second_norm_le
#print axioms hydrogen_first_memLp
#print axioms hydrogen_second_memLp
end TheoremT.Continuum
