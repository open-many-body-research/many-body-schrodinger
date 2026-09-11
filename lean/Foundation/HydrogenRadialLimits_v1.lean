import HydrogenRadialLp_v1
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Actual pointwise limits of the regularized hydrogen derivative profiles.
The singular formulas are used only away from zero, a null configuration set.
They do not claim classical differentiability at the nucleus. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.Continuum

def hydrogenEpsilon (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem hydrogenEpsilon_pos (n : ℕ) : 0 < hydrogenEpsilon n := by
  unfold hydrogenEpsilon
  positivity

theorem hydrogenEpsilon_tendsto : Tendsto hydrogenEpsilon atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

def hydrogenFirst (Z : ℝ) (k : Coordinate 1) (x : Configuration 1) : ℂ :=
  ((-Z * x k / ‖x‖ : ℝ) : ℂ) * hydrogenRadial Z x

def hydrogenSecond (Z : ℝ) (k l : Coordinate 1) (x : Configuration 1) : ℂ :=
  ((Z ^ 2 * x k * x l / ‖x‖ ^ 2 - Z * (if k = l then 1 else 0) / ‖x‖ +
      Z * x k * x l / ‖x‖ ^ 3 : ℝ) : ℂ) * hydrogenRadial Z x

def hydrogenRegularizedFirst (Z δ : ℝ) (k : Coordinate 1) (x : Configuration 1) : ℂ :=
  ((-Z * x k / Real.sqrt (‖x‖ ^ 2 + δ) : ℝ) : ℂ) *
    (Real.exp (-Z * Real.sqrt (‖x‖ ^ 2 + δ)) : ℂ)

def hydrogenRegularizedSecond (Z δ : ℝ) (k l : Coordinate 1)
    (x : Configuration 1) : ℂ :=
  ((Z ^ 2 * x k * x l / (Real.sqrt (‖x‖ ^ 2 + δ)) ^ 2 -
      Z * (if k = l then 1 else 0) / Real.sqrt (‖x‖ ^ 2 + δ) +
      Z * x k * x l / (Real.sqrt (‖x‖ ^ 2 + δ)) ^ 3 : ℝ) : ℂ) *
    (Real.exp (-Z * Real.sqrt (‖x‖ ^ 2 + δ)) : ℂ)

theorem hydrogen_radius_tendsto (x : Configuration 1) :
    Tendsto (fun n => Real.sqrt (‖x‖ ^ 2 + hydrogenEpsilon n)) atTop (𝓝 ‖x‖) := by
  convert (tendsto_const_nhds.add hydrogenEpsilon_tendsto).sqrt using 1
  simp

theorem hydrogen_profile_tendsto (Z : ℝ) (x : Configuration 1) :
    Tendsto (fun n => (Real.exp (-Z * Real.sqrt (‖x‖ ^ 2 + hydrogenEpsilon n)) : ℂ))
      atTop (𝓝 (hydrogenRadial Z x)) := by
  exact Complex.continuous_ofReal.continuousAt.tendsto.comp
    (Real.continuous_exp.continuousAt.tendsto.comp ((hydrogen_radius_tendsto x).const_mul (-Z)))

theorem hydrogen_first_tendsto (Z : ℝ) (k : Coordinate 1) {x : Configuration 1}
    (hx : x ≠ 0) :
    Tendsto (fun n => hydrogenRegularizedFirst Z (hydrogenEpsilon n) k x)
      atTop (𝓝 (hydrogenFirst Z k x)) := by
  have hr := hydrogen_radius_tendsto x
  have hc := (tendsto_const_nhds.div hr (norm_ne_zero_iff.mpr hx) :
    Tendsto (fun n => -Z * x k / Real.sqrt (‖x‖ ^ 2 + hydrogenEpsilon n)) atTop
      (𝓝 (-Z * x k / ‖x‖)))
  exact (Complex.continuous_ofReal.continuousAt.tendsto.comp hc).mul
    (hydrogen_profile_tendsto Z x)

theorem hydrogen_second_tendsto (Z : ℝ) (k l : Coordinate 1) {x : Configuration 1}
    (hx : x ≠ 0) :
    Tendsto (fun n => hydrogenRegularizedSecond Z (hydrogenEpsilon n) k l x)
      atTop (𝓝 (hydrogenSecond Z k l x)) := by
  have hr := hydrogen_radius_tendsto x
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h1 := (tendsto_const_nhds.div (hr.pow 2) (pow_ne_zero 2 hn) :
    Tendsto (fun n => Z ^ 2 * x k * x l /
      (Real.sqrt (‖x‖ ^ 2 + hydrogenEpsilon n)) ^ 2) atTop
      (𝓝 (Z ^ 2 * x k * x l / ‖x‖ ^ 2)))
  have h2 := (tendsto_const_nhds.div hr hn :
    Tendsto (fun n => Z * (if k = l then 1 else 0) /
      Real.sqrt (‖x‖ ^ 2 + hydrogenEpsilon n)) atTop
      (𝓝 (Z * (if k = l then 1 else 0) / ‖x‖)))
  have h3 := (tendsto_const_nhds.div (hr.pow 3) (pow_ne_zero 3 hn) :
    Tendsto (fun n => Z * x k * x l /
      (Real.sqrt (‖x‖ ^ 2 + hydrogenEpsilon n)) ^ 3) atTop
      (𝓝 (Z * x k * x l / ‖x‖ ^ 3)))
  exact (Complex.continuous_ofReal.continuousAt.tendsto.comp ((h1.sub h2).add h3)).mul
    (hydrogen_profile_tendsto Z x)

theorem hydrogen_ae_ne_zero : ∀ᵐ x : Configuration 1 ∂volume, x ≠ 0 := by
  exact ae_iff.mpr (by simp)

#print axioms hydrogen_profile_tendsto
#print axioms hydrogen_first_tendsto
#print axioms hydrogen_second_tendsto
end TheoremT.Continuum
