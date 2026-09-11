import HydrogenSphereBilinear_v1

/-! The actual derivative of radial retraction to the sphere is the orthogonal
tangential projection. This identifies angular derivatives of polynomial
restrictions with their physical tangential gradients. -/
noncomputable section
open scoped BigOperators ContDiff RealInnerProductSpace
namespace TheoremT.HydrogenPolynomial

def unitRadialRetraction (x : AngularR3) : AngularR3 := ‖x‖⁻¹ • x

def angularRetraction (f : AngularR3 → ℝ) (x : AngularR3) : ℝ := f (unitRadialRetraction x)

def tangentialPartial (i : Fin 3) (f : AngularR3 → ℝ) (x : AngularR3) : ℝ :=
  euclideanPartial i f x - x i * fderiv ℝ f x x

theorem unitRadialRetraction_eq_radialSquaredPower (x : AngularR3) :
    unitRadialRetraction x = radialSquaredPower (-(1 : ℝ) / 2) x • x := by
  simpa only [Nat.cast_one, pow_one, unitRadialRetraction] using
    congrArg (fun r : ℝ => r • x) (radialSquaredPower_neg_half_nat 1 x).symm

theorem unitRadialRetraction_contDiffAt {x : AngularR3} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ unitRadialRetraction x := by
  have he : unitRadialRetraction = (fun y : AngularR3 => radialSquaredPower (-(1 : ℝ) / 2) y • y) :=
    funext unitRadialRetraction_eq_radialSquaredPower
  rw [he]
  exact (radialSquaredPower_contDiffAt _ hx).smul contDiffAt_id

theorem unitRadialRetraction_unit {x : AngularR3} (hx : ‖x‖ = 1) :
    unitRadialRetraction x = x := by simp [unitRadialRetraction, hx]

theorem unitRadialRetraction_norm {x : AngularR3} (hx : x ≠ 0) :
    ‖unitRadialRetraction x‖ = 1 := by
  simp [unitRadialRetraction, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg x), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

theorem unitRadialRetraction_fderiv_unit {x : AngularR3} (hx : ‖x‖ = 1) (v : AngularR3) :
    fderiv ℝ unitRadialRetraction x v = v - (inner ℝ x v) • x := by
  have hx0 : x ≠ 0 := by intro he; simp [he] at hx
  have hh := (radialSquaredPower_hasFDerivAt (-(1 : ℝ) / 2) hx0).smul (hasFDerivAt_id x)
  change HasFDerivAt (fun y : AngularR3 => radialSquaredPower (-(1 : ℝ) / 2) y • y) _ x at hh
  have he : unitRadialRetraction = (fun y : AngularR3 => radialSquaredPower (-(1 : ℝ) / 2) y • y) :=
    funext unitRadialRetraction_eq_radialSquaredPower
  rw [he, hh.fderiv]
  simp [radialSquaredPower, hx, sub_eq_add_neg, add_comm]
  module

theorem angularRetraction_fderiv_unit {f : AngularR3 → ℝ} {x : AngularR3}
    (hf : DifferentiableAt ℝ f x) (hx : ‖x‖ = 1) (v : AngularR3) :
    fderiv ℝ (angularRetraction f) x v = fderiv ℝ f x v - (inner ℝ x v) * fderiv ℝ f x x := by
  have hx0 : x ≠ 0 := by intro he; simp [he] at hx
  have hf' : DifferentiableAt ℝ f (unitRadialRetraction x) := by
    rw [unitRadialRetraction_unit hx]
    exact hf
  have hh := hf'.hasFDerivAt.comp x
    ((unitRadialRetraction_contDiffAt hx0).differentiableAt (by simp)).hasFDerivAt
  rw [unitRadialRetraction_unit hx] at hh
  change HasFDerivAt (angularRetraction f) _ x at hh
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.comp_apply, unitRadialRetraction_fderiv_unit hx,
    map_sub, map_smul, smul_eq_mul]

theorem angularRetraction_partial_unit {f : AngularR3 → ℝ} {x : AngularR3}
    (hf : DifferentiableAt ℝ f x) (hx : ‖x‖ = 1) (i : Fin 3) :
    euclideanPartial i (angularRetraction f) x = tangentialPartial i f x := by
  rw [euclideanPartial, angularRetraction_fderiv_unit hf hx]
  simp [tangentialPartial, euclideanPartial, EuclideanSpace.inner_single_right]

theorem angularRetraction_polynomial_smooth (P : MvPolynomial (Fin 3) ℝ) :
    SmoothAwayZero (angularRetraction (euclideanEvaluation P)) := by
  intro x hx
  exact (euclideanEvaluation_contDiff P).contDiffAt.comp x (unitRadialRetraction_contDiffAt hx)

end TheoremT.HydrogenPolynomial
