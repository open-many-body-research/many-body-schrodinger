import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Real scalar reconstruction algebra for the pair-distance map.
Triangle inequalities imply a nonnegative transverse square. The axis
coordinate is the literal quotient and the displayed reconstruction
identities do not assume the desired distances or choose a square root. -/
set_option autoImplicit false
noncomputable section
namespace TheoremT.Continuum

theorem pair_distance_heron_factorization (r s u : ℝ) :
    4*((r^2+s^2)/2-u^2/4)*u^2-(r^2-s^2)^2 =
      ((r+s)^2-u^2)*(u^2-(r-s)^2) := by ring

theorem pair_distance_heron_nonneg {r s u : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hu : 0 ≤ u)
    (hlow : |r-s| ≤ u) (hhigh : u ≤ r+s) :
    0 ≤ 4*((r^2+s^2)/2-u^2/4)*u^2-(r^2-s^2)^2 := by
  have hl : 0 ≤ u^2-(r-s)^2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (r-s)) hlow 2
    rw [sq_abs] at h
    linarith
  have hh : 0 ≤ (r+s)^2-u^2 := by
    have h := pow_le_pow_left₀ hu hhigh 2
    linarith
  rw [pair_distance_heron_factorization]
  exact mul_nonneg hh hl

theorem pair_distance_axis_real_quotient_identity {r s τ : ℝ} (hτ : τ ≠ 0) :
    τ*((r^2-s^2)/(2*τ)) = (r^2-s^2)/2 := by
  field_simp

theorem pair_distance_real_transverse_nonneg {r s u τ : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hu : 0 ≤ u)
    (hlow : |r-s| ≤ u) (hhigh : u ≤ r+s)
    (hτ : 0 < τ) (htau : τ^2 = (r^2+s^2)/2-u^2/4) :
    0 ≤ u^2-((r^2-s^2)/(2*τ))^2 := by
  let z := (r^2-s^2)/(2*τ)
  have hz : τ*z = (r^2-s^2)/2 := pair_distance_axis_real_quotient_identity (ne_of_gt hτ)
  have hz2 := congrArg (fun x : ℝ => x^2) hz
  have hh := pair_distance_heron_nonneg hr hs hu hlow hhigh
  rw [← htau] at hh
  have hmul : 0 ≤ (4*τ^2)*(u^2-z^2) := by nlinarith [hz2]
  exact nonneg_of_mul_nonneg_right hmul (by positivity : 0 < 4*τ^2)

theorem pair_distance_real_radius_identities {r s u τ : ℝ}
    (hτ : τ ≠ 0) (htau : τ^2 = (r^2+s^2)/2-u^2/4) :
    τ^2+u^2/4+τ*((r^2-s^2)/(2*τ)) = r^2 ∧
      τ^2+u^2/4-τ*((r^2-s^2)/(2*τ)) = s^2 := by
  rw [pair_distance_axis_real_quotient_identity hτ,htau]
  constructor <;> ring

theorem pair_distance_real_reconstruction {r s u τ : ℝ}
    (hτ : τ ≠ 0) (htau : τ^2 = (r^2+s^2)/2-u^2/4) :
    let z := (r^2-s^2)/(2*τ)
    let w := u^2-z^2
    w/4+(τ+z/2)^2 = r^2 ∧
      w/4+(τ-z/2)^2 = s^2 ∧ w+z^2 = u^2 := by
  dsimp only
  have h := pair_distance_real_radius_identities hτ htau
  constructor
  · calc
      _ = τ^2+u^2/4+τ*((r^2-s^2)/(2*τ)) := by ring
      _ = r^2 := h.1
  constructor
  · calc
      _ = τ^2+u^2/4-τ*((r^2-s^2)/(2*τ)) := by ring
      _ = s^2 := h.2
  · ring

end TheoremT.Continuum
