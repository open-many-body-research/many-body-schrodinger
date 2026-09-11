import SmoothRadialPowerL2_v1
import CoulombWeakFormPairing_v1

/-! Lift the pointwise radial test identities to actual L2 inner products.
Potential products refer to the same real multiplication potential on both
sides; no finite matrix, quadrature, or formal differential expression is used. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum

theorem smoothRadialPowerL2_inner {N : ℕ} {a b r : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hr : 0 ≤ r) (f : SpatialL2 N) :
    inner ℝ (smoothRadialPowerL2 ha hab (show 0 ≤ 2*r by positivity) f) f =
      ‖smoothRadialPowerL2 ha hab hr f‖^2 := by
  rw [L2.inner_def,spatialL2_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [smoothRadialPowerL2_ae ha hab (show 0 ≤ 2*r by positivity) f,
    smoothRadialPowerL2_ae ha hab hr f] with x h1 h2
  rw [h1,h2]
  exact smoothRadialPower_test_inner ha hab (f x)

theorem smoothRadialPowerL2_potential_inner {N : ℕ} {a b r : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hr : 0 ≤ r) (f vf vg : SpatialL2 N)
    (V : Configuration N → ℝ)
    (hvf : vf =ᵐ[volume] fun x => (V x : ℂ)*f x)
    (hvg : vg =ᵐ[volume] fun x => (V x : ℂ)*smoothRadialPowerL2 ha hab hr f x) :
    inner ℝ (smoothRadialPowerL2 ha hab (show 0 ≤ 2*r by positivity) f) vf =
      inner ℝ (smoothRadialPowerL2 ha hab hr f) vg := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [smoothRadialPowerL2_ae ha hab (show 0 ≤ 2*r by positivity) f,
    smoothRadialPowerL2_ae ha hab hr f,hvf,hvg] with x h1 h2 h3 h4
  rw [h1,h3,h4,h2]
  exact smoothRadialPower_potential_inner ha hab (f x) (V x)

theorem smoothRadialPowerDerivativeL2_energy {N : ℕ} {a b r : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hr : 0 ≤ r) (f d : SpatialL2 N) :
    ‖smoothRadialPowerDerivativeL2 ha hab hr f d‖^2 ≤
      (1+4*r^2)*inner ℝ
        (smoothRadialPowerDerivativeL2 ha hab (show 0 ≤ 2*r by positivity) f d) d := by
  rw [spatialL2_norm_sq_eq_integral,L2.inner_def,← integral_const_mul]
  apply integral_mono_ae
  · exact (Lp.memLp _).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  · exact (L2.integrable_inner _ _).const_mul _
  · filter_upwards [smoothRadialPowerDerivativeL2_ae ha hab hr f d,
      smoothRadialPowerDerivativeL2_ae ha hab (show 0 ≤ 2*r by positivity) f d] with x h1 h2
    rw [h1,h2]
    exact smoothRadialPower_energy_bound ha hab hr (f x) (d x)

theorem smoothRadialPowerL2_gradient_energy {N : ℕ} {a b r : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hr : 0 ≤ r) (f : SpatialL2 N)
    (d : Coordinate N → SpatialL2 N) :
    (∑ k, ‖smoothRadialPowerDerivativeL2 ha hab hr f (d k)‖^2) ≤
      (1+4*r^2)*∑ k, inner ℝ
        (smoothRadialPowerDerivativeL2 ha hab (show 0 ≤ 2*r by positivity) f (d k)) (d k) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun k _ => smoothRadialPowerDerivativeL2_energy ha hab hr f (d k))

#print axioms smoothRadialPowerL2_inner
#print axioms smoothRadialPowerL2_potential_inner
#print axioms smoothRadialPowerL2_gradient_energy
end TheoremT.Continuum
