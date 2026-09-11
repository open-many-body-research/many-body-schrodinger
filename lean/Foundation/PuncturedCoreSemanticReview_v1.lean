import PuncturedFormComparisonTransfer_v1
import CoulombH1PhysicalEnergy_v1

/-! Independent semantic adapter for the punctured H1 transfer.
This binds its inverse-radius L2 inner product to the literal physical integral.
The core comparison remains a hypothesis, and no hydrogen gap is asserted. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace TheoremT.Continuum

theorem inverse_radius_real_inner_pointwise (z : ℂ) (r : ℝ) :
    inner ℝ z (z / (r : ℂ)) = ‖z‖ ^ 2 / r := by
  have he : z / (r : ℂ) = (r⁻¹ : ℝ) • z := by
    rw [Complex.real_smul]
    simp [div_eq_mul_inv, mul_comm]
  rw [he, inner_smul_right, real_inner_self_eq_norm_sq]
  simp [div_eq_mul_inv, mul_comm]

theorem inverse_radius_energy_integrable (f v : SpatialL2 1)
    (hv : v =ᵐ[volume] fun x => f x / (‖x‖ : ℂ)) :
    Integrable (fun x => ‖f x‖ ^ 2 / ‖x‖) volume := by
  apply (L2.integrable_inner (𝕜 := ℝ) f v).congr
  filter_upwards [hv] with x hx
  rw [hx, inverse_radius_real_inner_pointwise]

theorem inverse_radius_energy_eq_integral (f v : SpatialL2 1)
    (hv : v =ᵐ[volume] fun x => f x / (‖x‖ : ℂ)) :
    (inner ℂ f v).re = ∫ x, ‖f x‖ ^ 2 / ‖x‖ := by
  rw [L2.inner_def]
  change RCLike.re (∫ x, inner ℂ (f x) (v x)) = _
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) f v)]
  apply integral_congr_ae
  filter_upwards [hv] with x hx
  rw [hx]
  exact inverse_radius_real_inner_pointwise (f x) ‖x‖

theorem punctured_core_integral_bound_extends_weakH1
    (Z β C : ℝ) (l : SpatialL2 1 →L[ℂ] ℂ)
    (hcore : ∀ (u : Configuration 1 → ℂ) (g : SpatialL2 1)
      (dg : Coordinate 1 → SpatialL2 1),
      ContDiff ℝ ∞ u → HasCompactSupport u → (0 : Configuration 1) ∉ tsupport u →
      (g =ᵐ[volume] u) →
      (∀ k, dg k =ᵐ[volume] smoothPartial u k) →
      β * ‖g‖ ^ 2 ≤ (1 / 2 : ℝ) * (∑ k : Coordinate 1, ‖dg k‖ ^ 2) -
        Z * (∫ x, ‖g x‖ ^ 2 / ‖x‖) + C * ‖l g‖ ^ 2)
    (f : SpatialL2 1) (d : Coordinate 1 → SpatialL2 1)
    (hd : ∀ k, WeakPartial f (d k) k) :
    β * ‖f‖ ^ 2 ≤ (1 / 2 : ℝ) * (∑ k : Coordinate 1, ‖d k‖ ^ 2) -
      Z * (∫ x, ‖f x‖ ^ 2 / ‖x‖) + C * ‖l f‖ ^ 2 := by
  let hm := weakH1_div_configuration_norm_memLp f d hd
  let v : SpatialL2 1 := hm.toLp (fun x => f x / (‖x‖ : ℂ))
  have hv : v =ᵐ[volume] fun x => f x / (‖x‖ : ℂ) := hm.coeFn_toLp
  rw [← inverse_radius_energy_eq_integral f v hv]
  apply punctured_core_rankOne_bound_extends_weakH1 Z β C l _ f v d hd hv
  intro u g w dg hu hc hzero hgu hdgu hgw
  rw [inverse_radius_energy_eq_integral g w hgw]
  exact hcore u g dg hu hc hzero hgu hdgu

#print axioms inverse_radius_real_inner_pointwise
#print axioms inverse_radius_energy_integrable
#print axioms inverse_radius_energy_eq_integral
#print axioms punctured_core_integral_bound_extends_weakH1
end TheoremT.Continuum
