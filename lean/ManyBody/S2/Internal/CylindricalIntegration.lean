import PolarThree_v1
import Mathlib.MeasureTheory.Integral.Prod

/-! Exact Cartesian axis/plane splitting and cylindrical Fubini integration
in canonical three-dimensional Lebesgue volume. This analytic infrastructure
uses the proved two-dimensional radial formula; it assumes no Coulomb moment.
-/
noncomputable section
open MeasureTheory Set
namespace ManyBody.S2.Internal.Cylindrical

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Axis := EuclideanSpace ℝ (Fin 1)
abbrev Plane := EuclideanSpace ℝ (Fin 2)

def splitIsometry : Space ≃ₗᵢ[ℝ] WithLp 2 (Axis × Plane) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (finSumFinEquiv : Fin 1 ⊕ Fin 2 ≃ Fin 3).symm).trans
    (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin 1 ⊕ Fin 2 => ℝ))

def split : Space ≃L[ℝ] Axis × Plane :=
  splitIsometry.toContinuousLinearEquiv.trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ Axis Plane)

theorem split_measurePreserving :
    MeasurePreserving split volume ((volume : Measure Axis).prod volume) :=
  (WithLp.volume_preserving_ofLp Axis Plane).comp splitIsometry.measurePreserving

theorem assemble_measurePreserving :
    MeasurePreserving split.symm ((volume : Measure Axis).prod volume) volume :=
  splitIsometry.symm.measurePreserving.comp
    (WithLp.volume_preserving_toLp Axis Plane)

theorem assemble_norm_sq (z : Axis) (w : Plane) :
    ‖split.symm (z,w)‖^2 = ‖z‖^2 + ‖w‖^2 := by
  change ‖splitIsometry.symm (WithLp.toLp 2 (z,w))‖^2 = _
  rw [splitIsometry.symm.norm_map,WithLp.prod_norm_sq_eq_of_L2]
  rfl

theorem plane_unit_ball_volume :
    (volume : Measure Plane).real (Metric.ball 0 1) = Real.pi := by
  rw [Measure.real,InnerProductSpace.volume_ball_of_dim_even
    (k := 1) (by simp : Module.finrank ℝ Plane = 2*1)]
  norm_num [ENNReal.toReal_ofReal Real.pi_nonneg]

theorem integral_plane_radial (f : ℝ → ℝ) :
    (∫ w : Plane, f ‖w‖) =
      (2*Real.pi) * ∫ ρ : ℝ in Ioi 0, ρ * f ρ := by
  rw [integral_fun_norm_addHaar (volume : Measure Plane) f,plane_unit_ball_volume]
  have hdim : Module.finrank ℝ Plane = 2 := by simp [Plane]
  rw [hdim]
  simp only [Nat.reduceSub,
    pow_one,smul_eq_mul]
  ring

/-- An exact cylindrical Fubini formula in canonical three-dimensional volume. -/
theorem integral_cylindrical (F : Axis → ℝ → ℝ)
    (hF : Integrable (fun x : Space => F (split x).1 ‖(split x).2‖)) :
    (∫ x : Space, F (split x).1 ‖(split x).2‖) =
      (2*Real.pi) * ∫ z : Axis, ∫ ρ : ℝ in Ioi 0, ρ * F z ρ := by
  have hp : Integrable (fun p : Axis × Plane => F p.1 ‖p.2‖)
      ((volume : Measure Axis).prod volume) := by
    have hp0 := assemble_measurePreserving.integrable_comp_of_integrable hF
    apply hp0.congr
    filter_upwards [] with p
    simp only [Function.comp_apply,split.apply_symm_apply]
  calc
    _ = ∫ p : Axis × Plane, F p.1 ‖p.2‖
        ∂(volume : Measure Axis).prod volume := by
      have h := assemble_measurePreserving.integral_comp
        split.symm.toHomeomorph.measurableEmbedding
        (fun x : Space => F (split x).1 ‖(split x).2‖)
      simpa only [Function.comp_apply,split.apply_symm_apply] using h.symm
    _ = ∫ z : Axis, ∫ w : Plane, F z ‖w‖ := integral_prod _ hp
    _ = _ := by
      rw [← integral_const_mul]
      congr 1
      funext z
      exact integral_plane_radial (F z)

#print axioms integral_cylindrical
#print axioms assemble_norm_sq
end ManyBody.S2.Internal.Cylindrical
