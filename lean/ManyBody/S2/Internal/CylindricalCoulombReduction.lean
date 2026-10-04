import ManyBody.S2.Internal.CylindricalIntegration
import ManyBody.S2.Internal.CylindricalRadiusSubstitution

/-! Actual canonical three-dimensional volume in height/full-radius coordinates, obtained from volume-preserving Euclidean splitting, planar radial integration, and the proved full-radius substitution. The displaced Coulomb integral retains its literal norm denominator. -/

noncomputable section
open MeasureTheory Set
namespace ManyBody.S2.Internal.Cylindrical

def axisReal : Axis ≃ₗᵢ[ℝ] ℝ := (OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm

def height (x : Space) : ℝ := axisReal (split x).1

def axisPoint (s : ℝ) : Space := split.symm (axisReal.symm s,0)

theorem norm_eq_split (x : Space) :
    ‖x‖^2 = (height x)^2 + ‖(split x).2‖^2 := by
  have h := assemble_norm_sq (split x).1 (split x).2
  simp only [Prod.eta,split.symm_apply_apply] at h
  rw [← axisReal.norm_map (split x).1,Real.norm_eq_abs,sq_abs] at h
  exact h

theorem norm_sub_axisPoint_sq (x : Space) (s : ℝ) :
    ‖x-axisPoint s‖^2 = ‖x‖^2-2*s*height x+s^2 := by
  have he : x-axisPoint s = split.symm ((split x).1-axisReal.symm s,(split x).2) := by
    apply split.injective
    simp only [map_sub,axisPoint,split.apply_symm_apply]
    ext <;> simp
  rw [he,assemble_norm_sq,← axisReal.norm_map ((split x).1-axisReal.symm s),
    map_sub,axisReal.apply_symm_apply,Real.norm_eq_abs,sq_abs,norm_eq_split]
  change ((height x)-s)^2+‖(split x).2‖^2 = _
  ring

theorem norm_sub_axisPoint (x : Space) (s : ℝ) :
    ‖x-axisPoint s‖ = Real.sqrt (‖x‖^2-2*s*height x+s^2) := by
  rw [← norm_sub_axisPoint_sq,Real.sqrt_sq (norm_nonneg _)]

/-- Canonical three-dimensional integration in height and full radius. -/
theorem integral_height_radius (K : ℝ → ℝ → ℝ)
    (hK : Integrable (fun x : Space => K (height x) ‖x‖)) :
    (∫ x : Space, K (height x) ‖x‖) =
      (2*Real.pi) * ∫ z : ℝ, ∫ R : ℝ in Ioi |z|, R*K z R := by
  have hnorm (x : Space) :
      ‖x‖ = Real.sqrt (‖(split x).1‖^2+‖(split x).2‖^2) := by
    have h := assemble_norm_sq (split x).1 (split x).2
    simp only [Prod.eta,split.symm_apply_apply] at h
    rw [← h,Real.sqrt_sq (norm_nonneg _)]
  have hF : Integrable (fun x : Space =>
      K (axisReal (split x).1)
        (Real.sqrt (‖(split x).1‖^2+‖(split x).2‖^2))) := by
    apply hK.congr
    filter_upwards [] with x
    rw [← hnorm]
    rfl
  have hc := integral_cylindrical
    (fun a : Axis => fun ρ : ℝ => K (axisReal a) (Real.sqrt (‖a‖^2+ρ^2))) hF
  have hcoord := axisReal.symm.measurePreserving.integral_comp
    axisReal.symm.toHomeomorph.measurableEmbedding
    (fun a : Axis => ∫ ρ : ℝ in Ioi 0, ρ*K (axisReal a) (Real.sqrt (‖a‖^2+ρ^2)))
  have hcoord' :
      (∫ z : ℝ, ∫ ρ : ℝ in Ioi 0, ρ*K z (Real.sqrt (z^2+ρ^2))) =
      ∫ a : Axis, ∫ ρ : ℝ in Ioi 0, ρ*K (axisReal a) (Real.sqrt (‖a‖^2+ρ^2)) := by
    simpa only [axisReal.apply_symm_apply,axisReal.symm.norm_map,Real.norm_eq_abs,sq_abs]
      using hcoord
  calc
    _ = (2*Real.pi) * ∫ a : Axis, ∫ ρ : ℝ in Ioi 0,
        ρ*K (axisReal a) (Real.sqrt (‖a‖^2+ρ^2)) := by
      rw [← hc]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← hnorm]
      rfl
    _ = (2*Real.pi) * ∫ z : ℝ, ∫ ρ : ℝ in Ioi 0,
        ρ*K z (Real.sqrt (z^2+ρ^2)) := by rw [hcoord']
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with z
      exact integral_full_radius z (K z)

/-- The literal displaced Coulomb integral in canonical Euclidean volume. -/
theorem integral_radial_coulomb_cylindrical (s : ℝ) (f : ℝ → ℝ)
    (hf : Integrable (fun x : Space => f ‖x‖ / ‖x-axisPoint s‖)) :
    (∫ x : Space, f ‖x‖ / ‖x-axisPoint s‖) =
      (2*Real.pi) * ∫ z : ℝ, ∫ R : ℝ in Ioi |z|,
        R*f R / Real.sqrt (R^2-2*s*z+s^2) := by
  have hK : Integrable (fun x : Space =>
      f ‖x‖ / Real.sqrt (‖x‖^2-2*s*height x+s^2)) := by
    apply hf.congr
    filter_upwards [] with x
    rw [← norm_sub_axisPoint]
  have h := integral_height_radius
    (fun z R : ℝ => f R / Real.sqrt (R^2-2*s*z+s^2)) hK
  simpa only [← norm_sub_axisPoint, mul_div_assoc] using h

#print axioms integral_height_radius
#print axioms integral_radial_coulomb_cylindrical
end ManyBody.S2.Internal.Cylindrical
