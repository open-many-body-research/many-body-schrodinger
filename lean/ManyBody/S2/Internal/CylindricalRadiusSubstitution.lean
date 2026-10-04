import PolarThree_v1
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! An exact change from planar radius to full three-dimensional radius.
The measure-theoretic Jacobian proof handles arbitrary integrands and retains
the correct radial factor; no Coulomb integral is assumed.
-/
noncomputable section
open MeasureTheory Set
namespace ManyBody.S2.Internal.Cylindrical

/-- The actual planar-radius to full-radius change of variables, valid for
arbitrary integrands with the Bochner integral's usual convention. -/
theorem integral_full_radius (z : ℝ) (f : ℝ → ℝ) :
    (∫ ρ : ℝ in Ioi 0, ρ * f (Real.sqrt (z^2+ρ^2))) =
      ∫ R : ℝ in Ioi |z|, R * f R := by
  have hpos (ρ : ℝ) (hρ : ρ ∈ Ioi (0 : ℝ)) : 0 < z^2+ρ^2 := by
    nlinarith [sq_nonneg z,sq_pos_of_pos (mem_Ioi.mp hρ)]
  have himage : (fun ρ : ℝ => Real.sqrt (z^2+ρ^2)) '' Ioi 0 = Ioi |z| := by
    ext R
    constructor
    · rintro ⟨ρ,hρ,rfl⟩
      apply (sq_lt_sq₀ (abs_nonneg z) (Real.sqrt_nonneg _)).mp
      rw [sq_abs,Real.sq_sqrt (by positivity)]
      nlinarith [sq_pos_of_pos (mem_Ioi.mp hρ)]
    · intro hR
      have hR0 : 0 < R := lt_of_le_of_lt (abs_nonneg z) hR
      have hdiff : 0 < R^2-z^2 := by
        have h := (sq_lt_sq₀ (abs_nonneg z) hR0.le).mpr hR
        rw [sq_abs] at h
        linarith
      refine ⟨Real.sqrt (R^2-z^2),Real.sqrt_pos.mpr hdiff,?_⟩
      have he : z^2+(Real.sqrt (R^2-z^2))^2 = R^2 := by
        rw [Real.sq_sqrt hdiff.le]
        ring
      dsimp only
      rw [he,Real.sqrt_sq hR0.le]
  have hinj : InjOn (fun ρ : ℝ => Real.sqrt (z^2+ρ^2)) (Ioi 0) := by
    intro ρ hρ τ hτ he
    have he2 := congrArg (fun u : ℝ => u^2) he
    rw [Real.sq_sqrt (hpos ρ hρ).le,Real.sq_sqrt (hpos τ hτ).le] at he2
    apply (sq_eq_sq₀ hρ.le hτ.le).mp
    linarith
  have hderiv (ρ : ℝ) (hρ : ρ ∈ Ioi (0 : ℝ)) :
      HasDerivAt (fun ρ : ℝ => Real.sqrt (z^2+ρ^2))
        (ρ / Real.sqrt (z^2+ρ^2)) ρ := by
    have h := ((hasDerivAt_const ρ (z^2)).add ((hasDerivAt_id ρ).pow 2)).sqrt
      (ne_of_gt (hpos ρ hρ))
    convert! h using 1
    dsimp
    field_simp [(Real.sqrt_pos.mpr (hpos ρ hρ)).ne']
    ring
  have he := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun ρ hρ => (hderiv ρ hρ).hasDerivWithinAt) hinj (fun R : ℝ => R*f R)
  rw [himage] at he
  rw [he]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro ρ hρ
  dsimp only
  rw [smul_eq_mul,abs_of_pos (div_pos (mem_Ioi.mp hρ) (Real.sqrt_pos.mpr (hpos ρ hρ)))]
  field_simp [(Real.sqrt_pos.mpr (hpos ρ hρ)).ne']

#print axioms integral_full_radius
end ManyBody.S2.Internal.Cylindrical
