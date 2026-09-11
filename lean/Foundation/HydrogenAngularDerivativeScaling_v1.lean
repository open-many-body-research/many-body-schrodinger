import HydrogenAngularHomogeneity_v1
import HydrogenAngularRegularity_v1

/-! Derivatives of the actual degree-zero angular extension scale with degree
minus one. This supplies the derivative factor in polar angular integration. -/
noncomputable section
open scoped ContDiff
namespace TheoremT.HydrogenPolynomial

theorem harmonicAngularExtension_fderiv_scale {P : MvPolynomial (Fin 3) ℝ} {m : ℕ}
    (hP : P.IsHomogeneous m) {c : ℝ} (hc : 0 < c)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ≠ 0) (v : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (harmonicAngularExtension m P) (c • x) v =
      c⁻¹ * fderiv ℝ (harmonicAngularExtension m P) x v := by
  have hcx : c • x ≠ 0 := smul_ne_zero hc.ne' hx
  have hy := ((harmonicAngularExtension_contDiffAt m P hcx).differentiableAt
    (by simp)).hasFDerivAt
  have hh := hy.comp x ((hasFDerivAt_id x).const_smul c)
  have he : (harmonicAngularExtension m P ∘ fun y : EuclideanSpace ℝ (Fin 3) => c • y) =
      harmonicAngularExtension m P := by
    funext y
    exact harmonicAngularExtension_scale hP hc y
  rw [he] at hh
  have hv := congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ => L v) hh.fderiv
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul] at hv
  rw [hv]
  field_simp

end TheoremT.HydrogenPolynomial
