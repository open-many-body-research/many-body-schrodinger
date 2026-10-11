import ScalarCoulombForm_v1
import WeakCoulombNorm_v2

/-! Control of actual first weak derivatives by the scalar Coulomb H¹ form.
This deliberately uses a coarse established Hardy coefficient and applies to
every finite electron count and real charge, without a binding hypothesis. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum

theorem scalar_form_kinetic_bound {N : ℕ} {Z q : ℝ} {f : SpatialL2 N}
    (d : Coordinate N → SpatialL2 N) (hd : ∀ k, WeakPartial f (d k) k)
    (hq : scalarCoulombH1FormValue N Z f q) :
    (∑ k, ‖d k‖^2) ≤ 4 * (q +
      (2*(|Z| *(N : ℝ)+(N.choose 2 : ℝ)))^2 * ‖f‖^2) := by
  obtain ⟨d',v,hd',hv,rfl⟩ := hq
  have he : d' = d := funext (fun k => weakPartial_unique (hd' k) (hd k))
  subst d'
  let D := ∑ k : Coordinate N, ‖d k‖^2
  let C := 2*(|Z| *(N : ℝ)+(N.choose 2 : ℝ))
  have hD : 0 ≤ D := Finset.sum_nonneg (fun k _ => sq_nonneg ‖d k‖)
  have hV : ‖v‖ ≤ C*Real.sqrt D := coulomb_product_norm_le Z f d hd v hv
  have hi := abs_real_inner_le_norm f v
  have hn := mul_le_mul_of_nonneg_left hV (norm_nonneg f)
  have hs := sq_nonneg (Real.sqrt D/2-C*‖f‖)
  simp only [sub_sq,div_pow,mul_pow,Real.sq_sqrt hD] at hs
  have hb : -(D/4+C^2*‖f‖^2) ≤ inner ℝ f v := by
    have h := neg_le_of_abs_le hi
    nlinarith
  unfold scalarCoulombH1Energy
  rw [← spatialL2_real_inner_eq_re]
  change D ≤ 4*((1/2 : ℝ)*D+inner ℝ f v+C^2*‖f‖^2)
  linarith

#print axioms scalar_form_kinetic_bound
end TheoremT.Continuum
