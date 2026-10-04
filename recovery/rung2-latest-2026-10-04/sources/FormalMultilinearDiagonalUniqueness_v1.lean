import Mathlib.Analysis.Analytic.Uniqueness

/-! Locally equal power-series sums have equal diagonal coefficients.
No equality of arbitrary nonsymmetric multilinear representatives is
claimed. This is the exact form needed for homogeneous polynomials. -/
noncomputable section
set_option autoImplicit false
open scoped Topology
namespace TheoremT.Continuum
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem formalMultilinear_diagonal_eq_of_eventually
    {f g : E → F} {p q : FormalMultilinearSeries 𝕜 E F} {x : E}
    (hp : HasFPowerSeriesAt f p x) (hq : HasFPowerSeriesAt g q x)
    (heq : f =ᶠ[𝓝 x] g) (n : ℕ) (y : E) :
    p n (fun _ => y) = q n (fun _ => y) := by
  have hz : HasFPowerSeriesAt (0 : E → F) (p-q) x := by
    simpa only [sub_self] using (hp.congr heq).sub hq
  have hh := hz.apply_eq_zero n y
  change p n (fun _ => y) - q n (fun _ => y) = 0 at hh
  exact sub_eq_zero.mp hh

end TheoremT.Continuum
