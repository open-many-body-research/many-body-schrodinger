import PowerSeriesDiagonalInvariance_v1

/-! Local invariance at an actual fixed center preserves every diagonal
coefficient of the actual convergent series at that center. The fixed-point
identity is explicit; no off-diagonal symmetry of the series is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace TheoremT.Continuum

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem powerSeries_diagonal_invariant_at_fixed_point
    {f : E → F} {p : FormalMultilinearSeries ℝ E F} {x : E}
    (hf : HasFPowerSeriesAt f p x) (L : E →L[ℝ] E) (hfixed : L x = x)
    (hInv : (f ∘ L) =ᶠ[𝓝 x] f) (n : ℕ) (y : E) :
    p n (fun _ => L y) = p n (fun _ => y) := by
  have hcomp : HasFPowerSeriesAt (f ∘ L) (p.compContinuousLinearMap L) x :=
    (show HasFPowerSeriesAt f p (L x) by rw [hfixed]; exact hf).compContinuousLinearMap
  simpa only [FormalMultilinearSeries.compContinuousLinearMap_apply,Function.comp_def] using
    powerSeries_diagonal_eq_of_eventually hcomp hf hInv n y

end TheoremT.Continuum
