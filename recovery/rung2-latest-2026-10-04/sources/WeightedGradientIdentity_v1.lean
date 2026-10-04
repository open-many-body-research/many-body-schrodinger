import BoundedRealMultiplierAlgebra_v1

/-! The exact per-coordinate Hilbert-space identity underlying the Agmon
weighted energy formula, with literal multiplication by real L-infinity weights. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

theorem boundedRealMul_gradient_identity {N : ℕ} (χ η : Configuration N → ℝ)
    (hχ : MemLp χ ⊤ volume) (hη : MemLp η ⊤ volume) (f d : SpatialL2 N) :
    ‖boundedRealMul χ hχ d + boundedRealMul η hη f‖^2 =
      inner ℝ (boundedRealMul χ hχ
        (boundedRealMul χ hχ d + boundedRealMul η hη f) +
          boundedRealMul η hη (boundedRealMul χ hχ f)) d +
        ‖boundedRealMul η hη f‖^2 := by
  have hb : inner ℝ (boundedRealMul η hη (boundedRealMul χ hχ f)) d =
      inner ℝ (boundedRealMul η hη f) (boundedRealMul χ hχ d) := by
    rw [← boundedRealMul_comm χ η hχ hη f,boundedRealMul_real_inner]
  rw [inner_add_left,boundedRealMul_real_inner,hb,inner_add_left,
    real_inner_self_eq_norm_sq,norm_add_sq_real,
    real_inner_comm (boundedRealMul η hη f) (boundedRealMul χ hχ d)]
  ring

#print axioms boundedRealMul_gradient_identity
end TheoremT.Continuum
