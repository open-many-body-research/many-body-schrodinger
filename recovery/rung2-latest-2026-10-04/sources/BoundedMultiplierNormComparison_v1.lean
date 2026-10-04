import BoundedRealMultiplierAlgebra_v1

/-! Norm comparison and finite-sum linearity for actual bounded real L²
multipliers. These represent genuine functions modulo almost-everywhere equality. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum

theorem boundedRealMul_norm_le_relative {N : ℕ}
    (χ η : Configuration N → ℝ) (hχ : MemLp χ ⊤ volume) (hη : MemLp η ⊤ volume)
    (C : ℝ) (hb : ∀ x, |χ x| ≤ C*|η x|) (f : SpatialL2 N) :
    ‖boundedRealMul χ hχ f‖ ≤ C*‖boundedRealMul η hη f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [boundedRealMul_ae χ hχ f,boundedRealMul_ae η hη f] with x hx hy
  rw [hx,hy]
  simp only [norm_smul,Real.norm_eq_abs]
  have h := mul_le_mul_of_nonneg_right (hb x) (norm_nonneg (f x))
  nlinarith

theorem boundedRealMul_sum {N : ℕ} {ι : Type*} [Fintype ι]
    (χ : Configuration N → ℝ) (hχ : MemLp χ ⊤ volume) (f : ι → SpatialL2 N) :
    boundedRealMul χ hχ (∑ i, f i) = ∑ i, boundedRealMul χ hχ (f i) := by
  classical
  let M : SpatialL2 N →ₗ[ℂ] SpatialL2 N :=
    { toFun := boundedRealMul χ hχ
      map_add' := boundedRealMul_add χ hχ
      map_smul' := fun c f => boundedRealMul_smul χ hχ c f }
  exact map_sum M f Finset.univ

#print axioms boundedRealMul_norm_le_relative
#print axioms boundedRealMul_sum
end TheoremT.Continuum
