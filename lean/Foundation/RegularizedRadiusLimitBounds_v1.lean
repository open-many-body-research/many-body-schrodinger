import RegularizedRadiusLaplacian_v1
import AtomicSobolevExponent_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

theorem configuration_ae_ne_zero {N : ℕ} (hN : 0 < N) :
    ∀ᵐ x : Configuration N, x ≠ 0 := by
  haveI : Nontrivial (Configuration N) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by rw [configuration_finrank]; omega)
  apply ae_iff.mpr
  simp

theorem regularizedConfigurationRadius_le_norm_add_one {N : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (x : Configuration N) :
    regularizedConfigurationRadius N δ x ≤ ‖x‖+1 := by
  nlinarith [regularizedConfigurationRadius_sq hδ x,
    regularizedConfigurationRadius_pos hδ x,norm_nonneg x]

def radiusRegularization (n : ℕ) : ℝ := 1/((n:ℝ)+1)

theorem radiusRegularization_pos (n : ℕ) : 0 < radiusRegularization n := by
  unfold radiusRegularization; positivity

theorem radiusRegularization_le_one (n : ℕ) : radiusRegularization n ≤ 1 := by
  unfold radiusRegularization
  apply (div_le_one (by positivity)).mpr
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem radiusRegularization_tendsto : Tendsto radiusRegularization atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

#print axioms configuration_ae_ne_zero
end TheoremT.Continuum
