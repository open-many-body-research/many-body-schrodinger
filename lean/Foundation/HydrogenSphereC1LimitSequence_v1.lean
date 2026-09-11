import HydrogenSphereC1LimitTangential_v1
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.ContinuousMap.Compact

/-! A single polynomial sequence converging in the actual sphere C1 norm.
The existential sequence is for a density proof, not an effective algorithm. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace TheoremT.HydrogenSphereC1Limit
open TheoremT.HydrogenPolynomial TheoremT.HydrogenPolynomialDensity

def sphereValueMap {f : AngularR3 → ℝ} (hf : Continuous f) :
    C(Metric.sphere (0 : AngularR3) 1, ℝ) :=
  ⟨fun w => f w.val, hf.comp continuous_subtype_val⟩

def sphereTangentMap {f : AngularR3 → ℝ} (hf : ContDiff ℝ 1 f) (i : Fin 3) :
    C(Metric.sphere (0 : AngularR3) 1, ℝ) :=
  sphereValueMap (continuous_tangentialPartial hf i)

theorem polynomial_contDiff_one (P : Polynomial3) :
    ContDiff ℝ 1 (euclideanEvaluation P) :=
  (euclideanEvaluation_contDiff P).of_le (by simp)

theorem exists_sphere_C1_polynomial_sequence {f : AngularR3 → ℝ}
    (hf : ContDiff ℝ 1 f) :
    ∃ P : ℕ → Polynomial3,
      Tendsto (fun n => sphereValueMap (euclideanEvaluation_contDiff (P n)).continuous)
        atTop (𝓝 (sphereValueMap hf.continuous)) ∧
      ∀ i : Fin 3,
        Tendsto (fun n => sphereTangentMap (polynomial_contDiff_one (P n)) i)
          atTop (𝓝 (sphereTangentMap hf i)) := by
  have hex (n : ℕ) := exists_polynomial_C1_near_euclidean_unitSphere hf
    (by positivity : 0 < (1 : ℝ) / ((n : ℝ) + 1))
  choose P hpv hpd using hex
  have hv (n : ℕ) :
      dist (sphereValueMap (euclideanEvaluation_contDiff (P n)).continuous)
        (sphereValueMap hf.continuous) ≤ (1 : ℝ) / ((n : ℝ) + 1) := by
    apply (ContinuousMap.dist_le (by positivity)).2
    intro w
    change |euclideanEvaluation (P n) w.val - f w.val| ≤ _
    exact (hpv n w.val (by simpa [Metric.mem_sphere, dist_zero_right] using w.property)).le
  have hd (i : Fin 3) (n : ℕ) :
      dist (sphereTangentMap (polynomial_contDiff_one (P n)) i)
        (sphereTangentMap hf i) ≤ 4 * ((1 : ℝ) / ((n : ℝ) + 1)) := by
    apply (ContinuousMap.dist_le (by positivity)).2
    intro w
    change |tangentialPartial i (euclideanEvaluation (P n)) w.val -
      tangentialPartial i f w.val| ≤ _
    apply tangentialPartial_error_le (by positivity)
      (by simpa [Metric.mem_sphere, dist_zero_right] using w.property)
    intro j
    simp only [euclideanPartial, euclideanEvaluation_fderiv_single]
    exact (hpd n j w.val (by simpa [Metric.mem_sphere, dist_zero_right] using w.property)).le
  refine ⟨P, ?_, ?_⟩
  · apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ => dist_nonneg) hv tendsto_one_div_add_atTop_nhds_zero_nat
  · intro i
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) (hd i)
    simpa only [mul_zero] using
      tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

end TheoremT.HydrogenSphereC1Limit

#print axioms TheoremT.HydrogenSphereC1Limit.exists_sphere_C1_polynomial_sequence
