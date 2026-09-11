import ConfigurationLpDominated_v1
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Uniform finite Lp bounds along exponents tending to infinity imply an
essential bound on the actual configuration function. Infinite total volume
is allowed; the proof uses Chebyshev, not finite-measure embeddings. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace TheoremT.Continuum

theorem configuration_norm_superlevel_null_of_Lp_bounds {N : ℕ} (f : SpatialL2 N)
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (ht : Tendsto a atTop atTop)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n, eLpNorm f (ENNReal.ofReal (a n)) volume ≤ ENNReal.ofReal C)
    {t : ℝ} (htC : C < t) :
    volume {x | ENNReal.ofReal t ≤ ‖f x‖ₑ} = 0 := by
  have ht0 : 0 < t := lt_of_le_of_lt hC htC
  have hbound (n : ℕ) : volume {x | ENNReal.ofReal t ≤ ‖f x‖ₑ} ≤
      ENNReal.ofReal ((C/t)^(a n)) := by
    have h := meas_ge_le_mul_pow_eLpNorm_enorm volume
      (by simpa using ha n : ENNReal.ofReal (a n) ≠ 0) ENNReal.ofReal_ne_top
      (Lp.aestronglyMeasurable f)
      (by simpa using ht0 : ENNReal.ofReal t ≠ 0)
      (fun ht' => False.elim (ENNReal.ofReal_ne_top ht'))
    rw [ENNReal.toReal_ofReal (ha n).le] at h
    calc
      _ ≤ (ENNReal.ofReal t)⁻¹^(a n)*eLpNorm f (ENNReal.ofReal (a n)) volume^(a n) := h
      _ ≤ (ENNReal.ofReal t)⁻¹^(a n)*(ENNReal.ofReal C)^(a n) :=
        mul_le_mul le_rfl (ENNReal.rpow_le_rpow (hb n) (ha n).le) (by positivity) (by positivity)
      _ = ENNReal.ofReal ((C/t)^(a n)) := by
        rw [← ENNReal.mul_rpow_of_nonneg _ _ (ha n).le,
          ← ENNReal.ofReal_inv_of_pos ht0,
          ← ENNReal.ofReal_mul (inv_nonneg.mpr ht0.le),
          ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (inv_nonneg.mpr ht0.le) hC) (ha n).le]
        congr 2; ring
  have hratio0 : 0 ≤ C/t := div_nonneg hC ht0.le
  have hratio1 : C/t < 1 := (div_lt_one ht0).mpr htC
  have hlim := (tendsto_rpow_atTop_of_base_lt_one (C/t)
    (by linarith) hratio1).comp ht
  have hlim' : Tendsto (fun n => ENNReal.ofReal ((C/t)^(a n))) atTop (𝓝 0) := by
    convert! ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim using 1
    simp
  exact le_antisymm (le_of_tendsto_of_tendsto' tendsto_const_nhds hlim' hbound) bot_le

#print axioms configuration_norm_superlevel_null_of_Lp_bounds
end TheoremT.Continuum
