import PuncturedCutoffGeometry_v1
import CutoffConvergence_v2
import WeakCoulombL2_v2
import HydrogenRadialTrace_v1

/-! Shrinking-cutoff convergence in actual L² and actual weak H¹ for one electron.
The derivative term is controlled by the already-proved three-dimensional Hardy
inequality. In particular, the nullity of the origin is not used alone to justify
convergence of derivatives. This is mathematical approximation, not an algorithm. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

theorem spatialL2_dominated_tendsto_zero {N : ℕ}
    (F : ℕ → SpatialL2 N) (b : Configuration N → ℂ) (hb : MemLp b 2 volume)
    (hbound : ∀ n, ∀ᵐ x ∂volume, ‖F n x‖ ≤ ‖b x‖)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun n => F n x) atTop (𝓝 0)) :
    Tendsto F atTop (𝓝 0) := by
  have hi : Integrable (fun x => ‖b x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hb.aestronglyMeasurable).mp hb
  have hdom (n : ℕ) : ∀ᵐ x ∂volume, ‖‖F n x‖ ^ 2‖ ≤ ‖b x‖ ^ 2 := by
    filter_upwards [hbound n] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hx 2
  have he : ∀ᵐ x ∂volume, Tendsto (fun n => ‖F n x‖ ^ 2) atTop (𝓝 0) := by
    filter_upwards [hlim] with x hx
    simpa using hx.norm.pow 2
  have ht : Tendsto (fun n => ∫ x, ‖F n x‖ ^ 2) atTop (𝓝 0) := by
    simpa only [integral_zero, Pi.pow_apply] using tendsto_integral_of_dominated_convergence
      (fun x => ‖b x‖ ^ 2) (fun n => (Lp.aestronglyMeasurable (F n)).norm.pow 2)
      hi hdom he
  have ht2 : Tendsto (fun n => ‖F n‖ ^ 2) atTop (𝓝 0) := by
    simpa only [spatialL2_norm_sq_integral] using ht
  have ht1 := (Real.continuous_sqrt.tendsto 0).comp ht2
  simp only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] at ht1
  exact tendsto_zero_iff_norm_tendsto_zero.mpr ht1

def shrinkingCutoffAt {N : ℕ} (n : ℕ) (f : SpatialL2 N) : SpatialL2 N :=
  cutoffMul (scaledCutoff N (punctureRadius n)) (scaledCutoff_contDiff N _).continuous
    (scaledCutoff_hasCompactSupport N (punctureRadius_pos n)) f

theorem shrinkingCutoffAt_ae {N : ℕ} (n : ℕ) (f : SpatialL2 N) :
    shrinkingCutoffAt n f =ᵐ[volume]
      (fun x => scaledCutoff N (punctureRadius n) x • f x) :=
  cutoffMul_ae _ _ _ f

def shrinkingCutoffErrorAt {N : ℕ} (n : ℕ) (f : SpatialL2 N)
    (k : Coordinate N) : SpatialL2 N :=
  cutoffMul (fun x => fderiv ℝ (scaledCutoff N (punctureRadius n)) x (coordinateVector k))
    (((scaledCutoff_contDiff N _).continuous_fderiv (by simp)).clm_apply continuous_const)
    ((scaledCutoff_hasCompactSupport N (punctureRadius_pos n)).fderiv_apply ℝ
      (coordinateVector k)) f

theorem shrinkingCutoffErrorAt_ae {N : ℕ} (n : ℕ) (f : SpatialL2 N)
    (k : Coordinate N) :
    shrinkingCutoffErrorAt n f k =ᵐ[volume]
      (fun x => fderiv ℝ (scaledCutoff N (punctureRadius n)) x (coordinateVector k) • f x) :=
  cutoffMul_ae _ _ _ f

theorem shrinkingCutoffAt_tendsto_zero (f : SpatialL2 1) :
    Tendsto (fun n => shrinkingCutoffAt n f) atTop (𝓝 0) := by
  apply spatialL2_dominated_tendsto_zero _ f (Lp.memLp f)
  · intro n
    filter_upwards [shrinkingCutoffAt_ae n f] with x hx
    rw [hx, norm_smul]
    simpa using mul_le_mul_of_nonneg_right
      (scaledCutoff_norm_le_one 1 (punctureRadius n) x) (norm_nonneg (f x))
  · have ha : ∀ᵐ x ∂volume, ∀ n, shrinkingCutoffAt n f x =
        scaledCutoff 1 (punctureRadius n) x • f x := ae_all_iff.mpr
      (fun n => shrinkingCutoffAt_ae n f)
    filter_upwards [ha, hydrogen_ae_ne_zero] with x hx hn
    have ht : Tendsto (fun n => scaledCutoff 1 (punctureRadius n) x) atTop (𝓝 0) :=
      tendsto_const_nhds.congr' (shrinkingCutoff_eventually_zero hn).symm
    simpa only [hx, zero_smul] using ht.smul_const (f x)

theorem weakH1_div_configuration_norm_memLp (f : SpatialL2 1)
    (d : Coordinate 1 → SpatialL2 1) (hd : ∀ k, WeakPartial f (d k) k) :
    MemLp (fun x => f x / (‖x‖ : ℂ)) 2 volume := by
  simpa only [position_one_norm] using (weak_nuclear_memLp_two_and_bound 0 f d hd).1

theorem shrinkingCutoffErrorAt_tendsto_zero (f : SpatialL2 1)
    (d : Coordinate 1 → SpatialL2 1) (hd : ∀ k, WeakPartial f (d k) k)
    (k : Coordinate 1) :
    Tendsto (fun n => shrinkingCutoffErrorAt n f k) atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := scaledCutoff_partial_inverse_distance_bound 1
  let b : Configuration 1 → ℂ := fun x => (2 * C) • (f x / (‖x‖ : ℂ))
  have hbm : MemLp b 2 volume := (weakH1_div_configuration_norm_memLp f d hd).const_smul (2 * C)
  apply spatialL2_dominated_tendsto_zero _ b hbm
  · intro n
    filter_upwards [shrinkingCutoffErrorAt_ae n f k, hydrogen_ae_ne_zero] with x hx hn
    rw [hx, norm_smul]
    have hh := mul_le_mul_of_nonneg_right (hb (punctureRadius n) (punctureRadius_pos n) x hn k)
      (norm_nonneg (f x))
    change _ ≤ ‖(2 * C) • (f x / (‖x‖ : ℂ))‖
    rw [norm_smul, Real.norm_eq_abs (2 * C), abs_of_nonneg (by positivity : 0 ≤ 2 * C),
      norm_div, Complex.norm_real, norm_norm]
    calc _ ≤ (2 * C) / ‖x‖ * ‖f x‖ := hh
         _ = _ := by ring
  · have ha : ∀ᵐ x ∂volume, ∀ n, shrinkingCutoffErrorAt n f k x =
        fderiv ℝ (scaledCutoff 1 (punctureRadius n)) x (coordinateVector k) • f x :=
      ae_all_iff.mpr (fun n => shrinkingCutoffErrorAt_ae n f k)
    filter_upwards [ha, hydrogen_ae_ne_zero] with x hx hn
    have ht : Tendsto
        (fun n => fderiv ℝ (scaledCutoff 1 (punctureRadius n)) x (coordinateVector k))
        atTop (𝓝 0) :=
      tendsto_const_nhds.congr' (shrinkingCutoff_partial_eventually_zero hn k).symm
    simpa only [hx, zero_smul] using ht.smul_const (f x)

#print axioms spatialL2_dominated_tendsto_zero
#print axioms shrinkingCutoffAt_tendsto_zero
#print axioms weakH1_div_configuration_norm_memLp
#print axioms shrinkingCutoffErrorAt_tendsto_zero
end TheoremT.Continuum
