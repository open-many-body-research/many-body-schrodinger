import HydrogenWeak_v1
import WeakCoulombNorm_v2

/-! Directional Hardy on the actual weak-H¹ domain, refining the earlier full-gradient
bound. Only the three derivatives of one selected electron occur on the right. -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped BigOperators ContDiff
namespace TheoremT.Continuum

theorem directional_weak_nuclear_hardy {N : ℕ} (i : Fin N)
    (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) :
    Integrable (fun x => ‖f x‖^2 / ‖position x i‖^2) volume ∧
      (∫ x, ‖f x‖^2 / ‖position x i‖^2) ≤ 4 * (∑ k : Fin 3, ‖d (i,k)‖^2) := by
  have hcore : ∀ u : Configuration N → ℂ, ContDiff ℝ ∞ u → HasCompactSupport u →
      Integrable (fun x => (‖position x i‖^2)⁻¹ * ‖u x‖^2) volume ∧
      (∫ x, (‖position x i‖^2)⁻¹ * ‖u x‖^2) ≤ 0 * (∫ x, ‖u x‖^2) +
        4 * (∫ x, ∑ k ∈ electronCoordinateFinset i, ‖smoothPartial u k x‖^2) := by
    intro u hu huc
    have h := compact_nuclear_hardy_integrable_sq_and_bound i (hu.of_le (by simp)) huc
    simpa only [sum_electronCoordinateFinset, smoothPartial, electronGradientEnergy,
      zero_mul, zero_add, div_eq_mul_inv, mul_comm] using h
  have h := weighted_compact_core_bound_extends_weakH1 (electronCoordinateFinset i)
    (fun x => (‖position x i‖^2)⁻¹) (fun x => inv_nonneg.mpr (sq_nonneg _)) 0 4 hcore f d hd
  simpa only [sum_electronCoordinateFinset, zero_mul, zero_add, div_eq_mul_inv, mul_comm] using h

theorem directional_weak_pair_hardy {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) :
    Integrable (fun x => ‖f x‖^2 / ‖position x i - position x j‖^2) volume ∧
      (∫ x, ‖f x‖^2 / ‖position x i - position x j‖^2) ≤ 4 * (∑ k : Fin 3, ‖d (i,k)‖^2) := by
  have hcore : ∀ u : Configuration N → ℂ, ContDiff ℝ ∞ u → HasCompactSupport u →
      Integrable (fun x => (‖position x i - position x j‖^2)⁻¹ * ‖u x‖^2) volume ∧
      (∫ x, (‖position x i - position x j‖^2)⁻¹ * ‖u x‖^2) ≤ 0 * (∫ x, ‖u x‖^2) +
        4 * (∫ x, ∑ k ∈ electronCoordinateFinset i, ‖smoothPartial u k x‖^2) := by
    intro u hu huc
    have h := compact_pair_hardy_integrable_sq_and_bound i j hij (hu.of_le (by simp)) huc
    simpa only [sum_electronCoordinateFinset, smoothPartial, electronGradientEnergy,
      zero_mul, zero_add, div_eq_mul_inv, mul_comm] using h
  have h := weighted_compact_core_bound_extends_weakH1 (electronCoordinateFinset i)
    (fun x => (‖position x i - position x j‖^2)⁻¹) (fun x => inv_nonneg.mpr (sq_nonneg _)) 0 4 hcore f d hd
  simpa only [sum_electronCoordinateFinset, zero_mul, zero_add, div_eq_mul_inv, mul_comm] using h

theorem directional_weak_nuclear_memLp_two_and_bound {N : ℕ} (i : Fin N)
    (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) :
    MemLp (fun x => f x / (‖position x i‖ : ℂ)) 2 volume ∧
      (∫ x, ‖f x / (‖position x i‖ : ℂ)‖^2) ≤ 4 * (∑ k : Fin 3, ‖d (i,k)‖^2) := by
  have h := directional_weak_nuclear_hardy i f d hd
  have hm : AEStronglyMeasurable (fun x => f x / (‖position x i‖ : ℂ)) volume :=
    ((Lp.memLp f).aestronglyMeasurable.aemeasurable.div
      (Complex.ofRealCLM.continuous.comp
        (continuous_position i).norm).measurable.aemeasurable).aestronglyMeasurable
  constructor
  · apply (memLp_two_iff_integrable_sq_norm hm).2
    simpa only [norm_div, Complex.norm_real, norm_norm, div_pow] using h.1
  · simpa only [norm_div, Complex.norm_real, norm_norm, div_pow] using h.2

theorem directional_weak_pair_memLp_two_and_bound {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) :
    MemLp (fun x => f x / (‖position x i - position x j‖ : ℂ)) 2 volume ∧
      (∫ x, ‖f x / (‖position x i - position x j‖ : ℂ)‖^2) ≤
        4 * (∑ k : Fin 3, ‖d (i,k)‖^2) := by
  have h := directional_weak_pair_hardy i j hij f d hd
  have hm : AEStronglyMeasurable
      (fun x => f x / (‖position x i - position x j‖ : ℂ)) volume :=
    ((Lp.memLp f).aestronglyMeasurable.aemeasurable.div
      (Complex.ofRealCLM.continuous.comp
        ((continuous_position i).sub
          (continuous_position j)).norm).measurable.aemeasurable).aestronglyMeasurable
  constructor
  · apply (memLp_two_iff_integrable_sq_norm hm).2
    simpa only [norm_div, Complex.norm_real, norm_norm, div_pow] using h.1
  · simpa only [norm_div, Complex.norm_real, norm_norm, div_pow] using h.2

theorem directional_nuclear_product_norm_le {N : ℕ} (i : Fin N)
    (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) :
    ‖(directional_weak_nuclear_memLp_two_and_bound i f d hd).1.toLp
        (fun x => f x / (‖position x i‖ : ℂ))‖ ≤
      2 * Real.sqrt (∑ k : Fin 3, ‖d (i,k)‖^2) :=
  norm_toLp_le_two_sqrt_of_integral_sq_le _
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (directional_weak_nuclear_memLp_two_and_bound i f d hd).2

theorem directional_pair_product_norm_le {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) :
    ‖(directional_weak_pair_memLp_two_and_bound i j hij f d hd).1.toLp
        (fun x => f x / (‖position x i - position x j‖ : ℂ))‖ ≤
      2 * Real.sqrt (∑ k : Fin 3, ‖d (i,k)‖^2) :=
  norm_toLp_le_two_sqrt_of_integral_sq_le _
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (directional_weak_pair_memLp_two_and_bound i j hij f d hd).2

/-- Combining the two directional pair estimates gives a bound by the sum of
its two electron derivative norms, without any spin or dimension factor. -/
theorem directional_pair_product_norm_le_add {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) :
    ‖(directional_weak_pair_memLp_two_and_bound i j hij f d hd).1.toLp
        (fun x => f x / (‖position x i - position x j‖ : ℂ))‖ ≤
      Real.sqrt (∑ k : Fin 3, ‖d (i,k)‖^2) + Real.sqrt (∑ k : Fin 3, ‖d (j,k)‖^2) := by
  have hi := directional_pair_product_norm_le i j hij f d hd
  have hj := norm_toLp_le_two_sqrt_of_integral_sq_le
    (directional_weak_pair_memLp_two_and_bound i j hij f d hd).1
    (D := ∑ k : Fin 3, ‖d (j,k)‖^2)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (by simpa only [norm_sub_rev] using
      (directional_weak_pair_memLp_two_and_bound j i hij.symm f d hd).2)
  linarith

#print axioms directional_weak_nuclear_hardy
#print axioms directional_weak_pair_hardy
#print axioms directional_nuclear_product_norm_le
#print axioms directional_pair_product_norm_le_add
end TheoremT.Continuum
