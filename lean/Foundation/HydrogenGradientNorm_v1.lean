import NormalizedHydrogenGraph_v1
import HardyWeakTransfer_v2

/-! Exact kinetic norm of the actual normalized hydrogen exponential. -/
noncomputable section
open MeasureTheory Filter
namespace TheoremT.Continuum
open TheoremT.Polar

theorem hydrogenFirst_pointwise_norm_sum (Z : ℝ) {x : Configuration 1} (hx : x ≠ 0) :
    (∑ k : Coordinate 1, ‖hydrogenFirst Z k x‖^2) = Z^2 * ‖hydrogenRadial Z x‖^2 := by
  simp only [hydrogenFirst,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,div_pow,
    neg_sq]
  have he (k : Coordinate 1) :
      (Z^2 * (x k)^2) / ‖x‖^2 * ‖hydrogenRadial Z x‖^2 =
        (Z^2 / ‖x‖^2 * ‖hydrogenRadial Z x‖^2) * (x k)^2 := by ring
  simp_rw [he]
  rw [← Finset.mul_sum,← EuclideanSpace.real_norm_sq_eq]
  field_simp [norm_ne_zero_iff.mpr hx]

theorem hydrogenFirstL2_norm_sum (Z : ℝ) (hZ : 0 < Z) :
    (∑ k : Coordinate 1, ‖hydrogenFirstL2 Z hZ k‖^2) =
      Z^2 * ‖hydrogenRadialL2 Z hZ‖^2 := by
  simp_rw [spatialL2_norm_sq_eq_integral]
  rw [← integral_finsetSum Finset.univ (fun k _ =>
    (Lp.memLp (hydrogenFirstL2 Z hZ k)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)),
    ← integral_const_mul]
  have hd : ∀ᵐ x ∂volume, ∀ k : Coordinate 1,
      hydrogenFirstL2 Z hZ k x = hydrogenFirst Z k x := by
    rw [ae_all_iff]
    intro k
    exact (hydrogen_first_memLp hZ k).coeFn_toLp
  apply integral_congr_ae
  filter_upwards [hd,hydrogenRadialL2_coe_ae Z hZ,hydrogen_ae_ne_zero] with x hd hf hx
  simp_rw [hd,hf]
  exact hydrogenFirst_pointwise_norm_sum Z hx

def normalizedHydrogenGradient (Z : ℝ) (hZ : 0 < Z) (k : Coordinate 1) : SpatialL2 1 :=
  (‖hydrogenRadialL2 Z hZ‖⁻¹ : ℂ) • hydrogenFirstL2 Z hZ k

theorem normalizedHydrogenGradient_weak (Z : ℝ) (hZ : 0 < Z) (k : Coordinate 1) :
    WeakPartial (normalizedPolarGround configuration_one_finrank Z hZ)
      (normalizedHydrogenGradient Z hZ k) k := by
  rw [normalizedPolarGround,polarGroundL2_eq_hydrogen]
  exact weakPartial_smul _ (hydrogen_first_weakPartial hZ k)

theorem normalizedHydrogenGradient_norm_sum (Z : ℝ) (hZ : 0 < Z) :
    (∑ k : Coordinate 1, ‖normalizedHydrogenGradient Z hZ k‖^2) = Z^2 := by
  simp only [normalizedHydrogenGradient,norm_smul,mul_pow,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_norm,← Finset.mul_sum]
  rw [hydrogenFirstL2_norm_sum]
  field_simp [norm_ne_zero_iff.mpr (hydrogenRadialL2_ne_zero Z hZ)]

theorem normalizedHydrogenGradient_electron_norm_sum (Z : ℝ) (hZ : 0 < Z) :
    (∑ k : Fin 3, ‖normalizedHydrogenGradient Z hZ (0,k)‖^2) = Z^2 := by
  simpa only [Coordinate,Fintype.sum_prod_type,Fin.sum_univ_one] using
    normalizedHydrogenGradient_norm_sum Z hZ

#print axioms hydrogenFirst_pointwise_norm_sum
#print axioms hydrogenFirstL2_norm_sum
#print axioms normalizedHydrogenGradient_weak
#print axioms normalizedHydrogenGradient_norm_sum
end TheoremT.Continuum
