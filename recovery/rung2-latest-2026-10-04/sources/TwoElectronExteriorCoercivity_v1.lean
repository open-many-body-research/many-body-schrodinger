import TwoElectronScalarRankOne_v1
import TwoElectronUniformGap_v1
import ExteriorOverlap_v1

/-! Actual exterior H¹ form coercivity relative to the full fermionic ground
energy. The positive constant is explicit; the finite radius is existential.
No ionization-threshold or unproved eigenfunction decay premise is used. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum
open TheoremT.Polar

theorem twoElectron_exterior_coercivity (Z : ℝ) (hZ : 2 ≤ Z) :
    ∃ R : ℝ, 0 < R ∧ ∀ (f : SpatialL2 2) (q : ℝ),
      scalarCoulombH1FormValue 2 Z f q →
      (∀ᵐ x, ‖x‖ ≤ R → f x = 0) →
      (Z^2/112) * ‖f‖^2 ≤ q - (variationalGroundEnergy 2 Z).toReal * ‖f‖^2 := by
  have hp : 0 < Z := lt_of_lt_of_le (by norm_num) hZ
  obtain ⟨R,hR,hsmall⟩ := exists_radius_exterior_overlap_small
    (twoElectronTensor (normalizedPolarGround configuration_one_finrank Z hp)
      (normalizedPolarGround configuration_one_finrank Z hp)) (by norm_num : (0 : ℝ) < 1/7)
  refine ⟨R,hR,fun f q hq hv => ?_⟩
  have hb := twoElectron_scalar_h1_rank_one Z hp hq
  have hov := hsmall f hv
  have hs := pow_le_pow_left₀ (norm_nonneg _) hov 2
  have hdef := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 3*Z^2/8)
  have hgap := mul_le_mul_of_nonneg_right (twoElectron_ground_separator_gap Z hZ)
    (sq_nonneg ‖f‖)
  nlinarith [mul_nonneg (sq_nonneg Z) (sq_nonneg ‖f‖)]

#print axioms twoElectron_exterior_coercivity
end TheoremT.Continuum
