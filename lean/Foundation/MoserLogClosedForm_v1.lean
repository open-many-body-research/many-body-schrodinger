import MoserLogSeries_v1
import CoulombMoserUniform_v1

noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

theorem moserLogWeight_tsum {B c : ℝ} (hc : 1 < c) :
    ∑' k, moserLogWeight B c k =
      Real.log B*(c/(c-1))+2*Real.log c*(c/(c-1)^2) := by
  have hc0 : 0 < c := by linarith
  have hi0 : 0 ≤ c⁻¹ := inv_nonneg.mpr hc0.le
  have hi1 : c⁻¹ < 1 := (inv_lt_one₀ hc0).mpr hc
  have hin : ‖c⁻¹‖ < 1 := by rwa [Real.norm_eq_abs,abs_of_nonneg hi0]
  have he : moserLogWeight B c = (fun k : ℕ =>
      Real.log B*(c⁻¹)^k+(2*Real.log c)*((k:ℝ)*(c⁻¹)^k)) := by
    funext k; unfold moserLogWeight; ring
  rw [he]
  have hsum := ((hasSum_geometric_of_lt_one hi0 hi1).mul_left (Real.log B)).add
    ((hasSum_coe_mul_geometric_of_norm_lt_one hin).mul_left (2*Real.log c))
  rw [hsum.tsum_eq]
  have hc1 : c-1 ≠ 0 := by linarith
  field_simp
  <;> ring

theorem coulombMoserBoundCoefficient_closed {N : ℕ} (hN : 0 < N) (Z E : ℝ) :
    coulombMoserBoundCoefficient N Z E =
      (coulombMoserBase N Z E)^(atomicMoserRatio N/(atomicMoserRatio N-1))*
      (atomicMoserRatio N)^(2*atomicMoserRatio N/(atomicMoserRatio N-1)^2) := by
  have hb : 0 < coulombMoserBase N Z E := lt_of_lt_of_le zero_lt_one (coulombMoserBase_ge_one N Z E)
  have hc : 0 < atomicMoserRatio N := lt_trans zero_lt_one (atomicMoserRatio_gt_one hN)
  rw [coulombMoserBoundCoefficient,moserLogWeight_tsum (atomicMoserRatio_gt_one hN),
    Real.rpow_def_of_pos hb,Real.rpow_def_of_pos hc,← Real.exp_add]
  congr 1; ring

#print axioms coulombMoserBoundCoefficient_closed
end TheoremT.Continuum
