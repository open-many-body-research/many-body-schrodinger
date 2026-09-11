import HydrogenWeak_v1

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum

/-- The constant-one nuclear Coulomb uncertainty inequality on the actual weak H¹
configuration space, using only the three derivatives of the selected electron. -/
theorem weak_nuclear_coulomb_uncertainty {N : ℕ} (i : Fin N)
    (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) :
    (∫ x : Configuration N, ‖f x‖^2 / ‖position x i‖) ≤
      ‖f‖ * Real.sqrt (∑ k : Fin 3, ‖d (i,k)‖^2) := by
  by_cases hf : f = 0
  · subst f
    have he : (fun x : Configuration N => ‖(0 : SpatialL2 N) x‖^2 / ‖position x i‖) =ᵐ[volume]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [Lp.coeFn_zero ℂ 2 volume] with x hx
      rw [hx]
      simp
    rw [integral_congr_ae he]
    simp
  · have hA : 0 < ‖f‖ := norm_pos_iff.mpr hf
    let I : ℝ := ∫ x : Configuration N, ‖f x‖^2 / ‖position x i‖
    let G : ℝ := ∑ k : Fin 3, ‖d (i,k)‖^2
    have hI : 0 ≤ I := integral_nonneg (fun x => by positivity)
    have hG : 0 ≤ G := Finset.sum_nonneg (fun k _ => sq_nonneg _)
    have hb := (weak_nuclear_coulomb_bound i
      (t := I / ‖f‖^2) (by positivity) f d hd).2
    change 2*(I/‖f‖^2)*I ≤ G + (I/‖f‖^2)^2*‖f‖^2 at hb
    have hh := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖f‖)
    have hsq : I^2 ≤ ‖f‖^2 * G := by
      field_simp [hA.ne'] at hh
      nlinarith [hh]
    change I ≤ ‖f‖ * Real.sqrt G
    apply (sq_le_sq₀ hI (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt hG]
    exact hsq

#print axioms weak_nuclear_coulomb_uncertainty
end TheoremT.Continuum
