import WeakGrushinPotentialForcingCompact_v1
import WeakGrushinJetLimits_v1

/-! Existence of finite compact coefficient bounds, before the solution data.
The aggregate spectator derivative bound remains explicit. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem l2_setIntegral_norm_sq_le (f : Lp ℂ 2 (volume : Measure (Space κ)))
    (K : Set (Space κ)) : (∫ p in K, ‖f p‖^2) ≤ ‖f‖^2 := by
  rw [l2_norm_sq_integral]
  exact setIntegral_le_integral ((Lp.memLp f).integrable_norm_pow (by norm_num))
    (Eventually.of_forall (fun p => sq_nonneg ‖f p‖))

theorem compact_spectator_coefficient_bounds_exist
    {Ω K : Set (Space κ)} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {B : Space κ → ℝ} (hB : ContDiffOn ℝ ∞ B Ω) :
    ∃ b b1 : ℝ, 0 ≤ b ∧ 0 ≤ b1 ∧
      (∀ p ∈ K, |B p| ≤ b) ∧
      (∀ p ∈ K, (∑ j, |fderiv ℝ B p (0,oscillatorBasis j)|^2) ≤ b1^2) := by
  obtain ⟨b,hb⟩ := hK.exists_bound_of_continuousOn (hB.continuousOn.mono hKΩ)
  have hD (j : κ) : ContinuousOn (fun p => fderiv ℝ B p (0,oscillatorBasis j)) Ω := by
    intro p hp
    exact (local_contDiffAt_directional_derivative (hB.contDiffAt (hΩ.mem_nhds hp))
      ((0 : EuclideanSpace ℝ (Fin 4)),oscillatorBasis j)).continuousAt.continuousWithinAt
  have hsum : ContinuousOn (fun p => ∑ j, |fderiv ℝ B p (0,oscillatorBasis j)|^2) K :=
    continuousOn_finsetSum _ (fun j _ => ((hD j).abs.pow 2).mono hKΩ)
  obtain ⟨q,hq⟩ := hK.exists_bound_of_continuousOn hsum
  refine ⟨|b|,|q|+1,abs_nonneg b,by positivity,?_,?_⟩
  · intro p hp
    have hbp : |B p| ≤ b := by simpa only [Real.norm_eq_abs] using hb p hp
    exact hbp.trans (le_abs_self b)
  · intro p hp
    have hqp : |∑ j, |fderiv ℝ B p (0,oscillatorBasis j)|^2| ≤ q := by
      simpa only [Real.norm_eq_abs] using hq p hp
    have hh : (∑ j, |fderiv ℝ B p (0,oscillatorBasis j)|^2) ≤ |q| :=
      (le_abs_self _).trans (hqp.trans (le_abs_self q))
    have hpos := abs_nonneg q
    nlinarith [sq_nonneg (|q|)]

#print axioms l2_setIntegral_norm_sq_le
#print axioms compact_spectator_coefficient_bounds_exist
end TheoremT.Continuum.WeakGrushin
