import HalfLineFactorWeakTest_v1
import HalfLineWeakODE_v1

/-! Orthogonality to the actual closed partner range forces the explicit
hydrogen radial profile. No endpoint or eigenfunction premise is used. -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace TheoremT.HalfLine

theorem weak_ode_integral_eq_restrict (Z : ℝ) (f : ℝ → ℂ)
    (φ : ℝ → ℝ) (hs : tsupport φ ⊆ Ioi (0:ℝ)) :
    (∫ x, (-deriv φ x - φ x / x + Z * φ x) • f x) =
      ∫ x, (-deriv φ x - φ x / x + Z * φ x) • f x ∂μ := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hn : x ∉ tsupport φ := fun hm => hx (hs hm)
  have hv := image_eq_zero_of_notMem_tsupport hn
  have hd := deriv_of_notMem_tsupport (f := φ) hn
  simp [hv,hd]

theorem range_orthogonal_profile {Z : ℝ} {f : E} (hf : f ∈ (B Z).range.orthogonal) :
    ∃ c : ℂ, (f : ℝ → ℂ) =ᵐ[μ] fun x => (x * Real.exp (-Z*x)) • c := by
  apply OneDimensional.weak_radial_ode_kernel_restrict Z f
  · exact locallyIntegrableOn_of_locallyIntegrable_restrict
      ((Lp.memLp f).locallyIntegrable (by norm_num))
  · intro φ hφ hc hs
    rw [weak_ode_integral_eq_restrict Z f φ hs]
    exact range_orthogonal_real_test hf φ hφ hc hs

#print axioms weak_ode_integral_eq_restrict
#print axioms range_orthogonal_profile
end TheoremT.HalfLine
