import HalfLineIntegratingFactor_v1

/-! The actual weak hydrogen radial equation determines its kernel without an
assumed absolutely continuous representative or a formal adjoint domain. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace TheoremT.OneDimensional

theorem radialWeight_inverse (Z x : ℝ) (hx : x ≠ 0) :
    (x*Real.exp (-Z*x))*radialWeight Z x = 1 := by
  rw [radialWeight, show -Z*x = -(Z*x) by ring, Real.exp_neg]
  field_simp

theorem weak_radial_ode_kernel (Z : ℝ) (f : ℝ → ℂ)
    (hf : LocallyIntegrableOn f (Ioi (0 : ℝ)))
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioi (0 : ℝ) →
      ∫ x, (-deriv ψ x-ψ x/x+Z*ψ x) • f x = 0) :
    ∃ c : ℂ, ∀ᵐ x, x ∈ Ioi (0 : ℝ) →
      f x = (x*Real.exp (-Z*x)) • c := by
  let F : ℝ → ℂ := fun x => radialWeight Z x • f x
  have hF : LocallyIntegrableOn F (Ioi (0 : ℝ)) :=
    LocallyIntegrableOn.continuousOn_smul isOpen_Ioi.isLocallyClosed hf
      (radialWeight_continuousOn Z)
  have hFw : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioi (0 : ℝ) → ∫ x, deriv ψ x • F x = 0 := by
    intro ψ hψ hψc hψs
    have hzero := hweak (fun x => ψ x*radialWeight Z x)
      (radial_weighted_test_contDiff Z ψ hψ hψs)
      (radial_weighted_test_compact Z ψ hψc)
      (radial_weighted_test_tsupport Z ψ hψs)
    have heq : (fun x => (-deriv (fun y => ψ y*radialWeight Z y) x
        -(ψ x*radialWeight Z x)/x+Z*(ψ x*radialWeight Z x)) • f x) =
        (fun x => -(deriv ψ x • F x)) := by
      funext x
      rw [radial_weighted_test_identity Z ψ hψ hψs x]
      simp only [neg_mul,neg_smul,mul_smul,F]
    rw [heq,integral_neg] at hzero
    exact neg_eq_zero.mp hzero
  obtain ⟨c,hc⟩ := weak_derivative_zero_halfline_constant F hF hFw
  refine ⟨c,?_⟩
  filter_upwards [hc] with x hx
  intro hpos
  have he := congrArg (fun z : ℂ => (x*Real.exp (-Z*x)) • z) (hx hpos)
  simpa only [F,smul_smul,radialWeight_inverse Z x (ne_of_gt hpos),one_smul] using he

theorem weak_radial_ode_kernel_restrict (Z : ℝ) (f : ℝ → ℂ)
    (hf : LocallyIntegrableOn f (Ioi (0 : ℝ)))
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioi (0 : ℝ) →
      ∫ x, (-deriv ψ x-ψ x/x+Z*ψ x) • f x = 0) :
    ∃ c : ℂ, f =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun x => (x*Real.exp (-Z*x)) • c) := by
  obtain ⟨c,hc⟩ := weak_radial_ode_kernel Z f hf hweak
  exact ⟨c,(ae_restrict_iff' measurableSet_Ioi).mpr hc⟩

#print axioms radialWeight_inverse
#print axioms weak_radial_ode_kernel
#print axioms weak_radial_ode_kernel_restrict
end TheoremT.OneDimensional
