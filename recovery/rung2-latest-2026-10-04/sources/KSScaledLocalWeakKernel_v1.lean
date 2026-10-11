import KSScaledPrincipalIBP_v1
import GrushinHoleCommutator_v1

/-! A local classical kernel identity gives the actual compact-test weak
equation for a supplied real Grushin spectator coefficient. This implication
assumes the local classical equation; it does not assert a physical pullback. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum

theorem ks_scaled_local_classical_kernel_weak {N : ℕ} (i : Fin N) (c : ℝ)
    {φ B : NuclearKSSpace i → ℝ} {u : NuclearKSSpace i → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hu : ∀ q ∈ tsupport φ, ContDiffAt ℝ ∞ u q)
    (hB : ∀ q ∈ tsupport φ, ContDiffAt ℝ ∞ B q)
    (hP : ∀ q ∈ tsupport φ, ksScaledPrincipal i c u q=B q • u q) :
    Integrable (fun q => (splitGrushin c spectatorBasis B φ q : ℂ)*u q) volume ∧
      (∫ q, (splitGrushin c spectatorBasis B φ q : ℂ)*u q)=0 := by
  have hi := ks_scaled_principal_integration_by_parts i c hφ hc hu
  have hT : Integrable (fun q => (B q*φ q) • u q) volume := by
    have ht := local_smooth_test_smul_integrable (μ := volume) hφ hc
      (fun q hq => (hB q hq).smul (hu q hq))
    convert ht using 1
    funext q
    rw [mul_smul,smul_comm]
    rfl
  have he : (fun q => φ q • ksScaledPrincipal i c u q)=(fun q => (B q*φ q) • u q) := by
    funext q
    by_cases hq : q ∈ tsupport φ
    · rw [hP q hq,mul_smul,smul_comm]
    · have hz := image_eq_zero_of_notMem_tsupport hq
      simp [hz]
  have hQ : (fun q => (splitGrushin c spectatorBasis B φ q : ℂ)*u q)=
      fun q => -(ksScaledRealPrincipal i c φ q • u q)+(B q*φ q) • u q := by
    funext q
    simp only [splitGrushin,ksScaledRealPrincipal,Complex.real_smul,Complex.ofReal_add,
      Complex.ofReal_sub,Complex.ofReal_neg,Complex.ofReal_mul,Complex.ofReal_ofNat]
    ring
  rw [hQ]
  refine ⟨hi.1.neg.add hT,?_⟩
  have hneg : Integrable (fun q => -(ksScaledRealPrincipal i c φ q • u q)) volume := hi.1.neg
  rw [integral_add hneg hT,integral_neg,hi.2.2,he]
  simp

#print axioms ks_scaled_local_classical_kernel_weak
end TheoremT.Continuum
