import NuclearKSPrincipalIBP_v1
import GrushinHoleCommutator_v1

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum

theorem nuclear_KS_local_classical_kernel_weak {N : ℕ} (i : Fin N)
    {φ B : NuclearKSSpace i → ℝ} {u : NuclearKSSpace i → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hu : ∀ q ∈ tsupport φ, ContDiffAt ℝ ∞ u q)
    (hB : ∀ q ∈ tsupport φ, ContDiffAt ℝ ∞ B q)
    (hP : ∀ q ∈ tsupport φ, nuclearKSPrincipal i u q=B q • u q) :
    Integrable (fun q => (splitGrushin 4 spectatorBasis B φ q : ℂ)*u q) volume ∧
      (∫ q, (splitGrushin 4 spectatorBasis B φ q : ℂ)*u q)=0 := by
  have hi := nuclear_KS_principal_integration_by_parts i hφ hc hu
  have hT : Integrable (fun q => (B q*φ q) • u q) volume := by
    have ht := local_smooth_test_smul_integrable (μ := volume) hφ hc
      (fun q hq => (hB q hq).smul (hu q hq))
    convert ht using 1
    funext q
    rw [mul_smul,smul_comm]
    rfl
  have he : (fun q => φ q • nuclearKSPrincipal i u q)=(fun q => (B q*φ q) • u q) := by
    funext q
    by_cases hq : q ∈ tsupport φ
    · rw [hP q hq,mul_smul,smul_comm]
    · have hz := image_eq_zero_of_notMem_tsupport hq
      simp [hz]
  have hQ : (fun q => (splitGrushin 4 spectatorBasis B φ q : ℂ)*u q)=
      fun q => -(nuclearKSRealPrincipal i φ q • u q)+(B q*φ q) • u q := by
    funext q
    simp only [splitGrushin,nuclearKSRealPrincipal,Complex.real_smul,Complex.ofReal_add,
      Complex.ofReal_sub,Complex.ofReal_neg,Complex.ofReal_mul,Complex.ofReal_ofNat]
    ring
  rw [hQ]
  refine ⟨hi.1.neg.add hT,?_⟩
  have hneg : Integrable (fun q => -(nuclearKSRealPrincipal i φ q • u q)) volume := hi.1.neg
  rw [integral_add hneg hT,integral_neg,hi.2.2,he]
  simp

#print axioms nuclear_KS_local_classical_kernel_weak
end TheoremT.Continuum
