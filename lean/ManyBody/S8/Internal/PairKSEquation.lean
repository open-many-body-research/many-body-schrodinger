import ManyBody.S8.Internal.PairKSGeometry
import ManyBody.S8.Internal.PairKSLaplacian
import CoulombNuclearKSWeak_v1

/-! The electron-pair KS classical and weak equations are derived from the
original two-electron Hamiltonian graph. Hadamard covariance preserves its
kinetic metric. The exact cleared coefficient has principal c=4 and constant
8/sqrt(2). Continuous Grushin removability extends the equation across the
selected pair collision in the patch excluding the original nuclei. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace ManyBody.S8
open TheoremT.Continuum

theorem pair_KS_principal_identity {g : Configuration 2 → ℂ} (q : PairKSSpace)
    (hg : ContDiffAt ℝ 2 g (pairKSLift q)) :
    nuclearKSPrincipal (1 : Fin 2) (g ∘ pairKSLift) q =
      (4*‖q.1‖^2) • smoothLaplacian g (pairKSLift q) := by
  have hg' : ContDiffAt ℝ 2 g
      (twoElectronRelativeEquiv (nuclearKSLift (1 : Fin 2) q)) := hg
  have hR : ContDiffAt ℝ 2 (fun z : Configuration 2 => twoElectronRelativeEquiv z)
      (nuclearKSLift (1 : Fin 2) q) :=
    twoElectronRelativeEquiv.toContinuousLinearEquiv.contDiff.contDiffAt
  have hrel : ContDiffAt ℝ 2 (g ∘ twoElectronRelativeEquiv)
      (nuclearKSLift (1 : Fin 2) q) :=
    hg'.comp (nuclearKSLift (1 : Fin 2) q) hR
  change nuclearKSPrincipal (1 : Fin 2)
    ((g ∘ twoElectronRelativeEquiv) ∘ nuclearKSLift (1 : Fin 2)) q = _
  rw [nuclear_KS_principal_identity (1 : Fin 2) q hrel,
    relative_smoothLaplacian _ hg]
  rfl

theorem scalar_coulomb_pair_KS_classical_equation {Z E : ℝ} {f : SpatialL2 2}
    (hgraph : scalarHamiltonianGraph 2 Z f ((E : ℂ) • f))
    {g : Configuration 2 → ℂ} (hg : Continuous g)
    (hfg : (f : Configuration 2 → ℂ) =ᵐ[volume] g)
    (q : PairKSSpace) (hq : q ∈ pairKSCoefficientPatch) (hy : q.1 ≠ 0) :
    ContDiffAt ℝ ∞ (g ∘ pairKSLift) q ∧
      nuclearKSPrincipal (1 : Fin 2) (g ∘ pairKSLift) q =
        pairKSPotential Z E q • (g ∘ pairKSLift) q := by
  have hx := pairKSCoefficientPatch_off_zero_collisionFree hq hy
  have hgs := scalar_coulomb_continuous_rep_smooth_away hgraph hg hfg hx
  refine ⟨hgs.comp q pairKSLift_contDiff.contDiffAt,?_⟩
  rw [pair_KS_principal_identity q (hgs.of_le (by simp)),
    scalar_coulomb_continuous_rep_pointwise_equation hgraph hg hfg hx,
    pairKSPotential_eq_coulomb_scaled Z E q hy]
  simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_sub,
    Complex.ofReal_ofNat,Function.comp_apply]
  ring

theorem scalar_coulomb_pair_KS_off_zero_weak {Z E : ℝ} {f : SpatialL2 2}
    (hgraph : scalarHamiltonianGraph 2 Z f ((E : ℂ) • f))
    {g : Configuration 2 → ℂ} (hg : Continuous g)
    (hfg : (f : Configuration 2 → ℂ) =ᵐ[volume] g)
    {φ : PairKSSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ pairKSCoefficientPatch \ {q | q.1=0}) :
    Integrable (fun q => (splitGrushin 4 spectatorBasis (pairKSPotential Z E) φ q : ℂ)*
      (g ∘ pairKSLift) q) volume ∧
    (∫ q, (splitGrushin 4 spectatorBasis (pairKSPotential Z E) φ q : ℂ)*
      (g ∘ pairKSLift) q)=0 := by
  have hh (q : PairKSSpace) (hq : q ∈ tsupport φ) :=
    scalar_coulomb_pair_KS_classical_equation hgraph hg hfg q (hs hq).1 (hs hq).2
  exact nuclear_KS_local_classical_kernel_weak (1 : Fin 2) hφ hc
    (fun q hq => (hh q hq).1)
    (fun q hq => pairKSPotential_contDiffAt Z E (hs hq).1)
    (fun q hq => (hh q hq).2)

/-- The actual weak equation and integrability hold across the selected pair collision. -/
theorem scalar_coulomb_pair_KS_weak {Z E : ℝ} {f : SpatialL2 2}
    (hgraph : scalarHamiltonianGraph 2 Z f ((E : ℂ) • f))
    {g : Configuration 2 → ℂ} (hg : Continuous g)
    (hfg : (f : Configuration 2 → ℂ) =ᵐ[volume] g)
    {φ : PairKSSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ pairKSCoefficientPatch) :
    Integrable (fun q => (splitGrushin 4 spectatorBasis (pairKSPotential Z E) φ q : ℂ)*
      (g ∘ pairKSLift) q) volume ∧
    (∫ q, (splitGrushin 4 spectatorBasis (pairKSPotential Z E) φ q : ℂ)*
      (g ∘ pairKSLift) q)=0 := by
  have hw : ∀ ψ : PairKSSpace → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ pairKSCoefficientPatch \ {q | q.1=0} →
      (∫ q, (splitGrushin 4 spectatorBasis (pairKSPotential Z E) ψ q : ℂ)*
        (g ∘ pairKSLift) q) = ∫ q, (ψ q : ℂ)*(0:ℂ) := by
    intro ψ hψ hcψ hsψ
    simpa only [mul_zero,integral_zero] using
      (scalar_coulomb_pair_KS_off_zero_weak hgraph hg hfg hψ hcψ hsψ).2
  have hh := nuclear_KS_local_coefficient_Grushin_removability (1 : Fin 2) 4 spectatorBasis
    pairKSCoefficientPatch_isOpen (fun q hq => pairKSPotential_contDiffAt Z E hq)
    (hg.comp pairKSLift_contDiff.continuous) (f := fun _ => (0:ℂ)) continuous_const
    hw hφ hc hs
  exact ⟨hh.1,by simpa only [mul_zero,integral_zero] using hh.2.2⟩

#print axioms pair_KS_principal_identity
#print axioms scalar_coulomb_pair_KS_classical_equation
#print axioms scalar_coulomb_pair_KS_weak
end ManyBody.S8