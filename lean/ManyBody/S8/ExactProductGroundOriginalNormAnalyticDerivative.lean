import ManyBody.S8.ExactProductGroundPointwise
import ManyBody.S8.CoulombSpinPhysicalOriginalNormAnalyticDerivative

/-! The actual exact-product ground branch obtains one normalized ground state
and one all-spin representative with state-independent original-norm derivative
budgets, fixed unit physical Lipschitz ball and every scale epsilon≤1/4.
The spectral/singlet conclusions and literal recovered derivative data are
retained. Original recovered coordinate and coefficient conventions are unchanged. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Metric
open scoped ContDiff NNReal BigOperators
namespace ManyBody.S8
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin

set_option maxHeartbeats 1200000 in
theorem exactProduct_physical_ground_original_norm_analytic_derivative
    (Z : ℝ) (hZ : 0 < Z) (hα : 0 < Z-5/16)
    (hsep : 5*Z^2/8 < (Z-5/16)^2) :
    ∃ M A : ℝ, ∃ C_L : ℝ≥0, ∃ Csrc CH12 : ℝ,
      1 ≤ M ∧ 1 ≤ A ∧ 0 ≤ Csrc ∧ 0 ≤ CH12 ∧
      ∃ g : (coulombPartialOperator 2 Z).domain,
      ‖(g : FermionicSpace 2)‖ = 1 ∧
      coulombPartialOperator 2 Z g =
        ((variationalGroundEnergy 2 Z).toReal : ℂ) • (g : FermionicSpace 2) ∧
      spectralGroundEnergy 2 Z = ((variationalGroundEnergy 2 Z).toReal : EReal) ∧
      (((variationalGroundEnergy 2 Z).toReal : ℂ) ∈
        TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator 2 Z)) ∧
      (∀ z ∈ TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator 2 Z),
        (variationalGroundEnergy 2 Z).toReal ≤ z.re) ∧
      ∃ F : SpatialL2 2, ‖F‖ = 1 ∧ pullback twoElectronSwap F = F ∧ HasH2 F ∧
        scalarHamiltonianGraph 2 Z F
          (((variationalGroundEnergy 2 Z).toReal : ℂ) • F) ∧
        (g : FermionicSpace 2).val = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • spinSingletLift F ∧
      ∃ u : SpinConfiguration 2 → Configuration 2 → ℂ,
        (∀ σ, LocallyLipschitz (u σ)) ∧
        (∀ σ, LipschitzOnWith (C_L * ‖(g : FermionicSpace 2).val‖₊) (u σ) (ball 0 1)) ∧
        (∀ᵐ x ∂volume, ∀ σ, (g : FermionicSpace 2).val σ x = u σ x) ∧
        (∀ π : Equiv.Perm (Fin 2), ∀ σ, ∀ x,
          u (permuteSpin π σ) (permuteSpace π x) = permutationSign π • u σ x) ∧
        (∀ x, Real.sqrt (∑ σ : SpinConfiguration 2, ‖u σ x‖^2) ≤
          coulombMoserBoundCoefficient 2 Z (variationalGroundEnergy 2 Z).toReal * ‖(g : FermionicSpace 2).val‖) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ 1/4 →
          ∀ (σ : SpinConfiguration 2) (i : Fin 2) (t0 : Position), ‖t0‖ = 1 →
            PhysicalKSBoxAnalyticDescentDerivativeData
              ((originScaledDifference (u σ) ε ∘ nuclearKSLift i) ∘
                (physicalSpectatorReindexAt i).symm)
              (fun X T => originScaledDifference (u σ) ε (nuclearKSPhysicalCoordinates i X T))
              t0 M A Csrc CH12) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ 1/4 →
          ∀ (σ : SpinConfiguration 2) (t0 : Position), ‖t0‖ = 1 →
            PhysicalKSBoxAnalyticDescentDerivativeData
              ((originScaledDifference (u σ) ε ∘ TheoremT.Continuum.pairKSLift) ∘
                (physicalSpectatorReindexAt (0 : Fin 2)).symm)
              (fun X T => originScaledDifference (u σ) ε (pairKSPhysicalCoordinates X T))
              t0 M A Csrc CH12) := by
  obtain ⟨M,A,C_L,Csrc,CH12,hM,hA,hsrc,hH12,hgain⟩ :=
    coulomb_spin_physical_original_norm_analytic_derivative
      Z (variationalGroundEnergy 2 Z).toReal
  obtain ⟨_,_,_,_,_,_,g,hg,hEg,hspec,hmem,hlower,
    F,hF,hFS,hH2,hFgraph,hSinglet,_⟩ :=
    exactProduct_physical_ground_pointwise Z hZ hα hsep
  have hgraph : hamiltonianGraph 2 Z (g : FermionicSpace 2).val
      (((variationalGroundEnergy 2 Z).toReal : ℂ) • (g : FermionicSpace 2).val) := by
    have hh := coulombPartialOperator_apply_graph 2 Z g
    rw [hEg] at hh
    exact hh
  obtain ⟨u,hu,hLip,hAE,hperm,hbound,hN,hP⟩ :=
    hgain (g : FermionicSpace 2).val hgraph
  have hnorm : ‖(g : FermionicSpace 2).val‖ = 1 := hg
  refine ⟨M,A,C_L,Csrc,CH12,hM,hA,hsrc,hH12,g,hg,hEg,hspec,hmem,hlower,
    F,hF,hFS,hH2,hFgraph,hSinglet,u,hu,hLip,hAE,hperm,hbound,?_,?_⟩
  · intro ε hε hlim σ i t0 ht0
    simpa only [hnorm, one_pow, mul_one] using (hN ε hε hlim σ i t0 ht0).1
  · intro ε hε hlim σ t0 ht0
    simpa only [hnorm, one_pow, mul_one] using (hP ε hε hlim σ t0 ht0).1

theorem exactProduct_physical_ground_original_norm_analytic_derivative_above_threshold
    (Z : ℝ) (hZ : (20+5*Real.sqrt 10)/24 < Z) :
    ∃ M A : ℝ, ∃ C_L : ℝ≥0, ∃ Csrc CH12 : ℝ,
      1 ≤ M ∧ 1 ≤ A ∧ 0 ≤ Csrc ∧ 0 ≤ CH12 ∧
      ∃ g : (coulombPartialOperator 2 Z).domain,
      ‖(g : FermionicSpace 2)‖ = 1 ∧
      coulombPartialOperator 2 Z g =
        ((variationalGroundEnergy 2 Z).toReal : ℂ) • (g : FermionicSpace 2) ∧
      spectralGroundEnergy 2 Z = ((variationalGroundEnergy 2 Z).toReal : EReal) ∧
      (((variationalGroundEnergy 2 Z).toReal : ℂ) ∈
        TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator 2 Z)) ∧
      (∀ z ∈ TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator 2 Z),
        (variationalGroundEnergy 2 Z).toReal ≤ z.re) ∧
      ∃ F : SpatialL2 2, ‖F‖ = 1 ∧ pullback twoElectronSwap F = F ∧ HasH2 F ∧
        scalarHamiltonianGraph 2 Z F
          (((variationalGroundEnergy 2 Z).toReal : ℂ) • F) ∧
        (g : FermionicSpace 2).val = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • spinSingletLift F ∧
      ∃ u : SpinConfiguration 2 → Configuration 2 → ℂ,
        (∀ σ, LocallyLipschitz (u σ)) ∧
        (∀ σ, LipschitzOnWith (C_L * ‖(g : FermionicSpace 2).val‖₊) (u σ) (ball 0 1)) ∧
        (∀ᵐ x ∂volume, ∀ σ, (g : FermionicSpace 2).val σ x = u σ x) ∧
        (∀ π : Equiv.Perm (Fin 2), ∀ σ, ∀ x,
          u (permuteSpin π σ) (permuteSpace π x) = permutationSign π • u σ x) ∧
        (∀ x, Real.sqrt (∑ σ : SpinConfiguration 2, ‖u σ x‖^2) ≤
          coulombMoserBoundCoefficient 2 Z (variationalGroundEnergy 2 Z).toReal * ‖(g : FermionicSpace 2).val‖) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ 1/4 →
          ∀ (σ : SpinConfiguration 2) (i : Fin 2) (t0 : Position), ‖t0‖ = 1 →
            PhysicalKSBoxAnalyticDescentDerivativeData
              ((originScaledDifference (u σ) ε ∘ nuclearKSLift i) ∘
                (physicalSpectatorReindexAt i).symm)
              (fun X T => originScaledDifference (u σ) ε (nuclearKSPhysicalCoordinates i X T))
              t0 M A Csrc CH12) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ 1/4 →
          ∀ (σ : SpinConfiguration 2) (t0 : Position), ‖t0‖ = 1 →
            PhysicalKSBoxAnalyticDescentDerivativeData
              ((originScaledDifference (u σ) ε ∘ TheoremT.Continuum.pairKSLift) ∘
                (physicalSpectatorReindexAt (0 : Fin 2)).symm)
              (fun X T => originScaledDifference (u σ) ε (pairKSPhysicalCoordinates X T))
              t0 M A Csrc CH12) := by
  obtain ⟨hZ0,hα,hsep⟩ := ManyBody.S2.exactProduct_charge_conditions Z hZ
  exact exactProduct_physical_ground_original_norm_analytic_derivative Z hZ0 hα hsep

theorem exactProduct_three_halves_physical_original_norm_analytic_derivative :
    ∃ M A : ℝ, ∃ C_L : ℝ≥0, ∃ Csrc CH12 : ℝ,
      1 ≤ M ∧ 1 ≤ A ∧ 0 ≤ Csrc ∧ 0 ≤ CH12 ∧
      ∃ g : (coulombPartialOperator 2 (3/2 : ℝ)).domain,
      ‖(g : FermionicSpace 2)‖ = 1 ∧
      coulombPartialOperator 2 (3/2 : ℝ) g =
        ((variationalGroundEnergy 2 (3/2 : ℝ)).toReal : ℂ) • (g : FermionicSpace 2) ∧
      spectralGroundEnergy 2 (3/2 : ℝ) = ((variationalGroundEnergy 2 (3/2 : ℝ)).toReal : EReal) ∧
      (((variationalGroundEnergy 2 (3/2 : ℝ)).toReal : ℂ) ∈
        TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator 2 (3/2 : ℝ))) ∧
      (∀ z ∈ TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator 2 (3/2 : ℝ)),
        (variationalGroundEnergy 2 (3/2 : ℝ)).toReal ≤ z.re) ∧
      ∃ F : SpatialL2 2, ‖F‖ = 1 ∧ pullback twoElectronSwap F = F ∧ HasH2 F ∧
        scalarHamiltonianGraph 2 (3/2 : ℝ) F
          (((variationalGroundEnergy 2 (3/2 : ℝ)).toReal : ℂ) • F) ∧
        (g : FermionicSpace 2).val = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • spinSingletLift F ∧
      ∃ u : SpinConfiguration 2 → Configuration 2 → ℂ,
        (∀ σ, LocallyLipschitz (u σ)) ∧
        (∀ σ, LipschitzOnWith (C_L * ‖(g : FermionicSpace 2).val‖₊) (u σ) (ball 0 1)) ∧
        (∀ᵐ x ∂volume, ∀ σ, (g : FermionicSpace 2).val σ x = u σ x) ∧
        (∀ π : Equiv.Perm (Fin 2), ∀ σ, ∀ x,
          u (permuteSpin π σ) (permuteSpace π x) = permutationSign π • u σ x) ∧
        (∀ x, Real.sqrt (∑ σ : SpinConfiguration 2, ‖u σ x‖^2) ≤
          coulombMoserBoundCoefficient 2 (3/2 : ℝ) (variationalGroundEnergy 2 (3/2 : ℝ)).toReal * ‖(g : FermionicSpace 2).val‖) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ 1/4 →
          ∀ (σ : SpinConfiguration 2) (i : Fin 2) (t0 : Position), ‖t0‖ = 1 →
            PhysicalKSBoxAnalyticDescentDerivativeData
              ((originScaledDifference (u σ) ε ∘ nuclearKSLift i) ∘
                (physicalSpectatorReindexAt i).symm)
              (fun X T => originScaledDifference (u σ) ε (nuclearKSPhysicalCoordinates i X T))
              t0 M A Csrc CH12) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ 1/4 →
          ∀ (σ : SpinConfiguration 2) (t0 : Position), ‖t0‖ = 1 →
            PhysicalKSBoxAnalyticDescentDerivativeData
              ((originScaledDifference (u σ) ε ∘ TheoremT.Continuum.pairKSLift) ∘
                (physicalSpectatorReindexAt (0 : Fin 2)).symm)
              (fun X T => originScaledDifference (u σ) ε (pairKSPhysicalCoordinates X T))
              t0 M A Csrc CH12) := by
  exact exactProduct_physical_ground_original_norm_analytic_derivative (3/2)
    (by norm_num) (by norm_num) (by norm_num)

#print axioms exactProduct_physical_ground_original_norm_analytic_derivative
#print axioms exactProduct_physical_ground_original_norm_analytic_derivative_above_threshold
#print axioms exactProduct_three_halves_physical_original_norm_analytic_derivative
end ManyBody.S8

