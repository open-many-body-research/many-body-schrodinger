import KSCommonPhysicalFactorialBudgets_v1
import CoulombKSPhysicalBoxEquation_v1
import PhysicalSpectatorWeakHkTransport_v1
import CoulombKSPhysicalH12Common_v1
import LocalWeakGrushinCommonKSBoxFactorial_v1

/-! Uniform factorial bounds for the actual normalized scalar Coulomb KS
pullbacks in both nuclear charts and the pair chart. The shared constants
are chosen before the physical solution, Lipschitz data, center and scale.
The output is a single coherent family of genuine weak derivatives and its
actual weighted local L2 profile. It is not yet a pointwise or descent theorem. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Metric
open scoped ContDiff NNReal BigOperators
namespace TheoremT.Continuum
open WeakGrushin

def PhysicalKSBoxFactorialData (f : Space (Fin 3) → ℂ) (t0 : Position)
    (M A F0 W : ℝ) : Prop :=
  ∃ F : FactorialRawJetFamily, F 0 0 = f ∧
    (∀ m : ℕ, ∃ V : ℝ, 0 ≤ V ∧ ∀ α β,
      (∑ i,α i)+(∑ j,β j) ≤ m →
        RegionL2Budget (F α β) (rectangularOpenBox (0,t0) (1/128) (1/128)) V) ∧
    (∀ α β i, ProductLocalWeakDirectional (rectangularOpenBox (0,t0) (1/128) (1/128))
      (F α β) (F (α+Pi.single i 1) β) (yDir i)) ∧
    (∀ α β j, ProductLocalWeakDirectional (rectangularOpenBox (0,t0) (1/128) (1/128))
      (F α β) (F α (β+Pi.single j 1)) (tDir j)) ∧
    ∀ r : ℕ,
      FactorialLocalMemLp F (rectangularOpenBox (0,t0) (1/256) (1/256)) r ∧
      let C := commonKSBoxFactorialConstant M
      factorialLocalProfile F (rectangularOpenBox (0,t0) (1/256) (1/256)) r ≤
        12*C*A*(F0+498*Real.sqrt W)*(3072*C*A)^r*(r.factorial : ℝ)

theorem scalar_coulomb_all_physical_box_factorial (Z E : ℝ) :
    ∃ C_H M A : ℝ, 1 ≤ C_H ∧ 1 ≤ M ∧ 1 ≤ A ∧
      ∀ f : SpatialL2 2, scalarHamiltonianGraph 2 Z f ((E : ℂ) • f) →
      ∀ g : Configuration 2 → ℂ, Continuous g → (f : Configuration 2 → ℂ) =ᵐ[volume] g →
      ∀ (L : ℝ≥0) (R eps : ℝ), LipschitzOnWith L g (ball 0 R) →
        0 < eps → eps ≤ min 1 (R/4) →
        (∀ (i : Fin 2) (t0 : Position), ‖t0‖ = 1 →
          PhysicalKSBoxFactorialData
            ((originScaledDifference g eps ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
            t0 M A (M*‖g 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L : ℝ)^2+‖g 0‖^2)*C_H)) ∧
        (∀ t0 : Position, ‖t0‖ = 1 →
          PhysicalKSBoxFactorialData
            ((originScaledDifference g eps ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm)
            t0 M A (M*‖g 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L : ℝ)^2+‖g 0‖^2)*C_H)) := by
  obtain ⟨C_H,hCH,hHN,hHP⟩ := scalar_coulomb_all_physical_coordinate_h12_common Z E
  obtain ⟨M,A,hM,hA,hBN,hBP⟩ := ksCommon_physical_factorial_budgets Z E
  refine ⟨C_H,M,A,hCH,hM,hA,?_⟩
  intro f hgraph g hg hfg L R eps hLip heps hlim
  have heps1 : eps ≤ 1 := hlim.trans (min_le_left _ _)
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  refine ⟨?_,?_⟩
  · intro i t0 ht0
    obtain ⟨hB,hs,hf,hEq⟩ := scalar_coulomb_nuclear_physical_box_equation i heps t0 ht0 hgraph hg hfg
    obtain ⟨hBb,hSB⟩ := hBN i t0 ht0 eps heps.le heps1 (g 0)
    have htphys : ‖(twoElectronSpectatorPositionEquiv i).symm t0‖ = 1 := by
      rw [(twoElectronSpectatorPositionEquiv i).symm.norm_map,ht0]
    have h12raw := hHN i ((twoElectronSpectatorPositionEquiv i).symm t0) htphys
      f hgraph g hg hfg L R eps hLip heps hlim
    rw [LinearIsometryEquiv.apply_symm_apply] at h12raw
    have h12 := physicalSpectatorReindexAt_mixedH12 i (rectangularOpenBox_isOpen (0,t0) _ _) h12raw
    exact local_weak_grushin_common_KS_box_factorial t0 4 (Or.inr rfl)
      hB hs hf (fun φ hφ hc ht => (hEq φ hφ hc ht).2.2)
      M A (M*‖g 0‖*Real.sqrt physicalKSUniformSourceVolume) hM0 hA (by positivity)
      hBb hSB (((L : ℝ)^2+‖g 0‖^2)*C_H) h12
  · intro t0 ht0
    obtain ⟨hB,hs,hf,hEq⟩ := scalar_coulomb_pair_physical_box_equation heps t0 ht0 hgraph hg hfg
    obtain ⟨hBb,hSB⟩ := hBP t0 ht0 eps heps.le heps1 (g 0)
    have htphys : ‖pairCenterEquiv.symm t0‖ = 1 := by
      rw [pairCenterEquiv.symm.norm_map,ht0]
    have h12raw := hHP (pairCenterEquiv.symm t0) htphys
      f hgraph g hg hfg L R eps hLip heps hlim
    rw [LinearIsometryEquiv.apply_symm_apply] at h12raw
    have h12 := physicalSpectatorReindexAt_mixedH12 (0 : Fin 2)
      (rectangularOpenBox_isOpen (0,t0) _ _) h12raw
    exact local_weak_grushin_common_KS_box_factorial t0 1 (Or.inl rfl)
      hB hs hf (fun φ hφ hc ht => (hEq φ hφ hc ht).2.2)
      M A (M*‖g 0‖*Real.sqrt physicalKSUniformSourceVolume) hM0 hA (by positivity)
      hBb hSB (((L : ℝ)^2+‖g 0‖^2)*C_H) h12

end TheoremT.Continuum
