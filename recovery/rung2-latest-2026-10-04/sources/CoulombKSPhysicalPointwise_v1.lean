import PhysicalKSBoxPointwiseFactorial_v1

/-! Actual scalar Coulomb eigenfunctions yield smooth analytic normalized
KS pullbacks and uniform factorial coordinate estimates in all three charts.
The constants precede the physical eigenfunction, the Lipschitz data, center,
scale, and derivative word. This is still a local lifted theorem. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Metric
open scoped ContDiff NNReal BigOperators
namespace TheoremT.Continuum
open WeakGrushin

def PhysicalKSBoxPointwiseData (f : Space (Fin 3) → ℂ) (t0 : Position)
    (M A F0 W : ℝ) : Prop :=
  ContDiffOn ℝ ∞ f (rectangularOpenBox (0,t0) (1/512) (1/512)) ∧
    AnalyticOnNhd ℝ f (rectangularOpenBox (0,t0) (1/512) (1/512)) ∧
    ∀ w p, p ∈ rectangularOpenBox (0,t0) (1/512) (1/512) →
      ‖complexDirectionalWordDeriv productCoordinateDirection f w p‖ ≤
        physicalKSPointwiseAmplitude M A F0 W *
          (physicalKSPointwiseRate M A)^w.length * (w.length.factorial : ℝ)

theorem physicalKSBoxFactorialData_to_pointwise
    {f : Space (Fin 3) → ℂ} {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxFactorialData f t0 M A F0 W)
    (hcont : ContinuousOn f (rectangularOpenBox (0,t0) (1/512) (1/512)))
    (hA : 1 ≤ A) (hF0 : 0 ≤ F0) :
    PhysicalKSBoxPointwiseData f t0 M A F0 W := by
  obtain ⟨hs,hb⟩ := physicalKSBoxFactorialData_smooth_pointwise hdata hcont hA hF0
  exact ⟨hs,physicalKSBoxFactorialData_analytic hdata hcont hA hF0,hb⟩

theorem scalar_coulomb_all_physical_box_pointwise (Z E : ℝ) :
    ∃ C_H M A : ℝ, 1 ≤ C_H ∧ 1 ≤ M ∧ 1 ≤ A ∧
      ∀ f : SpatialL2 2, scalarHamiltonianGraph 2 Z f ((E : ℂ) • f) →
      ∀ g : Configuration 2 → ℂ, Continuous g → (f : Configuration 2 → ℂ) =ᵐ[volume] g →
      ∀ (L : ℝ≥0) (R eps : ℝ), LipschitzOnWith L g (ball 0 R) →
        0 < eps → eps ≤ min 1 (R/4) →
        (∀ (i : Fin 2) (t0 : Position), ‖t0‖ = 1 →
          PhysicalKSBoxPointwiseData
            ((originScaledDifference g eps ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
            t0 M A (M*‖g 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L : ℝ)^2+‖g 0‖^2)*C_H)) ∧
        (∀ t0 : Position, ‖t0‖ = 1 →
          PhysicalKSBoxPointwiseData
            ((originScaledDifference g eps ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm)
            t0 M A (M*‖g 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L : ℝ)^2+‖g 0‖^2)*C_H)) := by
  obtain ⟨C_H,M,A,hCH,hM,hA,hdata⟩ := scalar_coulomb_all_physical_box_factorial Z E
  refine ⟨C_H,M,A,hCH,hM,hA,?_⟩
  intro f hgraph g hg hfg L R eps hLip heps hlim
  obtain ⟨hN,hP⟩ := hdata f hgraph g hg hfg L R eps hLip heps hlim
  have hF0 : 0 ≤ M*‖g 0‖*Real.sqrt physicalKSUniformSourceVolume := by positivity
  refine ⟨?_,?_⟩
  · intro i t0 ht0
    have hc : Continuous
        ((originScaledDifference g eps ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) :=
      ((originScaledDifference_continuous hg eps).comp (nuclearKSLift_contDiff i).continuous).comp
        (physicalSpectatorReindexAt i).symm.continuous
    exact physicalKSBoxFactorialData_to_pointwise (hN i t0 ht0) hc.continuousOn hA hF0
  · intro t0 ht0
    have hc : Continuous
        ((originScaledDifference g eps ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) :=
      ((originScaledDifference_continuous hg eps).comp pairKSLift_contDiff.continuous).comp
        (physicalSpectatorReindexAt (0 : Fin 2)).symm.continuous
    exact physicalKSBoxFactorialData_to_pointwise (hP t0 ht0) hc.continuousOn hA hF0

end TheoremT.Continuum
