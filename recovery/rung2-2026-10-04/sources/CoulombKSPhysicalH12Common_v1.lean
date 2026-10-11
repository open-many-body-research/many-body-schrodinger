import CoulombKSPhysicalH12All_v1
import CoulombKSPhysicalH12_v1
import SmoothTransitionExplicitBounds_v1
import PhysicalSpinCoordinateH12Reserve_v1

/-! One finite coefficient bound for both nuclear charts and the pair chart,
chosen before every solution, center, spin component and scale. It is the
finite sum of the previous explicit recurrence budgets plus one. -/
noncomputable section
open MeasureTheory Metric
open scoped ContDiff NNReal BigOperators
namespace TheoremT.Continuum
open WeakGrushin

theorem scalar_coulomb_all_physical_coordinate_h12_common (Z E : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧
    (∀ (i : Fin 2) (t0 : SpectatorConfiguration i), ‖t0‖ = 1 →
      ∀ f : SpatialL2 2, scalarHamiltonianGraph 2 Z f ((E : ℂ) • f) →
      ∀ g : Configuration 2 → ℂ, Continuous g → (f : Configuration 2 → ℂ) =ᵐ[volume] g →
      ∀ (L : ℝ≥0) (R ε : ℝ), LipschitzOnWith L g (ball 0 R) →
        0 < ε → ε ≤ min 1 (R/4) →
        ProductCoordinateWeakHk
          (physicalSpectatorReindexAt i ⁻¹' rectangularOpenBox
            (0,twoElectronSpectatorPositionEquiv i t0) (1/128) (1/128))
          (originScaledDifference g ε ∘ nuclearKSLift i) 12
          (((L : ℝ)^2+‖g 0‖^2)*C)) ∧
    (∀ t0 : SpectatorConfiguration (0 : Fin 2), ‖t0‖ = 1 →
      ∀ f : SpatialL2 2, scalarHamiltonianGraph 2 Z f ((E : ℂ) • f) →
      ∀ g : Configuration 2 → ℂ, Continuous g → (f : Configuration 2 → ℂ) =ᵐ[volume] g →
      ∀ (L : ℝ≥0) (R ε : ℝ), LipschitzOnWith L g (ball 0 R) →
        0 < ε → ε ≤ min 1 (R/4) →
        ProductCoordinateWeakHk
          (physicalSpectatorReindex ⁻¹' rectangularOpenBox
            (0,pairCenterEquiv t0) (1/128) (1/128))
          (originScaledDifference g ε ∘ pairKSLift) 12
          (((L : ℝ)^2+‖g 0‖^2)*C)) := by
  classical
  choose KT KY QY hKT hKY hQY hN0 hN using
    (fun i : Fin 2 => scalar_coulomb_nuclear_physical_coordinate_h12 i Z E 96 14016
      smoothTransition_deriv_abs_le_ninety_six
      smoothTransition_second_deriv_abs_le_fourteen_thousand_sixteen)
  obtain ⟨PT,PY,PQ,hPT,hPY,hPQ,hP0,hP⟩ :=
    scalar_coulomb_pair_physical_coordinate_h12 Z E 96 14016
      smoothTransition_deriv_abs_le_ninety_six
      smoothTransition_second_deriv_abs_le_fourteen_thousand_sixteen
  let Bn := fun i => ksH12MixedBudgetAt i 4 96 14016 (KT i) (KY i) (QY i)
  let Bp := ksH12MixedBudget 1 96 14016 PT PY PQ
  let C := 1 + (∑ i, Bn i) + Bp
  have hsum : 0 ≤ ∑ i, Bn i := Finset.sum_nonneg (fun i _ => hN0 i)
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hnC (i : Fin 2) : Bn i ≤ C := by
    have hi : Bn i ≤ ∑ j, Bn j :=
      Finset.single_le_sum (fun j _ => hN0 j) (Finset.mem_univ i)
    dsimp [C]
    linarith
  have hpC : Bp ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC,?_,?_⟩
  · intro i t0 ht0 f hgraph g hg hfg L R ε hLip hε hlim
    exact (hN i t0 ht0 f hgraph g hg hfg L R ε hLip hε hlim).mono_budget
      (mul_le_mul_of_nonneg_left (hnC i) (by positivity))
  · intro t0 ht0 f hgraph g hg hfg L R ε hLip hε hlim
    exact (hP t0 ht0 f hgraph g hg hfg L R ε hLip hε hlim).mono_budget
      (mul_le_mul_of_nonneg_left hpC (by positivity))

end TheoremT.Continuum
