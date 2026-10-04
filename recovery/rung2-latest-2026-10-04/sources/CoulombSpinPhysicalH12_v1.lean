import CoulombKSPhysicalH12Common_v1
import CoulombSpinKSScaledAmplitude_v1

/-! A single genuine full-spin representative with H12 initialization in
both nuclear charts and the pair chart. No input representative, Lipschitz
bound or scalar jet is supplied: they follow from the actual spin graph.
The finite common coefficient constant precedes the spin vector. -/
noncomputable section
open MeasureTheory Metric
open scoped ContDiff NNReal BigOperators
namespace TheoremT.Continuum
open WeakGrushin

def spinOriginH12Budget (C : ℝ) (L : ℝ≥0)
    (u : SpinConfiguration 2 → Configuration 2 → ℂ) : ℝ :=
  ((L : ℝ)^2 + ∑ σ, ‖u σ 0‖^2)*C

theorem coulomb_spin_physical_h12_representative (Z E : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ψ : SpinSpace 2,
      hamiltonianGraph 2 Z ψ ((E : ℂ) • ψ) →
      ∃ u : SpinConfiguration 2 → Configuration 2 → ℂ,
      ∃ L : ℝ≥0, ∃ R : ℝ,
        0 < R ∧ 0 ≤ spinOriginH12Budget C L u ∧
        (∀ σ, LocallyLipschitz (u σ)) ∧
        (∀ σ, LipschitzOnWith L (u σ) (ball 0 R)) ∧
        (∀ᵐ x ∂volume, ∀ σ, ψ σ x = u σ x) ∧
        (∀ π : Equiv.Perm (Fin 2), ∀ σ, ∀ x,
          u (permuteSpin π σ) (permuteSpace π x) = permutationSign π • u σ x) ∧
        (∀ x, Real.sqrt (∑ σ : SpinConfiguration 2, ‖u σ x‖^2) ≤
          coulombMoserBoundCoefficient 2 Z E * ‖ψ‖) ∧
        (∀ (i : Fin 2) (t0 : SpectatorConfiguration i), ‖t0‖ = 1 →
          ∀ ε : ℝ, 0 < ε → ε ≤ min 1 (R/4) →
          SpinPhysicalH12Reserve i
            (physicalSpectatorReindexAt i ⁻¹' rectangularOpenBox
              (0,twoElectronSpectatorPositionEquiv i t0) (1/128) (1/128))
            (fun σ => originScaledDifference (u σ) ε ∘ nuclearKSLift i)
            (spinOriginH12Budget C L u)) ∧
        (∀ t0 : SpectatorConfiguration (0 : Fin 2), ‖t0‖ = 1 →
          ∀ ε : ℝ, 0 < ε → ε ≤ min 1 (R/4) →
          SpinPhysicalH12Reserve (0 : Fin 2)
            (physicalSpectatorReindex ⁻¹' rectangularOpenBox
              (0,pairCenterEquiv t0) (1/128) (1/128))
            (fun σ => originScaledDifference (u σ) ε ∘ pairKSLift)
            (spinOriginH12Budget C L u)) := by
  classical
  obtain ⟨C,hC,hN,hP⟩ := scalar_coulomb_all_physical_coordinate_h12_common Z E
  refine ⟨C,hC,?_⟩
  intro ψ hgraph
  obtain ⟨u,L,R,hR,hu,hLip,hAE,hperm,hbound,_hNamp,_hPamp⟩ :=
    coulomb_spin_KS_scaled_amplitude_representative hgraph
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hW : 0 ≤ spinOriginH12Budget C L u := by
    unfold spinOriginH12Budget
    positivity
  have hAmp (σ : SpinConfiguration 2) :
      ((L : ℝ)^2+‖u σ 0‖^2)*C ≤ spinOriginH12Budget C L u := by
    have hi : ‖u σ 0‖^2 ≤ ∑ τ, ‖u τ 0‖^2 :=
      Finset.single_le_sum (fun τ _ => sq_nonneg ‖u τ 0‖) (Finset.mem_univ σ)
    exact mul_le_mul_of_nonneg_right (add_le_add le_rfl hi) hC0
  have hσAE (σ : SpinConfiguration 2) :
      (ψ σ : Configuration 2 → ℂ) =ᵐ[volume] u σ := by
    filter_upwards [hAE] with x hx
    exact hx σ
  have hσgraph (σ : SpinConfiguration 2) :
      scalarHamiltonianGraph 2 Z (ψ σ) ((E : ℂ) • ψ σ) := hgraph.2.2 σ
  refine ⟨u,L,R,hR,hW,hu,hLip,hAE,hperm,hbound,?_,?_⟩
  · intro i t0 ht0 ε hε hlim
    apply spinPhysicalH12Reserve_of_coordinate i
    intro σ
    exact (hN i t0 ht0 (ψ σ) (hσgraph σ) (u σ) (hu σ).continuous
      (hσAE σ) L R ε (hLip σ) hε hlim).mono_budget (hAmp σ)
  · intro t0 ht0 ε hε hlim
    apply spinPhysicalH12Reserve_of_coordinate (0 : Fin 2)
    intro σ
    exact (hP t0 ht0 (ψ σ) (hσgraph σ) (u σ) (hu σ).continuous
      (hσAE σ) L R ε (hLip σ) hε hlim).mono_budget (hAmp σ)

end TheoremT.Continuum
