import ManyBody.S8.Internal.PairKSEquation
import LocalWeakGrushinPotentialGain_v1
import ProductContinuousLocalL2_v1

/-! Genuine first Y/T and second YY weak L2 gains for the original physical pair KS pullback, obtained from its proved weak equation and exact smooth coefficient patch. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

theorem scalar_coulomb_pair_KS_one_step (Z E : ℝ)
    {χ : PairKSSpace → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ pairKSCoefficientPatch) :
    ∃ K : Set (PairKSSpace), ∃ C : ℝ,
      IsCompact K ∧ tsupport χ ⊆ K ∧ K ⊆ pairKSCoefficientPatch ∧ 0 ≤ C ∧
      ∀ {f : SpatialL2 2}, scalarHamiltonianGraph 2 Z f ((E : ℂ) • f) →
      ∀ {g : Configuration 2 → ℂ}, Continuous g → ((f : Configuration 2 → ℂ) =ᵐ[volume] g) →
        let F : ℝ := ∫ p in K, ‖g (pairKSLift p)‖^2
        let M : ℝ := ∫ p in K, ‖pairKSPotential Z E p • g (pairKSLift p)‖^2
        ∃ U : Lp ℂ 2 (volume : Measure (PairKSSpace)),
        ∃ gy : Fin 4 → Lp ℂ 2 (volume : Measure (PairKSSpace)),
        ∃ gt : SpectatorCoordinate (1 : Fin 2) → Lp ℂ 2 (volume : Measure (PairKSSpace)),
        ∃ hyy : Fin 4 → Fin 4 → Lp ℂ 2 (volume : Measure (PairKSSpace)),
          U =ᵐ[volume] (fun p => χ p • g (pairKSLift p)) ∧
          (∑ j, ‖gy j‖^2) ≤ 2*(C*F)+(3/4 : ℝ)*(C*(F+M)) ∧
          (∑ j, ‖gt j‖^2) ≤ (C*(F+M))/64 ∧
          (∑ j, ∑ k, ‖hyy j k‖^2) ≤ (3/2 : ℝ)*(C*(F+M)) ∧
          (∀ j, WeakProductL2Directional U (gy j) (WeakGrushin.yDir j)) ∧
          (∀ j, WeakProductL2Directional U (gt j) (WeakGrushin.tDir j)) ∧
          ∀ j k, WeakProductL2Directional (gy j) (hyy j k) (WeakGrushin.yDir k) := by
  obtain ⟨K,C,hK,hχK,hKΩ,hC,hgain⟩ :=
    WeakGrushin.local_weak_grushin_potential_cutoff_gain (κ := SpectatorCoordinate (1 : Fin 2))
      (by norm_num : (0 : ℝ) < 4) (pairKSCoefficientPatch_isOpen) hχ hcχ hχΩ
  refine ⟨K,C,hK,hχK,hKΩ,hC,?_⟩
  intro f hgraph g hg hfg
  have hcont : Continuous (g ∘ pairKSLift) := hg.comp (pairKSLift_contDiff).continuous
  have hlocal : ProductLocallyL2On (g ∘ pairKSLift) (pairKSCoefficientPatch) :=
    product_continuousOn_locallyL2 hcont.continuousOn
  have hzero : ProductLocallyL2On (fun _ : PairKSSpace => (0 : ℂ)) (pairKSCoefficientPatch) :=
    product_continuousOn_locallyL2 continuous_const.continuousOn
  have hB : ContinuousOn (pairKSPotential Z E) (pairKSCoefficientPatch) := by
    intro q hq
    exact (pairKSPotential_contDiffAt Z E hq).continuousAt.continuousWithinAt
  have hBasis : (spectatorBasis : SpectatorCoordinate (1 : Fin 2) → SpectatorConfiguration (1 : Fin 2)) = oscillatorBasis := by
    funext j
    simp only [spectatorBasis,oscillatorBasis,EuclideanSpace.single,PiLp.single]
  have hP : ∀ φ : PairKSSpace → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ pairKSCoefficientPatch →
      (∫ p, splitGrushin 4 oscillatorBasis (pairKSPotential Z E) φ p •
        (g ∘ pairKSLift) p) = ∫ p, φ p • (0 : ℂ) := by
    intro φ hφ hcφ hsφ
    have hh := (scalar_coulomb_pair_KS_weak hgraph hg hfg hφ hcφ hsφ).2
    rw [hBasis] at hh
    simpa only [Complex.real_smul,smul_zero,integral_zero] using hh
  have hh := hgain (pairKSPotential Z E) (g ∘ pairKSLift) (fun _ => 0)
    hB hlocal hzero hP
  simpa only [Function.comp_apply,zero_sub,norm_neg,show (16 : ℝ)*4=64 by norm_num] using hh

#print axioms scalar_coulomb_pair_KS_one_step
end ManyBody.S8
