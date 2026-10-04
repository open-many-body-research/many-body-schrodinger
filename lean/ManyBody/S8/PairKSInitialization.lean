import ManyBody.S8.Internal.PairKSCutoffGain
import ManyBody.S8.Internal.JointWeakH2Initialization

/-! Genuine joint local weak H2 in the electron-pair KS chart of the original
physical two-electron eigenfunction. The chart reconstructs original positions
through the orthogonal Hadamard map and covers every isolated pair collision
away from both nuclei. Its actual weak equation, smooth coefficient patch,
and Y/T/YY gains are proved before the generic joint-H2 initialization.
This gives qualitative collision-chart H2 initialization, not full Rung 2,
higher-order factorial estimates, or control of simultaneous collisions. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace ManyBody.S8
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin

/-- Every compact cutoff in the actual pair coefficient patch has all ordered
first and second genuine weak L2 derivatives, including mixed directions. -/
theorem scalar_coulomb_pair_KS_local_weakH2 (Z E : ℝ)
    {f : SpatialL2 2} (hgraph : scalarHamiltonianGraph 2 Z f ((E : ℂ) • f))
    {g : Configuration 2 → ℂ} (hg : Continuous g)
    (hfg : (f : Configuration 2 → ℂ) =ᵐ[volume] g) :
    ProductLocalWeakH2On (g ∘ pairKSLift) pairKSCoefficientPatch := by
  intro χ hχ hcχ hχpatch
  obtain ⟨χouter,houter,hcouter,hsouter,V,hV,hχV,hVpatch,houter1⟩ :=
    exists_outer_plateau hcχ pairKSCoefficientPatch_isOpen hχpatch
  obtain ⟨K,C,hK,houterK,hKpatch,hC,hinit⟩ :=
    scalar_coulomb_pair_KS_one_step Z E houter hcouter hsouter
  obtain ⟨U,gy,gt,hyy,hU,_,_,_,hgy,hgt,hhyy⟩ := hinit hgraph hg hfg
  have hBasis : (spectatorBasis : SpectatorCoordinate (1 : Fin 2) →
      SpectatorConfiguration (1 : Fin 2)) = oscillatorBasis := by
    funext j
    simp only [spectatorBasis,oscillatorBasis,EuclideanSpace.single,PiLp.single]
  have hPraw : ∀ φ : PairKSSpace → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ pairKSCoefficientPatch →
      (∫ p, splitGrushin 4 oscillatorBasis (pairKSPotential Z E) φ p •
        (g ∘ pairKSLift) p)=0 := by
    intro φ hφ hcφ hsφ
    have hh := (scalar_coulomb_pair_KS_weak hgraph hg hfg hφ hcφ hsφ).2
    rw [hBasis] at hh
    simpa only [Complex.real_smul] using hh
  have hP := weak_potential_output_on_plateau 4 (pairKSPotential Z E) hU
    hVpatch houter1 hPraw
  have hB : ContDiffOn ℝ ∞ (pairKSPotential Z E) V := by
    intro p hp
    exact (pairKSPotential_contDiffAt Z E (hVpatch hp)).contDiffWithinAt
  obtain ⟨W,a,b,hW,ha,hb⟩ := local_homogeneous_grushin_joint_cutoff_h2
    (by norm_num : (0 : ℝ) < 4) hV hB hχ hcχ hχV hgy hgt hhyy hP
  refine ⟨W,a,?_,ha,fun v w => ⟨b v w,hb v w⟩⟩
  filter_upwards [hW,hU] with p hp hu
  rw [hp]
  by_cases ht : p ∈ tsupport χ
  · rw [hu,houter1 p (hχV ht),one_smul]
    rfl
  · simp only [image_eq_zero_of_notMem_tsupport ht,zero_smul]

/-- One actual physical spin representative works for every spin component
and every compact cutoff of the isolated-pair chart, including its collision. -/
theorem coulomb_spin_pair_KS_local_weakH2 {Z E : ℝ} {ψ : SpinSpace 2}
    (hgraph : hamiltonianGraph 2 Z ψ ((E : ℂ) • ψ)) :
    ∃ u : SpinConfiguration 2 → Configuration 2 → ℂ,
      (∀ σ, LocallyLipschitz (u σ)) ∧
      (∀ᵐ x ∂volume, ∀ σ, ψ σ x = u σ x) ∧
      (∀ π : Equiv.Perm (Fin 2), ∀ σ, ∀ x,
        u (permuteSpin π σ) (permuteSpace π x) = permutationSign π • u σ x) ∧
      (∀ x, Real.sqrt (∑ σ : SpinConfiguration 2, ‖u σ x‖^2) ≤
        coulombMoserBoundCoefficient 2 Z E * ‖ψ‖) ∧
      ∀ σ : SpinConfiguration 2, LocallyLipschitz (u σ ∘ pairKSLift) ∧
        ProductLocalWeakH2On (u σ ∘ pairKSLift) pairKSCoefficientPatch := by
  obtain ⟨u,hu,hue,hperm,hbound⟩ :=
    coulomb_spin_locally_lipschitz_representative (by norm_num : 0 < 2) hgraph
  refine ⟨u,hu,hue,hperm,hbound,?_⟩
  intro σ
  have he : (ψ σ : Configuration 2 → ℂ) =ᵐ[volume] u σ := by
    filter_upwards [hue] with x hx
    exact hx σ
  exact ⟨(hu σ).comp pairKSLift_locallyLipschitz,
    scalar_coulomb_pair_KS_local_weakH2 Z E (hgraph.2.2 σ) (hu σ).continuous he⟩

#print axioms scalar_coulomb_pair_KS_local_weakH2
#print axioms coulomb_spin_pair_KS_local_weakH2
end ManyBody.S8