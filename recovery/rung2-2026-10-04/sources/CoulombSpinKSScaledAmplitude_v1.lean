import KSScaledDifferenceAmplitude_v1
import CoulombSpinLocallyLipschitz_v1

/-! The scaled KS amplitude input for one actual two-electron fermionic
representative, with one radius and Lipschitz bound chosen before spin, scale
and chart. The Lipschitz constant is finite but is not numerically evaluated. -/
noncomputable section
open MeasureTheory Filter Metric
open scoped Topology NNReal BigOperators
namespace TheoremT.Continuum

theorem finite_family_locallyLipschitz_origin_ball
    {E : Type*} [NormedAddCommGroup E] {S : Type*} [Fintype S]
    {g : S → E → ℂ} (hg : ∀ s, LocallyLipschitz (g s)) :
    ∃ L : ℝ≥0, ∃ R : ℝ, 0 < R ∧ ∀ s, LipschitzOnWith L (g s) (ball 0 R) := by
  classical
  choose L U hU hLip using (fun s => hg s 0)
  have hInter : (⋂ s, U s) ∈ 𝓝 (0 : E) := Filter.iInter_mem.mpr hU
  obtain ⟨R,hR,hRI⟩ := Metric.mem_nhds_iff.mp hInter
  refine ⟨∑ s, L s,R,hR,?_⟩
  intro s
  have hL : L s ≤ ∑ t, L t := Finset.single_le_sum (fun t ht => (by positivity : 0 ≤ L t))
    (Finset.mem_univ s)
  apply (hLip s).weaken hL |>.mono
  intro x hx
  exact Set.mem_iInter.mp (hRI hx) s

theorem coulomb_spin_KS_scaled_amplitude_representative
    {Z E : ℝ} {ψ : SpinSpace 2} (hgraph : hamiltonianGraph 2 Z ψ ((E : ℂ) • ψ)) :
    ∃ u : SpinConfiguration 2 → Configuration 2 → ℂ,
    ∃ L : ℝ≥0, ∃ R : ℝ,
      0 < R ∧
      (∀ σ, LocallyLipschitz (u σ)) ∧
      (∀ σ, LipschitzOnWith L (u σ) (ball 0 R)) ∧
      (∀ᵐ x ∂volume, ∀ σ, ψ σ x = u σ x) ∧
      (∀ π : Equiv.Perm (Fin 2), ∀ σ, ∀ x,
        u (permuteSpin π σ) (permuteSpace π x) = permutationSign π • u σ x) ∧
      (∀ x, Real.sqrt (∑ σ : SpinConfiguration 2, ‖u σ x‖^2) ≤
        coulombMoserBoundCoefficient 2 Z E * ‖ψ‖) ∧
      (∀ ε : ℝ, 0 < ε → ε ≤ R / 4 → ∀ (σ : SpinConfiguration 2)
        (i : Fin 2) (q : NuclearKSSpace i),
        ‖q.1‖ ≤ (1/4 : ℝ) → ‖q.2‖ ≤ (5/4 : ℝ) →
        ‖originScaledDifference (u σ) ε (nuclearKSLift i q)‖ ≤ 2 * (L : ℝ)) ∧
      (∀ ε : ℝ, 0 < ε → ε ≤ R / 4 → ∀ (σ : SpinConfiguration 2) (q : PairKSSpace),
        ‖q.1‖ ≤ (1/4 : ℝ) → ‖q.2‖ ≤ (5/4 : ℝ) →
        ‖originScaledDifference (u σ) ε (pairKSLift q)‖ ≤ 2 * (L : ℝ)) := by
  obtain ⟨u,hu,hue,hperm,hbound⟩ :=
    coulomb_spin_locally_lipschitz_representative (by norm_num : 0 < 2) hgraph
  obtain ⟨L,R,hR,hLR⟩ := finite_family_locallyLipschitz_origin_ball hu
  refine ⟨u,L,R,hR,hu,hLR,hue,hperm,hbound,?_,?_⟩
  · intro ε hε hεR σ i q hy ht
    exact nuclearKS_scaled_difference_amplitude i hR (hLR σ) hε hεR q hy ht
  · intro ε hε hεR σ q hy ht
    exact pairKS_scaled_difference_amplitude hR (hLR σ) hε hεR q hy ht

#print axioms finite_family_locallyLipschitz_origin_ball
#print axioms coulomb_spin_KS_scaled_amplitude_representative
end TheoremT.Continuum
