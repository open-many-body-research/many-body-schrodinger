import KSScaledFiniteSpectatorReserve_v1
import KSScaledDifferenceAmplitude_v1
import CoulombEpsilonKSDifference_v1

/-! Actual physical normalized differences supply the raw L2 input and the
inhomogeneous weak PDE for every finite spectator iteration. The coefficient
constant is chosen before the physical representative, scale and cutoffs.
The compact chart and the actual step geometry remain explicit inputs. -/
noncomputable section
open MeasureTheory Metric
open scoped ContDiff NNReal
namespace TheoremT.Continuum
open WeakGrushin

theorem scalar_coulomb_nuclear_scaled_finite_reserve {N : ℕ} (i : Fin N)
    (Z E : ℝ) {K : Set (NuclearKSSpace i)} (hK : IsCompact K)
    (hKpatch : K ⊆ nuclearKSCoefficientPatch i)
    (hbox : ∀ q ∈ K, ‖q.1‖ ≤ (1/4 : ℝ) ∧ ‖q.2‖ ≤ (5/4 : ℝ)) (n : ℕ) :
    ∃ K0 : ℝ, 1 ≤ K0 ∧
      ∀ (Ω W : ℕ → Set (NuclearKSSpace i)) (χ η : ℕ → NuclearKSSpace i → ℝ)
        (M A B D Q : ℕ → ℝ),
        (∀ k, k < n → SpectatorStepGeometry 4 (Ω k) (Ω (k+1)) (W k)
          (χ k) (η k) (M k) (A k) (B k) (D k) (Q k)) →
        MeasurableSet (Ω 0) → Ω 0 ⊆ K →
        ∀ (f : SpatialL2 N), scalarHamiltonianGraph N Z f ((E : ℂ) • f) →
        ∀ (g : Configuration N → ℂ), Continuous g →
          (f : Configuration N → ℂ) =ᵐ[volume] g →
        ∀ (L : ℝ≥0) (R ε : ℝ), 0 < R → LipschitzOnWith L g (ball 0 R) →
          0 < ε → ε ≤ 1 → ε ≤ R/4 →
          0 ≤ spectatorIterationBudgetSeq 4 M A B D Q K0
            (K0^2*‖g 0‖^2*(volume (Ω 0)).toReal)
            ((2*(L : ℝ))^2*(volume K).toReal) n ∧
          SpectatorFiniteState (Ω n) (originScaledDifference g ε ∘ nuclearKSLift i) n
            (spectatorIterationBudgetSeq 4 M A B D Q K0
              (K0^2*‖g 0‖^2*(volume (Ω 0)).toReal)
              ((2*(L : ℝ))^2*(volume K).toReal) n) := by
  obtain ⟨K0,hK0,hgain⟩ := nuclearKS_scaled_finite_spectator_reserve i Z E hK hKpatch n
  refine ⟨K0,hK0,?_⟩
  intro Ω W χ η M A B D Q hGeom hΩmeas hΩK f hgraph g hg hfg L R ε hR hLip hε hε1 hεR
  have hraw : RegionL2Budget (originScaledDifference g ε ∘ nuclearKSLift i) K
      ((2*(L : ℝ))^2*(volume K).toReal) :=
    nuclearKS_scaled_difference_compact_L2 i hg hR hLip hε hεR hK hbox
  apply hgain Ω W χ η M A B D Q hGeom hΩmeas hΩK ε hε.le hε1
    (g 0) (originScaledDifference g ε ∘ nuclearKSLift i)
    ((2*(L : ℝ))^2*(volume K).toReal) (by positivity)
    (hraw.restrict hΩK le_rfl)
  intro φ hφ hc hs
  have he := (scalar_coulomb_epsilon_nuclear_KS_difference_weak i hε hgraph hg hfg
    hφ hc (hs.trans (hΩK.trans hKpatch))).2.2
  have hBasis : (spectatorBasis : SpectatorCoordinate i → SpectatorConfiguration i) =
      oscillatorBasis := by
    funext j
    simp only [spectatorBasis,oscillatorBasis,EuclideanSpace.single,PiLp.single]
  rw [hBasis] at he
  simpa only [Function.comp_apply, Complex.real_smul, smul_neg, mul_neg] using he

theorem scalar_coulomb_pair_scaled_finite_reserve (Z E : ℝ)
    {K : Set PairKSSpace} (hK : IsCompact K) (hKpatch : K ⊆ pairKSCoefficientPatch)
    (hbox : ∀ q ∈ K, ‖q.1‖ ≤ (1/4 : ℝ) ∧ ‖q.2‖ ≤ (5/4 : ℝ)) (n : ℕ) :
    ∃ K0 : ℝ, 1 ≤ K0 ∧
      ∀ (Ω W : ℕ → Set PairKSSpace) (χ η : ℕ → PairKSSpace → ℝ)
        (M A B D Q : ℕ → ℝ),
        (∀ k, k < n → SpectatorStepGeometry 1 (Ω k) (Ω (k+1)) (W k)
          (χ k) (η k) (M k) (A k) (B k) (D k) (Q k)) →
        MeasurableSet (Ω 0) → Ω 0 ⊆ K →
        ∀ (f : SpatialL2 2), scalarHamiltonianGraph 2 Z f ((E : ℂ) • f) →
        ∀ (g : Configuration 2 → ℂ), Continuous g →
          (f : Configuration 2 → ℂ) =ᵐ[volume] g →
        ∀ (L : ℝ≥0) (R ε : ℝ), 0 < R → LipschitzOnWith L g (ball 0 R) →
          0 < ε → ε ≤ 1 → ε ≤ R/4 →
          0 ≤ spectatorIterationBudgetSeq 1 M A B D Q K0
            (K0^2*‖g 0‖^2*(volume (Ω 0)).toReal)
            ((2*(L : ℝ))^2*(volume K).toReal) n ∧
          SpectatorFiniteState (Ω n) (originScaledDifference g ε ∘ pairKSLift) n
            (spectatorIterationBudgetSeq 1 M A B D Q K0
              (K0^2*‖g 0‖^2*(volume (Ω 0)).toReal)
              ((2*(L : ℝ))^2*(volume K).toReal) n) := by
  obtain ⟨K0,hK0,hgain⟩ := pairKS_scaled_finite_spectator_reserve Z E hK hKpatch n
  refine ⟨K0,hK0,?_⟩
  intro Ω W χ η M A B D Q hGeom hΩmeas hΩK f hgraph g hg hfg L R ε hR hLip hε hε1 hεR
  have hraw : RegionL2Budget (originScaledDifference g ε ∘ pairKSLift) K
      ((2*(L : ℝ))^2*(volume K).toReal) :=
    pairKS_scaled_difference_compact_L2 hg hR hLip hε hεR hK hbox
  apply hgain Ω W χ η M A B D Q hGeom hΩmeas hΩK ε hε.le hε1
    (g 0) (originScaledDifference g ε ∘ pairKSLift)
    ((2*(L : ℝ))^2*(volume K).toReal) (by positivity)
    (hraw.restrict hΩK le_rfl)
  intro φ hφ hc hs
  have he := (scalar_coulomb_epsilon_pair_KS_difference_weak hε hgraph hg hfg
    hφ hc (hs.trans (hΩK.trans hKpatch))).2.2
  have hBasis : (spectatorBasis : SpectatorCoordinate (0 : Fin 2) →
      SpectatorConfiguration (0 : Fin 2)) = oscillatorBasis := by
    funext j
    simp only [spectatorBasis,oscillatorBasis,EuclideanSpace.single,PiLp.single]
  rw [hBasis] at he
  simpa only [Function.comp_apply, Complex.real_smul, smul_neg, mul_neg] using he

#print axioms scalar_coulomb_nuclear_scaled_finite_reserve
#print axioms scalar_coulomb_pair_scaled_finite_reserve
end TheoremT.Continuum
