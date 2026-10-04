import ManyBody.S8.NuclearKSScaledEquation
import ManyBody.S8.HomogeneousGrushinOneStep
import CoulombSpinNuclearKSOneStep_v1

/-! Physical initialization on one fixed rescaled nuclear chart.
The actual operator coefficient is r*B(Z,rE). The compact set and gain constant
precede radius, charge, energy and state. Budgets use the original spin norm;
the weak derivatives are in the rescaled coordinates.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin
namespace ManyBody.S8

private theorem compact_integral_norm_sq_le
    {K : Set (NuclearKSSpace (0 : Fin 2))} (hK : IsCompact K)
    {g : NuclearKSSpace (0 : Fin 2) → ℂ} (hg : Continuous g)
    {a : ℝ} (ha : 0 ≤ a) (hga : ∀ p ∈ K, ‖g p‖ ≤ a) :
    (∫ p in K, ‖g p‖ ^ 2) ≤ volume.real K * a ^ 2 := by
  calc
    _ ≤ ∫ _p in K, a ^ 2 := by
      apply integral_mono_ae ((hg.norm.pow 2).continuousOn.integrableOn_compact hK)
        (continuousOn_const.integrableOn_compact hK)
      filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
      exact (sq_le_sq₀ (norm_nonneg _) ha).mpr (hga p hp)
    _ = _ := by rw [setIntegral_const, smul_eq_mul]

private theorem spin_component_norm_le
    {u : SpinConfiguration 2 → Configuration 2 → ℂ} {a : ℝ}
    (hbound : ∀ x, Real.sqrt (∑ σ : SpinConfiguration 2, ‖u σ x‖ ^ 2) ≤ a)
    (σ : SpinConfiguration 2) (x : Configuration 2) : ‖u σ x‖ ≤ a := by
  have hs : ‖u σ x‖ ^ 2 ≤ ∑ τ : SpinConfiguration 2, ‖u τ x‖ ^ 2 :=
    Finset.single_le_sum (fun τ _ => sq_nonneg ‖u τ x‖) (Finset.mem_univ σ)
  calc
    _ = Real.sqrt (‖u σ x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := (Real.sqrt_le_sqrt hs).trans (hbound x)


theorem two_electron_rescaled_nuclear_chart_original_norm_initialization
    (t0 : Position) (ht0 : ‖t0‖ = 1)
    {χ : NuclearKSSpace (0 : Fin 2) → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ nuclearChartOpen t0) :
    ∃ K : Set (NuclearKSSpace (0 : Fin 2)), ∃ C : ℝ,
      IsCompact K ∧ tsupport χ ⊆ K ∧ K ⊆ nuclearChartOpen t0 ∧ 0 ≤ C ∧
      ∀ (r : ℝ), 0 < r → ∀ (Z E : ℝ) {ψ : SpinSpace 2},
        hamiltonianGraph 2 Z ψ ((E : ℂ) • ψ) →
        ∃ u : SpinConfiguration 2 → Configuration 2 → ℂ,
          (∀ σ, LocallyLipschitz (u σ)) ∧
          (∀ᵐ x ∂volume, ∀ σ, ψ σ x = u σ x) ∧
          (∀ π : Equiv.Perm (Fin 2), ∀ σ, ∀ x,
            u (permuteSpin π σ) (permuteSpace π x) = permutationSign π • u σ x) ∧
          (∀ x, Real.sqrt (∑ σ : SpinConfiguration 2, ‖u σ x‖ ^ 2) ≤
            coulombMoserBoundCoefficient 2 Z E * ‖ψ‖) ∧
          ∀ σ : SpinConfiguration 2,
            let b : ℝ := r * ((26 / 3 : ℝ) * |Z| + 8 / 11 + r * |E| / 2)
            let A : ℝ := volume.real K * (coulombMoserBoundCoefficient 2 Z E) ^ 2 * ‖ψ‖ ^ 2
            ∃ U : Lp ℂ 2 (volume : Measure (NuclearKSSpace (0 : Fin 2))),
            ∃ gy : Fin 4 → Lp ℂ 2 (volume : Measure (NuclearKSSpace (0 : Fin 2))),
            ∃ gt : SpectatorCoordinate (0 : Fin 2) →
              Lp ℂ 2 (volume : Measure (NuclearKSSpace (0 : Fin 2))),
            ∃ hyy : Fin 4 → Fin 4 →
              Lp ℂ 2 (volume : Measure (NuclearKSSpace (0 : Fin 2))),
              U =ᵐ[volume] (fun p => χ p • u σ
                (nuclearKSLift (0 : Fin 2) (nuclearKSAnisotropicScale (0 : Fin 2) r p))) ∧
              (∑ j, ‖gy j‖ ^ 2) ≤ C * (11 / 4 + 3 / 4 * b ^ 2) * A ∧
              (∑ j, ‖gt j‖ ^ 2) ≤ (C * (1 + b ^ 2) * A) / 64 ∧
              (∑ j, ∑ k, ‖hyy j k‖ ^ 2) ≤ 3 / 2 * C * (1 + b ^ 2) * A ∧
              (∀ j, WeakProductL2Directional U (gy j) (yDir j)) ∧
              (∀ j, WeakProductL2Directional U (gt j) (tDir j)) ∧
              ∀ j k, WeakProductL2Directional (gy j) (hyy j k) (yDir k) := by
  obtain ⟨K, C, hK, hχK, hKΩ, hC, hgain⟩ :=
    local_weak_grushin_homogeneous_cutoff_gain (κ := SpectatorCoordinate (0 : Fin 2))
      (by norm_num : (0 : ℝ) < 4) (nuclearChartOpen_isOpen t0) hχ hcχ hχΩ
  refine ⟨K, C, hK, hχK, hKΩ, hC, ?_⟩
  intro r hr Z E ψ hgraph
  obtain ⟨u, hu, hue, hperm, hbound⟩ :=
    coulomb_spin_locally_lipschitz_representative (by norm_num : 0 < (2 : ℕ)) hgraph
  refine ⟨u, hu, hue, hperm, hbound, ?_⟩
  intro σ
  let B : NuclearKSSpace (0 : Fin 2) → ℝ :=
    fun p => r * nuclearKSPotential (0 : Fin 2) Z (r * E) p
  let raw : NuclearKSSpace (0 : Fin 2) → ℂ := fun p =>
    u σ (nuclearKSLift (0 : Fin 2) (nuclearKSAnisotropicScale (0 : Fin 2) r p))
  let b : ℝ := r * ((26 / 3 : ℝ) * |Z| + 8 / 11 + r * |E| / 2)
  let a : ℝ := coulombMoserBoundCoefficient 2 Z E * ‖ψ‖
  have ha : 0 ≤ a := mul_nonneg (coulombMoserBoundCoefficient_pos 2 Z E).le (norm_nonneg _)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hraw : Continuous raw := (hu σ).continuous.comp
    ((nuclearKSLift_contDiff (0 : Fin 2)).continuous.comp
      (nuclearKSAnisotropicScaleCLM (0 : Fin 2) r).continuous)
  have hlocal : ProductLocallyL2On raw (nuclearChartOpen t0) :=
    product_continuousOn_locallyL2 hraw.continuousOn
  have hB : ContinuousOn B (nuclearChartOpen t0) := by
    intro p hp
    exact continuousAt_const.mul
      (nuclearKSPotential_contDiffAt_omega (0 : Fin 2) Z (r * E)
        (nuclearChartOpen_subset_coefficientPatch t0 ht0 hp)).continuousAt |>.continuousWithinAt
  have hBb : ∀ p ∈ K, ‖B p‖ ≤ b := by
    intro p hp
    have hh := mul_le_mul_of_nonneg_left
      (nuclearKSPotential_rescaled_norm_le Z E hr t0 ht0 (hKΩ hp)) hr.le
    simpa only [B, b, nuclearKSPotential_anisotropicScale (0 : Fin 2) Z E hr,
      norm_mul, Real.norm_eq_abs, abs_of_pos hr] using hh
  have he : (ψ σ : Configuration 2 → ℂ) =ᵐ[volume] u σ := by
    filter_upwards [hue] with x hx
    exact hx σ
  have hP : ∀ φ : NuclearKSSpace (0 : Fin 2) → ℝ, ContDiff ℝ ∞ φ →
      HasCompactSupport φ → tsupport φ ⊆ nuclearChartOpen t0 →
      (∫ p, splitGrushin 4 oscillatorBasis B φ p • raw p) = 0 := by
    intro φ hφ hcφ hsφ
    exact (scalar_coulomb_nuclear_KS_scaled_weak (0 : Fin 2) Z E hr
      (hgraph.2.2 σ) (hu σ).continuous he hφ hcφ
      (hsφ.trans (nuclearChartOpen_subset_coefficientPatch t0 ht0))).2
  have hF : (∫ p in K, ‖raw p‖ ^ 2) ≤
      volume.real K * (coulombMoserBoundCoefficient 2 Z E) ^ 2 * ‖ψ‖ ^ 2 := by
    simpa only [a, mul_pow, mul_assoc] using compact_integral_norm_sq_le hK hraw ha
      (fun p _ => spin_component_norm_le hbound σ _)
  obtain ⟨U, gy, gt, hyy, hU, hY, hT, hYY, hgy, hgt, hhyy⟩ :=
    hgain b B raw hb hB hlocal hBb hP
  refine ⟨U, gy, gt, hyy, hU, ?_, ?_, ?_, hgy, hgt, hhyy⟩
  · exact hY.trans (mul_le_mul_of_nonneg_left hF (by positivity))
  · have hT' : (∑ j, ‖gt j‖ ^ 2) ≤ (C * (1 + b ^ 2) * (∫ p in K, ‖raw p‖ ^ 2)) / 64 := by
      simpa only [show (16 : ℝ) * 4 = 64 by norm_num] using hT
    exact hT'.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hF (by positivity)) (by norm_num))
  · exact hYY.trans (mul_le_mul_of_nonneg_left hF (by positivity))

#print axioms two_electron_rescaled_nuclear_chart_original_norm_initialization
end ManyBody.S8
