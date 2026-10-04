import ManyBody.S8.NuclearChartSpectatorBootstrap

/-! Physical first-spectator TY/TT/TYY budgets in the original state norm.
All compact regions and geometric constants precede charge, energy and state.
The physical equation, outer derivatives and differentiated forcing are proved
by the existing actual chart initialization and spectator gain.
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

private theorem spectator_budget_absorb
    {b0 b1 A F M C L Q H : ℝ}
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hQ : 0 ≤ Q) (hH : 0 ≤ H)
    (hA : A ≤ Q * H) (hF : F ≤ L * (1 + b0 ^ 2) * H)
    (hM : M ≤ 2 * b1 ^ 2 * A + 2 * b0 ^ 2 * F) :
    let R : ℝ := 8 * C * (Q + L) * (1 + b0 ^ 2 + b1 ^ 2) ^ 2 * H
    2 * (C * F) + (3 / 4 : ℝ) * (C * (F + M)) ≤ R ∧
    (C * (F + M)) / 64 ≤ R ∧
    (3 / 2 : ℝ) * (C * (F + M)) ≤ R := by
  let s : ℝ := 1 + b0 ^ 2 + b1 ^ 2
  have hs : 1 ≤ s := by dsimp [s]; nlinarith [sq_nonneg b0, sq_nonneg b1]
  have hs0 : 0 ≤ s := le_trans (by norm_num) hs
  have hss : s ≤ s ^ 2 := by nlinarith
  have h0 : b0 ^ 2 ≤ s := by dsimp [s]; nlinarith [sq_nonneg b1]
  have h1 : b1 ^ 2 ≤ s ^ 2 := by
    apply le_trans (b := s) _ hss
    dsimp [s]
    nlinarith [sq_nonneg b0]
  have h0s : b0 ^ 2 * s ≤ s ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right h0 hs0]
  have hFs : F ≤ L * s * H := by
    apply hF.trans
    gcongr
    dsimp [s]
    nlinarith [sq_nonneg b1]
  have hFsq : F ≤ L * s ^ 2 * H := by
    apply hFs.trans
    gcongr
  have hMsq : M ≤ 2 * (Q + L) * s ^ 2 * H := by
    calc
      _ ≤ 2 * b1 ^ 2 * (Q * H) + 2 * b0 ^ 2 * (L * s * H) :=
        hM.trans (add_le_add
          (mul_le_mul_of_nonneg_left hA (by positivity))
          (mul_le_mul_of_nonneg_left hFs (by positivity)))
      _ = (2 * Q * H) * b1 ^ 2 + (2 * L * H) * (b0 ^ 2 * s) := by ring
      _ ≤ (2 * Q * H) * s ^ 2 + (2 * L * H) * s ^ 2 := add_le_add
        (mul_le_mul_of_nonneg_left h1 (by positivity))
        (mul_le_mul_of_nonneg_left h0s (by positivity))
      _ = _ := by ring
  let q : ℝ := (Q + L) * s ^ 2 * H
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hFq : F ≤ q := by
    apply hFsq.trans
    dsimp [q]
    gcongr
    linarith
  have hMq : M ≤ 2 * q := by
    calc
      M ≤ 2 * (Q + L) * s ^ 2 * H := hMsq
      _ = 2 * q := by dsimp [q]; ring
  have hFMq : F + M ≤ 3 * q := by linarith
  have hY := add_le_add (mul_le_mul_of_nonneg_left hFq (by positivity : 0 ≤ 2 * C))
    (mul_le_mul_of_nonneg_left hFMq (by positivity : 0 ≤ (3 / 4 : ℝ) * C))
  have hT := mul_le_mul_of_nonneg_left hFMq hC
  have hYY := mul_le_mul_of_nonneg_left hFMq (by positivity : 0 ≤ (3 / 2 : ℝ) * C)
  have hCq : 0 ≤ C * q := mul_nonneg hC hq
  have he : 8 * C * (Q + L) * (1 + b0 ^ 2 + b1 ^ 2) ^ 2 * H = 8 * C * q := by
    dsimp [q, s]
    ring
  dsimp only
  rw [he]
  constructor
  · nlinarith
  constructor <;> nlinarith


/-- Fixed-chart physical spectator derivatives with one geometric budget in the
original spin-state norm. The chart/cutoff constants are independent of Z,E,ψ. -/
theorem two_electron_nuclear_chart_spectator_original_norm_budget
    (t0 : Position) (ht0 : ‖t0‖ = 1)
    {χ : NuclearKSSpace (0 : Fin 2) → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ nuclearChartOpen t0) :
    ∃ χouter : NuclearKSSpace (0 : Fin 2) → ℝ,
      ContDiff ℝ ∞ χouter ∧ HasCompactSupport χouter ∧
      tsupport χouter ⊆ nuclearChartOpen t0 ∧
    ∃ V : Set (NuclearKSSpace (0 : Fin 2)),
      IsOpen V ∧ tsupport χ ⊆ V ∧ V ⊆ nuclearChartOpen t0 ∧
      (∀ p ∈ V, χouter p = 1) ∧
    ∃ K0 : Set (NuclearKSSpace (0 : Fin 2)), ∃ C0 : ℝ,
      IsCompact K0 ∧ tsupport χouter ⊆ K0 ∧ K0 ⊆ nuclearChartOpen t0 ∧ 0 ≤ C0 ∧
    ∃ K : Set (NuclearKSSpace (0 : Fin 2)), ∃ C : ℝ, ∃ D : ℝ,
      IsCompact K ∧ tsupport χ ⊆ K ∧ K ⊆ V ∧ 0 ≤ C ∧ 0 ≤ D ∧
      D = 8 * C * (volume.real K + C0 * volume.real K0) ∧
      ∀ (Z E : ℝ) {ψ : SpinSpace 2}, hamiltonianGraph 2 Z ψ ((E : ℂ) • ψ) →
        ∃ u : SpinConfiguration 2 → Configuration 2 → ℂ,
          (∀ σ, LocallyLipschitz (u σ)) ∧
          (∀ᵐ x ∂volume, ∀ σ, ψ σ x = u σ x) ∧
          (∀ π : Equiv.Perm (Fin 2), ∀ σ, ∀ x,
            u (permuteSpin π σ) (permuteSpace π x) = permutationSign π • u σ x) ∧
          (∀ x, Real.sqrt (∑ σ : SpinConfiguration 2, ‖u σ x‖ ^ 2) ≤
            coulombMoserBoundCoefficient 2 Z E * ‖ψ‖) ∧
          ∀ σ : SpinConfiguration 2,
            let b0 : ℝ := (26 / 3 : ℝ) * |Z| + 8 / 11 + |E| / 2
            let b1 : ℝ := (8 / 9 : ℝ) * |Z| + 128 / 121
            let H : ℝ := (coulombMoserBoundCoefficient 2 Z E) ^ 2 * ‖ψ‖ ^ 2
            let R : ℝ := D * (1 + b0 ^ 2 + b1 ^ 2) ^ 2 * H
            ∃ U : Lp ℂ 2 (volume : Measure (NuclearKSSpace (0 : Fin 2))),
            ∃ d : SpectatorCoordinate (0 : Fin 2) →
              Lp ℂ 2 (volume : Measure (NuclearKSSpace (0 : Fin 2))),
              U =ᵐ[volume] (fun p => χouter p • u σ (nuclearKSLift (0 : Fin 2) p)) ∧
              (∀ j, WeakProductL2Directional U (d j) (tDir j)) ∧
              (∑ j, ‖d j‖ ^ 2) ≤ (C0 * (1 + b0 ^ 2) * volume.real K0 * H) / 64 ∧
              ∀ j : SpectatorCoordinate (0 : Fin 2),
                ∃ W : Lp ℂ 2 (volume : Measure (NuclearKSSpace (0 : Fin 2))),
                ∃ gy : Fin 4 → Lp ℂ 2 (volume : Measure (NuclearKSSpace (0 : Fin 2))),
                ∃ gt : SpectatorCoordinate (0 : Fin 2) →
                  Lp ℂ 2 (volume : Measure (NuclearKSSpace (0 : Fin 2))),
                ∃ hyy : Fin 4 → Fin 4 →
                  Lp ℂ 2 (volume : Measure (NuclearKSSpace (0 : Fin 2))),
                  W =ᵐ[volume] (fun p => χ p • d j p) ∧
                  (∑ i, ‖gy i‖ ^ 2) ≤ R ∧
                  (∑ k, ‖gt k‖ ^ 2) ≤ R ∧
                  (∑ i, ∑ k, ‖hyy i k‖ ^ 2) ≤ R ∧
                  (∀ i, WeakProductL2Directional W (gy i) (yDir i)) ∧
                  (∀ k, WeakProductL2Directional W (gt k) (tDir k)) ∧
                  ∀ i k, WeakProductL2Directional (gy i) (hyy i k) (yDir k) := by
  obtain ⟨χouter, houter, hcouter, hsouter, V, hV, hχV, hVO, houter1⟩ :=
    exists_outer_plateau hcχ (nuclearChartOpen_isOpen t0) hχΩ
  obtain ⟨K0, C0, hK0, houterK0, hK0Ω, hC0, hinit⟩ :=
    two_electron_nuclear_chart_initialization t0 ht0 houter hcouter hsouter
  obtain ⟨K, C, hK, hχK, hKV, hC, hgain⟩ :=
    local_weak_grushin_spectator_cutoff_gain (κ := SpectatorCoordinate (0 : Fin 2))
      (by norm_num : (0 : ℝ) < 4) hV hχ hcχ hχV
  let D : ℝ := 8 * C * (volume.real K + C0 * volume.real K0)
  have hvolK : 0 ≤ volume.real K := ENNReal.toReal_nonneg
  have hvolK0 : 0 ≤ volume.real K0 := ENNReal.toReal_nonneg
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨χouter, houter, hcouter, hsouter, V, hV, hχV, hVO, houter1,
    K0, C0, hK0, houterK0, hK0Ω, hC0, K, C, D, hK, hχK, hKV, hC, hD, rfl, ?_⟩
  intro Z E ψ hgraph
  obtain ⟨u, hu, hue, hperm, hbound, huinit⟩ := hinit Z E hgraph
  refine ⟨u, hu, hue, hperm, hbound, ?_⟩
  intro σ
  let b0 : ℝ := (26 / 3 : ℝ) * |Z| + 8 / 11 + |E| / 2
  let b1 : ℝ := (8 / 9 : ℝ) * |Z| + 128 / 121
  let H : ℝ := (coulombMoserBoundCoefficient 2 Z E) ^ 2 * ‖ψ‖ ^ 2
  let a : ℝ := coulombMoserBoundCoefficient 2 Z E * ‖ψ‖
  have ha : 0 ≤ a := mul_nonneg (coulombMoserBoundCoefficient_pos 2 Z E).le (norm_nonneg _)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hraw (p : NuclearKSSpace (0 : Fin 2)) :
      ‖u σ (nuclearKSLift (0 : Fin 2) p)‖ ≤ a :=
    spin_component_norm_le hbound σ _
  have hcont : Continuous (fun p => u σ (nuclearKSLift (0 : Fin 2) p)) :=
    (hu σ).continuous.comp (nuclearKSLift_contDiff (0 : Fin 2)).continuous
  have hF0 : (∫ p in K0, ‖u σ (nuclearKSLift (0 : Fin 2) p)‖ ^ 2) ≤
      volume.real K0 * H := by
    simpa only [a, H, mul_pow] using
      compact_integral_norm_sq_le hK0 hcont ha (fun p _ => hraw p)
  obtain ⟨U, gy0, d, hyy0, hU, hY0, hT0, hYY0, hgy0, hd, hhyy0⟩ := huinit σ
  have houterT : (∑ j, ‖d j‖ ^ 2) ≤
      (C0 * (1 + b0 ^ 2) * volume.real K0 * H) / 64 := by
    change (∑ j, ‖d j‖ ^ 2) ≤ (C0 * (1 + b0 ^ 2) *
      (∫ p in K0, ‖u σ (nuclearKSLift (0 : Fin 2) p)‖ ^ 2)) / 64 at hT0
    calc
      _ ≤ _ := hT0
      _ ≤ (C0 * (1 + b0 ^ 2) * (volume.real K0 * H)) / 64 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hF0 (by positivity)) (by norm_num)
      _ = _ := by ring
  refine ⟨U, d, hU, hd, houterT, ?_⟩
  intro j
  let F : ℝ := ∫ p in K, ‖d j p‖ ^ 2
  let A : ℝ := ∫ p in K, ‖U p‖ ^ 2
  let M : ℝ := ∫ p in K,
    ‖-(fderiv ℝ (nuclearKSPotential (0 : Fin 2) Z E) p (tDir j) • U p) -
      nuclearKSPotential (0 : Fin 2) Z E p • d j p‖ ^ 2
  have hF : F ≤ (C0 * volume.real K0) * (1 + b0 ^ 2) * H := by
    calc
      _ ≤ ∫ p, ‖d j p‖ ^ 2 := setIntegral_le_integral
        ((Lp.memLp (d j)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
        (Eventually.of_forall (fun p => sq_nonneg _))
      _ = ‖d j‖ ^ 2 := (l2_norm_sq_integral (d j)).symm
      _ ≤ ∑ k, ‖d k‖ ^ 2 :=
        Finset.single_le_sum (fun k _ => sq_nonneg ‖d k‖) (Finset.mem_univ j)
      _ ≤ _ := houterT
      _ ≤ C0 * (1 + b0 ^ 2) * volume.real K0 * H := by
        have hp : 0 ≤ C0 * (1 + b0 ^ 2) * volume.real K0 * H := by positivity
        linarith
      _ = _ := by ring
  have hA : A ≤ volume.real K * H := by
    have heq : A = ∫ p in K, ‖u σ (nuclearKSLift (0 : Fin 2) p)‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hU, ae_restrict_mem hK.measurableSet] with p hp hm
      rw [hp, houter1 p (hKV hm), one_smul]
    rw [heq]
    simpa only [a, H, mul_pow] using
      compact_integral_norm_sq_le hK hcont ha (fun p _ => hraw p)
  have hM : M ≤ 2 * b1 ^ 2 * A + 2 * b0 ^ 2 * F :=
    nuclear_chart_spectator_forcing_integral_le Z E t0 ht0 hK
      (hKV.trans hVO) U (d j) j
  have hab := spectator_budget_absorb
    hC (mul_nonneg hC0 hvolK0) hvolK hH hA hF hM
  have he : (ψ σ : Configuration 2 → ℂ) =ᵐ[volume] u σ := by
    filter_upwards [hue] with x hx
    exact hx σ
  have hP := scalar_nuclear_output_on_plateau (0 : Fin 2) Z E (hgraph.2.2 σ)
    (hu σ).continuous he hU hVO (nuclearChartOpen_subset_coefficientPatch t0 ht0) houter1
  have hB : ContDiffOn ℝ ∞ (nuclearKSPotential (0 : Fin 2) Z E) V := by
    intro p hp
    exact (nuclearKSPotential_contDiffAt (0 : Fin 2) Z E
      (nuclearChartOpen_subset_coefficientPatch t0 ht0 (hVO hp))).contDiffWithinAt
  obtain ⟨W, gy, gt, hyy, hW, hY, hT, hYY, hgy, hgt, hhyy⟩ :=
    hgain (nuclearKSPotential (0 : Fin 2) Z E) U (d j) j hB (hd j) hP
  refine ⟨W, gy, gt, hyy, hW, ?_, ?_, ?_, hgy, hgt, hhyy⟩
  · simpa only [D, H, mul_assoc] using hY.trans hab.1
  · have hT' : (∑ k, ‖gt k‖ ^ 2) ≤ (C * (F + M)) / 64 := by
      simpa only [show (16 : ℝ) * 4 = 64 by norm_num] using hT
    simpa only [D, H, mul_assoc] using hT'.trans hab.2.1
  · simpa only [D, H, mul_assoc] using hYY.trans hab.2.2

#print axioms two_electron_nuclear_chart_spectator_original_norm_budget
end ManyBody.S8
