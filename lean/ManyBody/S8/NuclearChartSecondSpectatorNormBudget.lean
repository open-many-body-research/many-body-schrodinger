import ManyBody.S8.NuclearChartSpectatorNormBudget
import ManyBody.S8.Internal.NuclearChartSecondDerivativeBounds
import ManyBody.S8.Internal.HigherSpectatorRegularity
/-! Finite second-spectator budgets in the original physical spin-state norm.
All nested cutoffs and geometric constants precede charge, energy and state.
The differentiated weak equation is derived from the original physical graph.
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

private theorem lp_integral_norm_sq_le
    (K : Set (NuclearKSSpace (0 : Fin 2)))
    (d : Lp ℂ 2 (volume : Measure (NuclearKSSpace (0 : Fin 2)))) :
    (∫ p in K, ‖d p‖ ^ 2) ≤ ‖d‖ ^ 2 := by
  calc
    _ ≤ ∫ p, ‖d p‖ ^ 2 := setIntegral_le_integral
      ((Lp.memLp d).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
      (Eventually.of_forall (fun p => sq_nonneg _))
    _ = _ := (l2_norm_sq_integral d).symm

private theorem second_spectator_budget_absorb
    {b0 b1 b2 F F1 A M C D1 L Q H : ℝ}
    (hC : 0 ≤ C) (hD1 : 0 ≤ D1) (hL : 0 ≤ L) (hQ : 0 ≤ Q) (hH : 0 ≤ H)
    (hF : F ≤ D1 * (1 + b0 ^ 2 + b1 ^ 2) ^ 2 * H)
    (hF1 : F1 ≤ L * (1 + b0 ^ 2) * H) (hA : A ≤ Q * H)
    (hM : M ≤ 4 * b0 ^ 2 * F + 8 * b1 ^ 2 * F1 + 4 * b2 ^ 2 * A) :
    let R : ℝ := 16 * C * (D1 + L + Q) * (1 + b0 ^ 2 + b1 ^ 2 + b2 ^ 2) ^ 3 * H
    2 * (C * F) + (3 / 4 : ℝ) * (C * (F + M)) ≤ R ∧
    (C * (F + M)) / 64 ≤ R ∧
    (3 / 2 : ℝ) * (C * (F + M)) ≤ R := by
  let s : ℝ := 1 + b0 ^ 2 + b1 ^ 2 + b2 ^ 2
  have hs : 1 ≤ s := by dsimp [s]; nlinarith [sq_nonneg b0, sq_nonneg b1, sq_nonneg b2]
  have hs0 : 0 ≤ s := le_trans (by norm_num) hs
  have h02 : b0 ^ 2 ≤ s := by dsimp [s]; nlinarith [sq_nonneg b1, sq_nonneg b2]
  have h12 : b1 ^ 2 ≤ s := by dsimp [s]; nlinarith [sq_nonneg b0, sq_nonneg b2]
  have h22 : b2 ^ 2 ≤ s := by dsimp [s]; nlinarith [sq_nonneg b0, sq_nonneg b1]
  have hss : s ≤ s ^ 2 := by nlinarith
  have hsss : s ^ 2 ≤ s ^ 3 := by nlinarith [sq_nonneg s, mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hs)]
  have hF' : F ≤ D1 * s ^ 2 * H := by
    apply hF.trans
    gcongr
    dsimp [s]
    nlinarith [sq_nonneg b2]
  have hF1' : F1 ≤ L * s * H := by
    apply hF1.trans
    gcongr
    dsimp [s]
    nlinarith [sq_nonneg b1, sq_nonneg b2]
  have hMs : M ≤ (4 * D1 + 8 * L + 4 * Q) * s ^ 3 * H := by
    calc
      _ ≤ 4 * b0 ^ 2 * (D1 * s ^ 2 * H) +
          8 * b1 ^ 2 * (L * s * H) + 4 * b2 ^ 2 * (Q * H) :=
        hM.trans (add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left hF' (by positivity))
          (mul_le_mul_of_nonneg_left hF1' (by positivity)))
          (mul_le_mul_of_nonneg_left hA (by positivity)))
      _ = (4 * D1 * H) * (b0 ^ 2 * s ^ 2) +
          (8 * L * H) * (b1 ^ 2 * s) + (4 * Q * H) * b2 ^ 2 := by ring
      _ ≤ (4 * D1 * H) * s ^ 3 + (8 * L * H) * s ^ 3 +
          (4 * Q * H) * s ^ 3 := by
        apply add_le_add
        · apply add_le_add
          · apply mul_le_mul_of_nonneg_left _ (by positivity)
            calc
              _ ≤ s * s ^ 2 := mul_le_mul_of_nonneg_right h02 (sq_nonneg s)
              _ = _ := by ring
          · apply mul_le_mul_of_nonneg_left _ (by positivity)
            calc
              _ ≤ s * s := mul_le_mul_of_nonneg_right h12 hs0
              _ = s ^ 2 := by ring
              _ ≤ _ := hsss
        · exact mul_le_mul_of_nonneg_left (h22.trans (hss.trans hsss)) (by positivity)
      _ = _ := by ring
  let q : ℝ := (D1 + L + Q) * s ^ 3 * H
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hFq : F ≤ q := by
    apply hF'.trans
    dsimp [q]
    gcongr
    linarith
  have hMq : M ≤ 8 * q := by
    apply hMs.trans
    dsimp [q]
    have hh : 4 * D1 + 8 * L + 4 * Q ≤ 8 * (D1 + L + Q) := by linarith
    have ht := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (pow_nonneg hs0 3)) hH
    nlinarith only [ht]
  have hFMq : F + M ≤ 9 * q := by linarith
  have hY := add_le_add (mul_le_mul_of_nonneg_left hFq (by positivity : 0 ≤ 2 * C))
    (mul_le_mul_of_nonneg_left hFMq (by positivity : 0 ≤ (3 / 4 : ℝ) * C))
  have hT := mul_le_mul_of_nonneg_left hFMq hC
  have hYY := mul_le_mul_of_nonneg_left hFMq (by positivity : 0 ≤ (3 / 2 : ℝ) * C)
  have hCq : 0 ≤ C * q := mul_nonneg hC hq
  have he : 16 * C * (D1 + L + Q) * (1 + b0 ^ 2 + b1 ^ 2 + b2 ^ 2) ^ 3 * H = 16 * C * q := by
    dsimp [q, s]
    ring
  dsimp only
  rw [he]
  constructor
  · nlinarith only [hY, hCq]
  constructor
  · nlinarith only [hT, hCq]
  · nlinarith only [hYY, hCq]

private theorem second_spectator_forcing_integral_le
    {Ω K : Set (NuclearKSSpace (0 : Fin 2))} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {B : NuclearKSSpace (0 : Fin 2) → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    (U d W e : Lp ℂ 2 (volume : Measure (NuclearKSSpace (0 : Fin 2))))
    (j k : SpectatorCoordinate (0 : Fin 2))
    {b0 b1 b2 : ℝ} (_hb0 : 0 ≤ b0) (_hb1 : 0 ≤ b1) (_hb2 : 0 ≤ b2)
    (hBb : ∀ p ∈ K, ‖B p‖ ≤ b0)
    (hDbj : ∀ p ∈ K, ‖fderiv ℝ B p (tDir j)‖ ≤ b1)
    (hDbk : ∀ p ∈ K, ‖fderiv ℝ B p (tDir k)‖ ≤ b1)
    (hD2 : ∀ p ∈ K, ‖fderiv ℝ (fun z => fderiv ℝ B z (tDir j)) p (tDir k)‖ ≤ b2) :
    (∫ p in K, ‖(-(fderiv ℝ B p (tDir j) • d p +
        fderiv ℝ (fun z => fderiv ℝ B z (tDir j)) p (tDir k) • U p) -
        fderiv ℝ B p (tDir k) • W p) - B p • e p‖ ^ 2) ≤
      4 * b1 ^ 2 * (∫ p in K, ‖d p‖ ^ 2) +
      4 * b2 ^ 2 * (∫ p in K, ‖U p‖ ^ 2) +
      4 * b1 ^ 2 * (∫ p in K, ‖W p‖ ^ 2) +
      4 * b0 ^ 2 * (∫ p in K, ‖e p‖ ^ 2) := by
  have hAj : ContDiffOn ℝ ∞ (fun p => fderiv ℝ B p (tDir j)) Ω := by
    intro p hp
    exact (local_contDiffAt_directional_derivative (hB.contDiffAt (hΩ.mem_nhds hp)) (tDir j)).contDiffWithinAt
  have hmj := smooth_coefficient_and_directional_memLp_top_restrict_compact
    (μ := volume) hΩ hK hKΩ hB (tDir j)
  have hmk := smooth_coefficient_and_directional_memLp_top_restrict_compact
    (μ := volume) hΩ hK hKΩ hB (tDir k)
  have hmjk := smooth_coefficient_and_directional_memLp_top_restrict_compact
    (μ := volume) hΩ hK hKΩ hAj (tDir k)
  have hUl := (Lp.memLp U).mono_measure (Measure.restrict_le_self (μ := volume) (s := K))
  have hdl := (Lp.memLp d).mono_measure (Measure.restrict_le_self (μ := volume) (s := K))
  have hWl := (Lp.memLp W).mono_measure (Measure.restrict_le_self (μ := volume) (s := K))
  have hel := (Lp.memLp e).mono_measure (Measure.restrict_le_self (μ := volume) (s := K))
  have hsource : MemLp (fun p => (-(fderiv ℝ B p (tDir j) • d p +
      fderiv ℝ (fun z => fderiv ℝ B z (tDir j)) p (tDir k) • U p) -
      fderiv ℝ B p (tDir k) • W p) - B p • e p) 2 (volume.restrict K) :=
    (((hdl.smul hmj.2).add (hUl.smul hmjk.2)).neg.sub (hWl.smul hmk.2)).sub (hel.smul hmj.1)
  have hi := hsource.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hiU := hUl.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hid := hdl.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hiW := hWl.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hie := hel.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hi12 : Integrable (fun p => 4 * b1 ^ 2 * ‖d p‖ ^ 2 + 4 * b2 ^ 2 * ‖U p‖ ^ 2) (volume.restrict K) :=
    (hid.const_mul _).add (hiU.const_mul _)
  have hi123 : Integrable (fun p => 4 * b1 ^ 2 * ‖d p‖ ^ 2 + 4 * b2 ^ 2 * ‖U p‖ ^ 2 +
      4 * b1 ^ 2 * ‖W p‖ ^ 2) (volume.restrict K) := hi12.add (hiW.const_mul _)
  have hi1234 : Integrable (fun p => 4 * b1 ^ 2 * ‖d p‖ ^ 2 + 4 * b2 ^ 2 * ‖U p‖ ^ 2 +
      4 * b1 ^ 2 * ‖W p‖ ^ 2 + 4 * b0 ^ 2 * ‖e p‖ ^ 2) (volume.restrict K) :=
    hi123.add (hie.const_mul _)
  calc
    _ ≤ ∫ p in K, 4 * b1 ^ 2 * ‖d p‖ ^ 2 + 4 * b2 ^ 2 * ‖U p‖ ^ 2 +
        4 * b1 ^ 2 * ‖W p‖ ^ 2 + 4 * b0 ^ 2 * ‖e p‖ ^ 2 := by
      apply integral_mono_ae hi hi1234
      filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
      have hn : ‖(-(fderiv ℝ B p (tDir j) • d p +
          fderiv ℝ (fun z => fderiv ℝ B z (tDir j)) p (tDir k) • U p) -
          fderiv ℝ B p (tDir k) • W p) - B p • e p‖ ≤
          b1 * ‖d p‖ + b2 * ‖U p‖ + b1 * ‖W p‖ + b0 * ‖e p‖ := by
        calc
          _ ≤ ‖fderiv ℝ B p (tDir j) • d p +
              fderiv ℝ (fun z => fderiv ℝ B z (tDir j)) p (tDir k) • U p‖ +
              ‖fderiv ℝ B p (tDir k) • W p‖ + ‖B p • e p‖ := by
            simpa only [norm_neg] using
              (norm_sub_le
                (-(fderiv ℝ B p (tDir j) • d p +
                  fderiv ℝ (fun z => fderiv ℝ B z (tDir j)) p (tDir k) • U p) -
                  fderiv ℝ B p (tDir k) • W p) (B p • e p)).trans
                (add_le_add (norm_sub_le
                  (-(fderiv ℝ B p (tDir j) • d p +
                    fderiv ℝ (fun z => fderiv ℝ B z (tDir j)) p (tDir k) • U p))
                  (fderiv ℝ B p (tDir k) • W p)) (le_refl ‖B p • e p‖))
          _ ≤ (‖fderiv ℝ B p (tDir j) • d p‖ +
              ‖fderiv ℝ (fun z => fderiv ℝ B z (tDir j)) p (tDir k) • U p‖) +
              ‖fderiv ℝ B p (tDir k) • W p‖ + ‖B p • e p‖ := by
            gcongr
            exact norm_add_le _ _
          _ ≤ _ := by
            simp only [norm_smul]
            gcongr
            · exact hDbj p hp
            · exact hD2 p hp
            · exact hDbk p hp
            · exact hBb p hp
      have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
      nlinarith [sq_nonneg (b1 * ‖d p‖ - b2 * ‖U p‖),
        sq_nonneg (b1 * ‖d p‖ - b1 * ‖W p‖), sq_nonneg (b1 * ‖d p‖ - b0 * ‖e p‖),
        sq_nonneg (b2 * ‖U p‖ - b1 * ‖W p‖), sq_nonneg (b2 * ‖U p‖ - b0 * ‖e p‖),
        sq_nonneg (b1 * ‖W p‖ - b0 * ‖e p‖)]
    _ = _ := by
      rw [integral_add hi123 (hie.const_mul _),
        integral_add hi12 (hiW.const_mul _),
        integral_add (hid.const_mul _) (hiU.const_mul _)]
      simp only [integral_const_mul]

/-- The second spectator derivatives have finite Y/T/YY budgets in the original
physical state norm, with one geometric constant fixed before Z,E,ψ. -/
theorem two_electron_nuclear_chart_second_spectator_original_norm_budget
    (t0 : Position) (ht0 : ‖t0‖ = 1)
    {χ : NuclearKSSpace (0 : Fin 2) → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ nuclearChartOpen t0) :
    ∃ χouter χmiddle : NuclearKSSpace (0 : Fin 2) → ℝ,
      ContDiff ℝ ∞ χouter ∧ HasCompactSupport χouter ∧
      tsupport χouter ⊆ nuclearChartOpen t0 ∧
      ContDiff ℝ ∞ χmiddle ∧ HasCompactSupport χmiddle ∧
      tsupport χmiddle ⊆ nuclearChartOpen t0 ∧
    ∃ V : Set (NuclearKSSpace (0 : Fin 2)),
      IsOpen V ∧ tsupport χ ⊆ V ∧ V ⊆ nuclearChartOpen t0 ∧
      (∀ p ∈ V, χouter p = 1 ∧ χmiddle p = 1) ∧
    ∃ D : ℝ, 0 ≤ D ∧
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
            let b2 : ℝ := (128 / 27 : ℝ) * |Z| + 8192 / 1331
            let R : ℝ := D * (1 + b0 ^ 2 + b1 ^ 2 + b2 ^ 2) ^ 3 *
              (coulombMoserBoundCoefficient 2 Z E) ^ 2 * ‖ψ‖ ^ 2
            ∃ U : Lp ℂ 2 (volume : Measure (NuclearKSSpace (0 : Fin 2))),
            ∃ d : SpectatorCoordinate (0 : Fin 2) →
              Lp ℂ 2 (volume : Measure (NuclearKSSpace (0 : Fin 2))),
            ∃ W : SpectatorCoordinate (0 : Fin 2) →
              Lp ℂ 2 (volume : Measure (NuclearKSSpace (0 : Fin 2))),
            ∃ e : SpectatorCoordinate (0 : Fin 2) → SpectatorCoordinate (0 : Fin 2) →
              Lp ℂ 2 (volume : Measure (NuclearKSSpace (0 : Fin 2))),
              U =ᵐ[volume] (fun p => χouter p • u σ (nuclearKSLift (0 : Fin 2) p)) ∧
              (∀ j, WeakProductL2Directional U (d j) (tDir j)) ∧
              ∀ j : SpectatorCoordinate (0 : Fin 2),
                W j =ᵐ[volume] (fun p => χmiddle p • d j p) ∧
                (∀ k, WeakProductL2Directional (W j) (e j k) (tDir k)) ∧
                ∀ k : SpectatorCoordinate (0 : Fin 2),
                  ∃ A : Lp ℂ 2 (volume : Measure (NuclearKSSpace (0 : Fin 2))),
                  ∃ gy : Fin 4 → Lp ℂ 2 (volume : Measure (NuclearKSSpace (0 : Fin 2))),
                  ∃ gt : SpectatorCoordinate (0 : Fin 2) →
                    Lp ℂ 2 (volume : Measure (NuclearKSSpace (0 : Fin 2))),
                  ∃ hyy : Fin 4 → Fin 4 →
                    Lp ℂ 2 (volume : Measure (NuclearKSSpace (0 : Fin 2))),
                    A =ᵐ[volume] (fun p => χ p • e j k p) ∧
                    (∑ i, ‖gy i‖ ^ 2) ≤ R ∧
                    (∑ l, ‖gt l‖ ^ 2) ≤ R ∧
                    (∑ i, ∑ l, ‖hyy i l‖ ^ 2) ≤ R ∧
                    (∀ i, WeakProductL2Directional A (gy i) (yDir i)) ∧
                    (∀ l, WeakProductL2Directional A (gt l) (tDir l)) ∧
                    ∀ i l, WeakProductL2Directional (gy i) (hyy i l) (yDir l) := by
  obtain ⟨χmiddle, hmiddle, hcmiddle, hsmiddle, Vmiddle, hVmiddle, hχVmiddle, hVmiddleΩ, hmiddle1⟩ :=
    exists_outer_plateau hcχ (nuclearChartOpen_isOpen t0) hχΩ
  obtain ⟨χouter, houter, hcouter, hsouter, Vouter, hVouter, hmiddleVouter, hVouterΩ, houter1,
      K0, C0, hK0, houterK0, hK0Ω, hC0, K1, C1, D1, hK1, hmiddleK1, hK1Vouter, hC1, hD1, hD1eq, hfirst⟩ :=
    two_electron_nuclear_chart_spectator_original_norm_budget t0 ht0 hmiddle hcmiddle hsmiddle
  have hχmiddle : tsupport χ ⊆ tsupport χmiddle := by
    intro p hp
    by_contra hn
    have hh := image_eq_zero_of_notMem_tsupport hn
    rw [hmiddle1 p (hχVmiddle hp)] at hh
    norm_num at hh
  let V := Vmiddle ∩ Vouter
  have hV : IsOpen V := hVmiddle.inter hVouter
  have hχV : tsupport χ ⊆ V := fun p hp => ⟨hχVmiddle hp, hmiddleVouter (hχmiddle hp)⟩
  have hVO : V ⊆ nuclearChartOpen t0 := fun _ hp => hVouterΩ hp.2
  obtain ⟨K2, C2, hK2, hχK2, hK2V, hC2, hgain⟩ :=
    local_weak_grushin_potential_cutoff_gain (κ := SpectatorCoordinate (0 : Fin 2))
      (by norm_num : (0 : ℝ) < 4) hV hχ hcχ hχV
  let L : ℝ := C0 * volume.real K0
  let Q : ℝ := volume.real K2
  let D : ℝ := 16 * C2 * (D1 + L + Q)
  have hL : 0 ≤ L := mul_nonneg hC0 ENNReal.toReal_nonneg
  have hQ : 0 ≤ Q := ENNReal.toReal_nonneg
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨χouter, χmiddle, houter, hcouter, hsouter, hmiddle, hcmiddle, hsmiddle,
    V, hV, hχV, hVO, (fun p hp => ⟨houter1 p hp.2, hmiddle1 p hp.1⟩), D, hD, ?_⟩
  intro Z E ψ hgraph
  obtain ⟨u, hu, hue, hperm, hbound, hfirstu⟩ := hfirst Z E hgraph
  refine ⟨u, hu, hue, hperm, hbound, ?_⟩
  intro σ
  let B := nuclearKSPotential (0 : Fin 2) Z E
  let b0 : ℝ := (26 / 3 : ℝ) * |Z| + 8 / 11 + |E| / 2
  let b1 : ℝ := (8 / 9 : ℝ) * |Z| + 128 / 121
  let b2 : ℝ := (128 / 27 : ℝ) * |Z| + 8192 / 1331
  let H : ℝ := (coulombMoserBoundCoefficient 2 Z E) ^ 2 * ‖ψ‖ ^ 2
  let a : ℝ := coulombMoserBoundCoefficient 2 Z E * ‖ψ‖
  have hb0 : 0 ≤ b0 := by dsimp [b0]; positivity
  have hb1 : 0 ≤ b1 := by dsimp [b1]; positivity
  have hb2 : 0 ≤ b2 := by dsimp [b2]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have ha : 0 ≤ a := mul_nonneg (coulombMoserBoundCoefficient_pos 2 Z E).le (norm_nonneg _)
  obtain ⟨U, d, hU, hd, hdBudget, hfirstσ⟩ := hfirstu σ
  change (∑ j, ‖d j‖ ^ 2) ≤ (C0 * (1 + b0 ^ 2) * volume.real K0 * H) / 64 at hdBudget
  choose W gy1 e hyy1 hW hY1 hT1 hYY1 hgy1 he hhyy1 using hfirstσ
  have hdGlobal (l : SpectatorCoordinate (0 : Fin 2)) : ‖d l‖ ^ 2 ≤ L * (1 + b0 ^ 2) * H := by
    calc
      _ ≤ ∑ m, ‖d m‖ ^ 2 := Finset.single_le_sum (fun m _ => sq_nonneg ‖d m‖) (Finset.mem_univ l)
      _ ≤ _ := hdBudget
      _ ≤ C0 * (1 + b0 ^ 2) * volume.real K0 * H := by
        have hh : 0 ≤ C0 * (1 + b0 ^ 2) * volume.real K0 * H := by positivity
        linarith
      _ = _ := by dsimp [L]; ring
  have hfg : (ψ σ : Configuration 2 → ℂ) =ᵐ[volume] u σ := by
    filter_upwards [hue] with x hx
    exact hx σ
  have hP0 := scalar_nuclear_output_on_plateau (0 : Fin 2) Z E (hgraph.2.2 σ)
    (hu σ).continuous hfg hU hVO (nuclearChartOpen_subset_coefficientPatch t0 ht0)
    (fun p hp => houter1 p hp.2)
  have hB : ContDiffOn ℝ ∞ B V := by
    intro p hp
    exact (nuclearKSPotential_contDiffAt (0 : Fin 2) Z E
      (nuclearChartOpen_subset_coefficientPatch t0 ht0 (hVO hp))).contDiffWithinAt
  have hA0 : (∫ p in K2, ‖U p‖ ^ 2) ≤ Q * H := by
    have heq : (∫ p in K2, ‖U p‖ ^ 2) = ∫ p in K2, ‖u σ (nuclearKSLift (0 : Fin 2) p)‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hU, ae_restrict_mem hK2.measurableSet] with p hp hm
      rw [hp, houter1 p (hK2V hm).2, one_smul]
    rw [heq]
    have hcont := (hu σ).continuous.comp (nuclearKSLift_contDiff (0 : Fin 2)).continuous
    simpa only [Q, H, a, mul_pow, Function.comp_apply] using compact_integral_norm_sq_le hK2 hcont ha
      (fun p _ => spin_component_norm_le hbound σ _)
  have hdLocal (l : SpectatorCoordinate (0 : Fin 2)) :
      (∫ p in K2, ‖d l p‖ ^ 2) ≤ L * (1 + b0 ^ 2) * H :=
    (lp_integral_norm_sq_le K2 (d l)).trans (hdGlobal l)
  have hWLocal (l : SpectatorCoordinate (0 : Fin 2)) :
      (∫ p in K2, ‖W l p‖ ^ 2) ≤ L * (1 + b0 ^ 2) * H := by
    have heq : (∫ p in K2, ‖W l p‖ ^ 2) = ∫ p in K2, ‖d l p‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (hW l), ae_restrict_mem hK2.measurableSet] with p hp hm
      rw [hp, hmiddle1 p (hK2V hm).1, one_smul]
    rw [heq]
    exact hdLocal l
  refine ⟨U, d, W, e, hU, hd, ?_⟩
  intro j
  refine ⟨hW j, he j, ?_⟩
  intro k
  let Aj := fun p => fderiv ℝ B p (tDir j)
  let gj := fun p => -(Aj p • U p)
  let kjk := fun p => -(Aj p • d k p + fderiv ℝ Aj p (tDir k) • U p)
  have hAj : ContDiffOn ℝ ∞ Aj V := by
    intro p hp
    exact (local_contDiffAt_directional_derivative (hB.contDiffAt (hV.mem_nhds hp)) (tDir j)).contDiffWithinAt
  obtain ⟨hgj, hPj⟩ := weak_grushin_homogeneous_spectator_equation 4 hV hB j (hd j) hP0
  have hkjk : ProductLocallyL2On kjk V := by
    intro K hK hKV
    exact ((product_spectator_potential_leibniz_locallyL2 hV hAj U (d k)
      (oscillatorBasis k)) K hK hKV).neg
  have hgjD : ∀ φ : NuclearKSSpace (0 : Fin 2) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∫ p, φ p • kjk p) = -(∫ p, fderiv ℝ φ p (tDir k) • gj p) := by
    intro φ hφ hcφ hsφ
    have hh := (weakProduct_directional_local_potential_test (hd k) hV hAj hφ hcφ hsφ).2.2
    simpa only [kjk, gj, tDir, smul_neg, integral_neg, neg_neg] using congrArg Neg.neg hh
  have hPW : ∀ φ : NuclearKSSpace (0 : Fin 2) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∫ p, splitGrushin 4 oscillatorBasis B φ p • W j p) = ∫ p, φ p • gj p := by
    intro φ hφ hcφ hsφ
    calc
      _ = ∫ p, splitGrushin 4 oscillatorBasis B φ p • d j p := by
        apply integral_congr_ae
        filter_upwards [hW j] with p hp
        by_cases ht : p ∈ tsupport φ
        · rw [hp, hmiddle1 p (hsφ ht).1, one_smul]
        · rw [splitGrushin_zero_off_test 4 oscillatorBasis B ht]
          simp only [zero_smul]
      _ = _ := hPj φ hφ hcφ hsφ
  obtain ⟨hsource, hdiff⟩ := weak_grushin_inhomogeneous_spectator_equation 4 hV hB
    k (he j k) gj kjk hgj hkjk hPW hgjD
  let source := fun p => kjk p - fderiv ℝ B p (tDir k) • W j p
  let F : ℝ := ∫ p in K2, ‖e j k p‖ ^ 2
  let M : ℝ := ∫ p in K2, ‖source p - B p • e j k p‖ ^ 2
  have hF : F ≤ D1 * (1 + b0 ^ 2 + b1 ^ 2) ^ 2 * H := by
    calc
      _ ≤ ‖e j k‖ ^ 2 := lp_integral_norm_sq_le K2 (e j k)
      _ ≤ ∑ l, ‖e j l‖ ^ 2 := Finset.single_le_sum (fun l _ => sq_nonneg ‖e j l‖) (Finset.mem_univ k)
      _ ≤ _ := hT1 j
  have hM : M ≤ 4 * b0 ^ 2 * F + 8 * b1 ^ 2 * (L * (1 + b0 ^ 2) * H) +
      4 * b2 ^ 2 * (∫ p in K2, ‖U p‖ ^ 2) := by
    have hforce := second_spectator_forcing_integral_le hV hK2 hK2V hB U (d k) (W j) (e j k) j k hb0 hb1 hb2
      (fun p hp => nuclearKSPotential_norm_le_of_mem_nuclearChartOpen Z E t0 ht0 (hVO (hK2V hp)))
      (fun p hp => by simpa only [Real.norm_eq_abs] using
        nuclearKSPotential_spectator_abs_le_of_mem_nuclearChartOpen Z E t0 ht0 (hVO (hK2V hp)) j)
      (fun p hp => by simpa only [Real.norm_eq_abs] using
        nuclearKSPotential_spectator_abs_le_of_mem_nuclearChartOpen Z E t0 ht0 (hVO (hK2V hp)) k)
      (fun p hp => by simpa only [Real.norm_eq_abs] using
        nuclearKSPotential_second_spectator_abs_le_of_mem_nuclearChartOpen Z E t0 ht0 (hVO (hK2V hp)) j k)
    change M ≤ 4 * b1 ^ 2 * (∫ p in K2, ‖d k p‖ ^ 2) +
      4 * b2 ^ 2 * (∫ p in K2, ‖U p‖ ^ 2) +
      4 * b1 ^ 2 * (∫ p in K2, ‖W j p‖ ^ 2) + 4 * b0 ^ 2 * F at hforce
    calc
      _ ≤ _ := hforce
      _ ≤ 4 * b1 ^ 2 * (L * (1 + b0 ^ 2) * H) +
          4 * b2 ^ 2 * (∫ p in K2, ‖U p‖ ^ 2) +
          4 * b1 ^ 2 * (L * (1 + b0 ^ 2) * H) + 4 * b0 ^ 2 * F := by
        gcongr
        · exact hdLocal k
        · exact hWLocal j
      _ = _ := by ring
  have hab := second_spectator_budget_absorb hC2 hD1 hL hQ hH hF (le_refl (L * (1 + b0 ^ 2) * H)) hA0 hM
  have heLocal : ProductLocallyL2On (e j k : NuclearKSSpace (0 : Fin 2) → ℂ) V :=
    fun _ _ _ => (Lp.memLp (e j k)).mono_measure Measure.restrict_le_self
  obtain ⟨A, gy, gt, hyy, hA, hY, hT, hYY, hgy, hgt, hhyy⟩ :=
    hgain B (e j k) source hB.continuousOn heLocal hsource hdiff
  refine ⟨A, gy, gt, hyy, hA, ?_, ?_, ?_, hgy, hgt, hhyy⟩
  · simpa only [D, H, mul_assoc] using hY.trans hab.1
  · have hT' : (∑ l, ‖gt l‖ ^ 2) ≤ (C2 * (F + M)) / 64 := by
      simpa only [show (16 : ℝ) * 4 = 64 by norm_num] using hT
    simpa only [D, H, mul_assoc] using hT'.trans hab.2.1
  · simpa only [D, H, mul_assoc] using hYY.trans hab.2.2

#print axioms two_electron_nuclear_chart_second_spectator_original_norm_budget
end ManyBody.S8
