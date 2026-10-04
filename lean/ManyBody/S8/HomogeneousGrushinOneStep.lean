import LocalWeakGrushinPotentialGain_v1

/-!
One-step local initialization for the existing weak Grushin operator.

A known bound on the zeroth-order coefficient removes its multiplication
norm from the right-hand side. The compact region and base constant precede
the coefficient, its bound, and the input function. Only the actual weak
equation and local L2 membership are input; no input derivative is assumed.

The output consists of first Y/T and ordered second YY weak derivatives of
the cutoff. It does not assert joint H2, H12, analyticity, or full Rung 2.
-/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin

namespace ManyBody.S8

variable {κ : Type} [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
theorem local_bounded_potential_sq_integral_le
    {Ω K : Set (Space κ)} {B : Space κ → ℝ} {f : Space κ → ℂ} {b : ℝ}
    (hB : ContinuousOn B Ω) (hf : ProductLocallyL2On f Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hb : 0 ≤ b)
    (hBb : ∀ p ∈ K, ‖B p‖ ≤ b) :
    (∫ p in K, ‖B p • f p‖ ^ 2) ≤ b ^ 2 * (∫ p in K, ‖f p‖ ^ 2) := by
  have hif := (hf K hK hKΩ).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hiB := ((product_locallyL2On_smul_of_continuousOn hB hf) K hK hKΩ).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0)
  calc
    (∫ p in K, ‖B p • f p‖ ^ 2) ≤ ∫ p in K, b ^ 2 * ‖f p‖ ^ 2 := by
      apply integral_mono_ae hiB (hif.const_mul (b ^ 2))
      filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
      rw [norm_smul, mul_pow]
      exact mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ (norm_nonneg _) hb).mpr (hBb p hp)) (sq_nonneg _)
    _ = b ^ 2 * (∫ p in K, ‖f p‖ ^ 2) := integral_const_mul _ _

theorem local_weak_grushin_homogeneous_cutoff_gain
    {c : ℝ} (hc : 0 < c) {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {χ : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ Ω) :
    ∃ K : Set (Space κ), ∃ C : ℝ,
      IsCompact K ∧ tsupport χ ⊆ K ∧ K ⊆ Ω ∧ 0 ≤ C ∧
      ∀ (b : ℝ) (B : Space κ → ℝ) (f : Space κ → ℂ),
        0 ≤ b → ContinuousOn B Ω → ProductLocallyL2On f Ω →
        (∀ p ∈ K, ‖B p‖ ≤ b) →
        (∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
          (∫ p, splitGrushin c oscillatorBasis B φ p • f p) = 0) →
        let F : ℝ := ∫ p in K, ‖f p‖ ^ 2
        ∃ U : Lp ℂ 2 (volume : Measure (Space κ)),
        ∃ gy : Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
        ∃ gt : κ → Lp ℂ 2 (volume : Measure (Space κ)),
        ∃ hyy : Fin 4 → Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
          U =ᵐ[volume] (fun p => χ p • f p) ∧
          (∑ i, ‖gy i‖ ^ 2) ≤ C * (11 / 4 + 3 / 4 * b ^ 2) * F ∧
          (∑ j, ‖gt j‖ ^ 2) ≤ (C * (1 + b ^ 2) * F) / (16 * c) ∧
          (∑ i, ∑ j, ‖hyy i j‖ ^ 2) ≤ 3 / 2 * C * (1 + b ^ 2) * F ∧
          (∀ i, WeakProductL2Directional U (gy i) (yDir i)) ∧
          (∀ j, WeakProductL2Directional U (gt j) (tDir j)) ∧
          ∀ i j, WeakProductL2Directional (gy i) (hyy i j) (yDir j) := by
  obtain ⟨K, C, hK, hχK, hKΩ, hC, hgain⟩ :=
    local_weak_grushin_potential_cutoff_gain hc hΩ hχ hcχ hχΩ
  refine ⟨K, C, hK, hχK, hKΩ, hC, ?_⟩
  intro b B f hb hB hf hBb hP
  have hzero : ProductLocallyL2On (fun _ : Space κ => (0 : ℂ)) Ω := by
    intro L hL hLΩ
    exact MemLp.zero
  have hPzero : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis B φ p • f p) = ∫ p, φ p • (0 : ℂ) := by
    intro φ hφ hcφ hsφ
    simpa only [smul_zero, integral_zero] using hP φ hφ hcφ hsφ
  obtain ⟨U, gy, gt, hyy, hU, hY, hT, hYY, hgy, hgt, hhyy⟩ :=
    hgain B f (fun _ => 0) hB hf hzero hPzero
  simp only [zero_sub, norm_neg] at hY hT hYY
  dsimp only
  have hM := local_bounded_potential_sq_integral_le hB hf hK hKΩ hb hBb
  have hCM : C * ((∫ p in K, ‖f p‖ ^ 2) + (∫ p in K, ‖B p • f p‖ ^ 2)) ≤
      C * ((∫ p in K, ‖f p‖ ^ 2) + b ^ 2 * (∫ p in K, ‖f p‖ ^ 2)) :=
    mul_le_mul_of_nonneg_left (add_le_add (le_refl _) hM) hC
  refine ⟨U, gy, gt, hyy, hU, ?_, ?_, ?_, hgy, hgt, hhyy⟩
  · calc
      _ ≤ 2 * (C * (∫ p in K, ‖f p‖ ^ 2)) +
          (3 / 4 : ℝ) * (C * ((∫ p in K, ‖f p‖ ^ 2) +
            (∫ p in K, ‖B p • f p‖ ^ 2))) := hY
      _ ≤ 2 * (C * (∫ p in K, ‖f p‖ ^ 2)) +
          (3 / 4 : ℝ) * (C * ((∫ p in K, ‖f p‖ ^ 2) +
            b ^ 2 * (∫ p in K, ‖f p‖ ^ 2))) := by
        exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hCM (by norm_num))
      _ = _ := by ring
  · calc
      _ ≤ (C * ((∫ p in K, ‖f p‖ ^ 2) +
          (∫ p in K, ‖B p • f p‖ ^ 2))) / (16 * c) := hT
      _ ≤ (C * ((∫ p in K, ‖f p‖ ^ 2) +
          b ^ 2 * (∫ p in K, ‖f p‖ ^ 2))) / (16 * c) := by
        exact div_le_div_of_nonneg_right hCM (by positivity)
      _ = _ := by ring
  · calc
      _ ≤ (3 / 2 : ℝ) * (C * ((∫ p in K, ‖f p‖ ^ 2) +
          (∫ p in K, ‖B p • f p‖ ^ 2))) := hYY
      _ ≤ (3 / 2 : ℝ) * (C * ((∫ p in K, ‖f p‖ ^ 2) +
          b ^ 2 * (∫ p in K, ‖f p‖ ^ 2))) := by
        exact mul_le_mul_of_nonneg_left hCM (by norm_num)
      _ = _ := by ring

#print axioms local_bounded_potential_sq_integral_le
#print axioms local_weak_grushin_homogeneous_cutoff_gain

end ManyBody.S8
