import KSScaledLocalWeakKernel_v1

/-! Subtracting a constant from an actual weak kernel and dividing by epsilon
produces the exact affine forcing. Smoothness of the coefficient is local to
the compact test support. No derivative of the weak input is assumed. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum

theorem ksScaledPrincipal_const {N : ℕ} (i : Fin N) (c : ℝ) (a : ℂ)
    (q : NuclearKSSpace i) : ksScaledPrincipal i c (fun _ => a) q = 0 := by
  simp [ksScaledPrincipal]

theorem ks_scaled_constant_weak_pairing {N : ℕ} (i : Fin N) (c : ℝ) (a : ℂ)
    {φ B : NuclearKSSpace i → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hB : ∀ q ∈ tsupport φ, ContDiffAt ℝ ∞ B q) :
    Integrable (fun q => (splitGrushin c spectatorBasis B φ q : ℂ) * a) volume ∧
    Integrable (fun q => φ q • (B q • a)) volume ∧
    (∫ q, (splitGrushin c spectatorBasis B φ q : ℂ) * a) =
      ∫ q, φ q • (B q • a) := by
  have hp := ks_scaled_principal_integration_by_parts i c hφ hc
    (u := fun _ => a) (fun _ _ => contDiffAt_const)
  have ht : Integrable (fun q => φ q • (B q • a)) volume :=
    local_smooth_test_smul_integrable (μ := volume) hφ hc
    (fun q hq => (hB q hq).smul (contDiffAt_const (c := a)))
  have hz : (∫ q, ksScaledRealPrincipal i c φ q • a) = 0 := by
    rw [hp.2.2]
    simp only [ksScaledPrincipal_const, smul_zero, integral_zero]
  have he : (fun q => (splitGrushin c spectatorBasis B φ q : ℂ) * a) =
      fun q => -(ksScaledRealPrincipal i c φ q • a) + φ q • (B q • a) := by
    funext q
    simp only [splitGrushin, ksScaledRealPrincipal, Complex.real_smul,
      Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_mul]
    ring
  rw [he]
  refine ⟨hp.1.neg.add ht, ht, ?_⟩
  have hn : Integrable (fun q => -(ksScaledRealPrincipal i c φ q • a)) volume := hp.1.neg
  rw [integral_add hn ht, integral_neg, hz, neg_zero, zero_add]

theorem ks_scaled_affine_weak_forcing {N : ℕ} (i : Fin N) (c ε : ℝ) (a : ℂ)
    {φ b : NuclearKSSpace i → ℝ} {u : NuclearKSSpace i → ℂ}
    (hε : ε ≠ 0) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hb : ∀ q ∈ tsupport φ, ContDiffAt ℝ ∞ b q)
    (hu : Integrable
      (fun q => (splitGrushin c spectatorBasis (fun q => ε * b q) φ q : ℂ) * u q) volume)
    (hweak : (∫ q, (splitGrushin c spectatorBasis (fun q => ε * b q) φ q : ℂ) * u q) = 0) :
    Integrable (fun q =>
      (splitGrushin c spectatorBasis (fun q => ε * b q) φ q : ℂ) *
        (ε⁻¹ • (u q - a))) volume ∧
    Integrable (fun q => φ q • (-(b q • a))) volume ∧
    (∫ q, (splitGrushin c spectatorBasis (fun q => ε * b q) φ q : ℂ) *
      (ε⁻¹ • (u q - a))) = ∫ q, φ q • (-(b q • a)) := by
  have ha := ks_scaled_constant_weak_pairing i c a (B := fun q => ε * b q) hφ hc
    (fun q hq => contDiffAt_const.mul (hb q hq))
  have ht : Integrable (fun q => φ q • (b q • a)) volume :=
    local_smooth_test_smul_integrable (μ := volume) hφ hc
    (fun q hq => (hb q hq).smul (contDiffAt_const (c := a)))
  have hv : (fun q =>
      (splitGrushin c spectatorBasis (fun q => ε * b q) φ q : ℂ) *
        (ε⁻¹ • (u q - a))) = fun q => ε⁻¹ •
      ((splitGrushin c spectatorBasis (fun q => ε * b q) φ q : ℂ) * u q -
        (splitGrushin c spectatorBasis (fun q => ε * b q) φ q : ℂ) * a) := by
    funext q
    simp only [Complex.real_smul]
    ring
  have hs : (fun q => φ q • (-(b q • a))) = fun q => -(φ q • (b q • a)) := by
    funext q
    exact smul_neg _ _
  have he : (fun q => φ q • ((ε * b q) • a)) =
      fun q => ε • (φ q • (b q • a)) := by
    funext q
    rw [mul_smul, smul_comm (φ q) ε]
  rw [hv, hs]
  refine ⟨(hu.sub ha.1).smul ε⁻¹, ht.neg, ?_⟩
  rw [integral_smul, integral_sub hu ha.1, hweak, ha.2.2, he,
    integral_smul, integral_neg]
  simp [smul_smul, hε]

end TheoremT.Continuum
