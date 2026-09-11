import FreeResolventMultiplier_v1
import FourierConjugateL2_v1
import WeakLaplacianDistribution_v1

/-!
The actual positive free resolvent for -Delta/2 on the original weak H2 domain.
R_mu is explicitly the Fourier conjugate of 1/(2*pi^2*|xi|^2+mu).
K_mu is the Fourier conjugate of a/(a+mu), and is the free kinetic output.
These are mathematical operators on actual L2, not a numerical algorithm.
-/

noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory FourierTransform TemperedDistribution Filter
open scoped SchwartzMap Laplacian BigOperators

namespace TheoremT.Continuum

theorem spatialL2_complex_ofReal_smul (N : ℕ) (c : ℝ) (f : SpatialL2 N) :
    (c : ℂ) • f = c • f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul (c : ℂ) f, Lp.coeFn_smul c f] with x hc hr
  simp only [Pi.smul_apply] at hc hr
  rw [hc, hr, Complex.coe_smul]

def freeResolvent (N : ℕ) (μ : ℝ) (hμ : 0 < μ) :
    SpatialL2 N →L[ℂ] SpatialL2 N :=
  fourierConjugateL2 (freeResolventMultiplier N μ hμ)

def freeKineticResolvent (N : ℕ) (μ : ℝ) (hμ : 0 < μ) :
    SpatialL2 N →L[ℂ] SpatialL2 N :=
  fourierConjugateL2 (freeKineticResolventMultiplier N μ hμ)

theorem freeResolvent_fourier_ae (N : ℕ) {μ : ℝ} (hμ : 0 < μ)
    (f : SpatialL2 N) :
    𝓕 (freeResolvent N μ hμ f) =ᵐ[volume]
      fun x => freeResolventSymbol N μ x * (𝓕 f) x := by
  rw [freeResolvent, fourier_fourierConjugateL2]
  exact freeResolventMultiplier_ae N hμ (𝓕 f)

theorem freeKineticResolvent_fourier_ae (N : ℕ) {μ : ℝ} (hμ : 0 < μ)
    (f : SpatialL2 N) :
    𝓕 (freeKineticResolvent N μ hμ f) =ᵐ[volume]
      fun x => ((freeKineticSymbol N x : ℂ) * freeResolventSymbol N μ x) * (𝓕 f) x := by
  rw [freeKineticResolvent, fourier_fourierConjugateL2]
  exact freeKineticResolventMultiplier_ae N hμ (𝓕 f)

theorem norm_freeResolvent_le (N : ℕ) {μ : ℝ} (hμ : 0 < μ) :
    ‖freeResolvent N μ hμ‖ ≤ μ⁻¹ :=
  (norm_fourierConjugateL2_le _).trans (norm_freeResolventMultiplier_le N hμ)

theorem norm_freeKineticResolvent_le (N : ℕ) {μ : ℝ} (hμ : 0 < μ) :
    ‖freeKineticResolvent N μ hμ‖ ≤ 1 :=
  (norm_fourierConjugateL2_le _).trans (norm_freeKineticResolventMultiplier_le N hμ)

theorem freeResolvent_fourier_normSq_memLp (N : ℕ) {μ : ℝ} (hμ : 0 < μ)
    (f : SpatialL2 N) :
    MemLp (fun x : Configuration N => Complex.ofReal (‖x‖ ^ 2) *
      (𝓕 (freeResolvent N μ hμ f)) x) 2 volume := by
  let c : ℂ := ((2 * Real.pi ^ 2 : ℝ) : ℂ)
  have hc : c ≠ 0 := by
    dsimp [c]
    norm_cast
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ Real.pi_ne_zero)
  have hscale (x : Configuration N) :
      c⁻¹ * (freeKineticSymbol N x : ℂ) = Complex.ofReal (‖x‖ ^ 2) := by
    have ha : (freeKineticSymbol N x : ℂ) = c * Complex.ofReal (‖x‖ ^ 2) := by
      simp [freeKineticSymbol, c]
    rw [ha, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  have hp := (Lp.memLp (𝓕 (freeKineticResolvent N μ hμ f))).const_mul c⁻¹
  apply MemLp.ae_eq _ hp
  filter_upwards [freeResolvent_fourier_ae N hμ f,
    freeKineticResolvent_fourier_ae N hμ f] with x hr hk
  rw [hr, hk]
  calc
    c⁻¹ * (((freeKineticSymbol N x : ℂ) * freeResolventSymbol N μ x) * (𝓕 f) x) =
        (c⁻¹ * (freeKineticSymbol N x : ℂ)) *
          (freeResolventSymbol N μ x * (𝓕 f) x) := by ring
    _ = _ := by rw [hscale]

theorem freeResolvent_hasH2 (N : ℕ) {μ : ℝ} (hμ : 0 < μ)
    (f : SpatialL2 N) : HasH2 (freeResolvent N μ hμ f) :=
  hasH2_of_fourier_normSq_memLp _ (freeResolvent_fourier_normSq_memLp N hμ f)

theorem freeResolvent_partition_complex (N : ℕ) {μ : ℝ} (hμ : 0 < μ)
    (f : SpatialL2 N) :
    freeKineticResolvent N μ hμ f + (μ : ℂ) • freeResolvent N μ hμ f = f := by
  apply (Lp.fourierTransformₗᵢ (Configuration N) ℂ).injective
  change 𝓕 (freeKineticResolvent N μ hμ f +
      (μ : ℂ) • freeResolvent N μ hμ f) = 𝓕 f
  rw [FourierTransform.fourier_add, FourierTransform.fourier_smul]
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (𝓕 (freeKineticResolvent N μ hμ f))
      ((μ : ℂ) • 𝓕 (freeResolvent N μ hμ f)),
    Lp.coeFn_smul (μ : ℂ) (𝓕 (freeResolvent N μ hμ f)),
    freeResolvent_fourier_ae N hμ f, freeKineticResolvent_fourier_ae N hμ f]
      with x hadd hsmul hr hk
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hadd hsmul
  rw [hadd, hsmul, hr, hk]
  calc
    ((freeKineticSymbol N x : ℂ) * freeResolventSymbol N μ x) * (𝓕 f) x +
        (μ : ℂ) * (freeResolventSymbol N μ x * (𝓕 f) x) =
      ((freeKineticSymbol N x : ℂ) * freeResolventSymbol N μ x +
        (μ : ℂ) * freeResolventSymbol N μ x) * (𝓕 f) x := by ring
    _ = _ := by rw [freeResolventSymbol_partition N hμ x, one_mul]

theorem freeResolvent_partition (N : ℕ) {μ : ℝ} (hμ : 0 < μ)
    (f : SpatialL2 N) :
    freeKineticResolvent N μ hμ f + μ • freeResolvent N μ hμ f = f := by
  simpa only [spatialL2_complex_ofReal_smul] using freeResolvent_partition_complex N hμ f

theorem freeResolvent_laplacian (N : ℕ) {μ : ℝ} (hμ : 0 < μ)
    (f : SpatialL2 N) :
    Δ (freeResolvent N μ hμ f : 𝓢'(Configuration N, ℂ)) =
      (((-2 : ℝ) • freeKineticResolvent N μ hμ f : SpatialL2 N) :
        𝓢'(Configuration N, ℂ)) := by
  obtain ⟨w, hw⟩ := (freeResolvent_hasH2 N hμ f).exists_temperedDistribution_laplacian
  have hweq : w = (-2 : ℂ) • freeKineticResolvent N μ hμ f := by
    apply (Lp.fourierTransformₗᵢ (Configuration N) ℂ).injective
    change 𝓕 w = 𝓕 ((-2 : ℂ) • freeKineticResolvent N μ hμ f)
    rw [FourierTransform.fourier_smul]
    apply Lp.ext
    filter_upwards [fourier_laplacian_ae (freeResolvent N μ hμ f) w hw,
      freeResolvent_fourier_ae N hμ f, freeKineticResolvent_fourier_ae N hμ f,
      Lp.coeFn_smul (-2 : ℂ) (𝓕 (freeKineticResolvent N μ hμ f))]
        with x hwx hr hk hsmul
    simp only [Pi.smul_apply, smul_eq_mul] at hsmul
    rw [hwx, hsmul, hr, hk]
    simp only [freeKineticSymbol, Complex.ofReal_mul, Complex.ofReal_neg,
      Complex.ofReal_pow, Complex.ofReal_ofNat]
    ring
  rw [hweq] at hw
  have hreal : (-2 : ℂ) • freeKineticResolvent N μ hμ f =
      (-2 : ℝ) • freeKineticResolvent N μ hμ f := by
    simpa using spatialL2_complex_ofReal_smul N (-2 : ℝ) (freeKineticResolvent N μ hμ f)
  rw [hreal] at hw
  exact hw

theorem spatialL2_toTemperedDistribution_injective (N : ℕ) :
    Function.Injective (fun f : SpatialL2 N => (f : 𝓢'(Configuration N, ℂ))) :=
  LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
    (F := ℂ) (μ := (volume : Measure (Configuration N))) (p := 2))

theorem freeResolvent_derivative_sum (N : ℕ) {μ : ℝ} (hμ : 0 < μ)
    (f : SpatialL2 N) (d e : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial (freeResolvent N μ hμ f) (d k) k)
    (he : ∀ k, WeakPartial (d k) (e k) k) :
    (∑ k, e k) = (-2 : ℝ) • freeKineticResolvent N μ hμ f := by
  apply spatialL2_toTemperedDistribution_injective N
  exact (distribution_laplacian_eq_sum_of_weakPartial d e hd he).symm.trans
    (freeResolvent_laplacian N hμ f)

theorem freeResolvent_solve (N : ℕ) {μ : ℝ} (hμ : 0 < μ) (f : SpatialL2 N) :
    ∃ d : Coordinate N → SpatialL2 N,
    ∃ e : Coordinate N → Coordinate N → SpatialL2 N,
      (∀ k, WeakPartial (freeResolvent N μ hμ f) (d k) k) ∧
      (∀ k l, WeakPartial (d k) (e k l) l) ∧
      f = (-((1 : ℝ) / 2)) • (∑ k, e k k) + μ • freeResolvent N μ hμ f := by
  classical
  obtain ⟨d, hd, hsecond⟩ := freeResolvent_hasH2 N hμ f
  choose e he using hsecond
  refine ⟨d, e, hd, he, ?_⟩
  rw [freeResolvent_derivative_sum N hμ f d (fun k => e k k) hd (fun k => he k k),
    smul_smul]
  norm_num
  exact (freeResolvent_partition N hμ f).symm

#print axioms freeResolvent_fourier_ae
#print axioms freeKineticResolvent_fourier_ae
#print axioms norm_freeResolvent_le
#print axioms norm_freeKineticResolvent_le
#print axioms freeResolvent_hasH2
#print axioms freeResolvent_partition
#print axioms freeResolvent_laplacian
#print axioms freeResolvent_derivative_sum
#print axioms freeResolvent_solve

end TheoremT.Continuum
