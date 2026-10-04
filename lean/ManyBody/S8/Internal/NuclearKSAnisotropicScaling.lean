import NuclearKSPotential_v1
import CoulombDilation_v1
import ManyBody.S8.Internal.NuclearChartScaling
import ManyBody.S8.Internal.NuclearChartDerivativeBounds

/-! Exact anisotropic rescaling of the actual physical nuclear KS potential.
Scaling the four KS variables by sqrt(r) and all spectator variables by r
scales the original physical configuration by r. The charge is unchanged and
the coefficient energy becomes r*E, including on the selected collision fiber.
This identity does not assert a uniform derivative-gain constant.
-/
noncomputable section
open scoped BigOperators
open TheoremT.Continuum

namespace ManyBody.S8

def nuclearKSAnisotropicScale {N : ℕ} (i : Fin N) (r : ℝ)
    (q : NuclearKSSpace i) : NuclearKSSpace i :=
  (Real.sqrt r • q.1, r • q.2)

theorem ksMap_real_smul (a : ℝ) (y : KSSpace) :
    ksMap (a • y) = a ^ 2 • ksMap y := by
  apply (WithLp.ext_iff 2).mpr
  funext k
  fin_cases k <;> simp [ksMap] <;> ring

theorem nuclearKSLift_anisotropicScale {N : ℕ} (i : Fin N) {r : ℝ}
    (hr : 0 ≤ r) (q : NuclearKSSpace i) :
    nuclearKSLift i (nuclearKSAnisotropicScale i r q) = r • nuclearKSLift i q := by
  unfold nuclearKSLift nuclearKSAnisotropicScale
  rw [ksMap_real_smul, Real.sq_sqrt hr]
  exact (configurationProductEquiv i).symm.map_smul r (ksMap q.1, q.2)

theorem coulombWithoutSelectedNucleus_real_smul {N : ℕ} (i : Fin N) (Z : ℝ)
    {r : ℝ} (hr : 0 < r) (x : Configuration N) :
    coulombWithoutSelectedNucleus i Z (r • x) = r⁻¹ * coulombWithoutSelectedNucleus i Z x := by
  have hn (j : Fin N) : ‖position (r • x) j‖⁻¹ = r⁻¹ * ‖position x j‖⁻¹ := by
    rw [position_real_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_inv_rev]
    ring
  have hp (j k : Fin N) :
      ‖position (r • x) j - position (r • x) k‖⁻¹ =
        r⁻¹ * ‖position x j - position x k‖⁻¹ := by
    rw [position_real_smul, position_real_smul, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_pos hr, mul_inv_rev]
    ring
  simp only [coulombWithoutSelectedNucleus, hn, hp]
  simp_rw [← Finset.mul_sum]
  ring

theorem nuclearKSPotential_anisotropicScale {N : ℕ} (i : Fin N) (Z E : ℝ)
    {r : ℝ} (hr : 0 < r) (q : NuclearKSSpace i) :
    nuclearKSPotential i Z E (nuclearKSAnisotropicScale i r q) =
      nuclearKSPotential i Z (r * E) q := by
  unfold nuclearKSPotential
  rw [nuclearKSLift_anisotropicScale i hr.le,
    coulombWithoutSelectedNucleus_real_smul i Z hr]
  change -8 * Z + 8 * ‖Real.sqrt r • q.1‖ ^ 2 *
    (r⁻¹ * coulombWithoutSelectedNucleus i Z (nuclearKSLift i q) - E) = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg r),
    mul_pow, Real.sq_sqrt hr.le]
  field_simp [hr.ne']

theorem nuclearKSCoefficientPatch_anisotropicScale_iff {N : ℕ} (i : Fin N)
    {r : ℝ} (hr : 0 < r) (q : NuclearKSSpace i) :
    nuclearKSAnisotropicScale i r q ∈ nuclearKSCoefficientPatch i ↔
      q ∈ nuclearKSCoefficientPatch i := by
  simp only [nuclearKSCoefficientPatch, Set.mem_ofPred_eq,
    nuclearKSLift_anisotropicScale i hr.le, position_real_smul]
  have hinj : Function.Injective (fun v : Position => r • v) :=
    smul_right_injective _ hr.ne'
  have hz (v : Position) : r • v ≠ 0 ↔ v ≠ 0 := by
    have ht : r • v ≠ r • (0 : Position) ↔ v ≠ 0 := hinj.ne_iff
    simpa only [smul_zero] using ht
  simp only [hz, hinj.ne_iff]

/-- The actual anisotropic map as a continuous linear map, without asserting
that it is an isometry of the ordinary product norm. -/
def nuclearKSAnisotropicScaleCLM {N : ℕ} (i : Fin N) (r : ℝ) :
    NuclearKSSpace i →L[ℝ] NuclearKSSpace i :=
  (Real.sqrt r • ContinuousLinearMap.fst ℝ KSSpace (SpectatorConfiguration i)).prod
    (r • ContinuousLinearMap.snd ℝ KSSpace (SpectatorConfiguration i))

theorem nuclearKSAnisotropicScaleCLM_apply {N : ℕ} (i : Fin N) (r : ℝ)
    (q : NuclearKSSpace i) :
    nuclearKSAnisotropicScaleCLM i r q = nuclearKSAnisotropicScale i r q := rfl

theorem nuclearKSAnisotropicScaleCLM_tDir {N : ℕ} (i : Fin N) (r : ℝ)
    (j : SpectatorCoordinate i) :
    nuclearKSAnisotropicScaleCLM i r (WeakGrushin.tDir j) = r • WeakGrushin.tDir j := by
  simp [nuclearKSAnisotropicScaleCLM, WeakGrushin.tDir]

theorem nuclearKSPotential_scaled_spectator_derivative {N : ℕ} (i : Fin N) (Z E : ℝ)
    {r : ℝ} (hr : 0 < r) {q : NuclearKSSpace i}
    (hq : q ∈ nuclearKSCoefficientPatch i) (j : SpectatorCoordinate i) :
    fderiv ℝ (nuclearKSPotential i Z E) (nuclearKSAnisotropicScale i r q)
      (r • WeakGrushin.tDir j) =
    fderiv ℝ (nuclearKSPotential i Z (r * E)) q (WeakGrushin.tDir j) := by
  let S := nuclearKSAnisotropicScaleCLM i r
  have hP : DifferentiableAt ℝ (nuclearKSPotential i Z E) (S q) :=
    (nuclearKSPotential_contDiffAt i Z E
      ((nuclearKSCoefficientPatch_anisotropicScale_iff i hr q).2 hq)).differentiableAt (by simp)
  have he : nuclearKSPotential i Z E ∘ S = nuclearKSPotential i Z (r * E) := by
    funext p
    exact nuclearKSPotential_anisotropicScale i Z E hr p
  have hd := fderiv_comp q hP S.differentiableAt
  rw [he, S.fderiv] at hd
  have hv := congrArg (fun L : NuclearKSSpace i →L[ℝ] ℝ => L (WeakGrushin.tDir j)) hd
  simp only [ContinuousLinearMap.comp_apply] at hv
  rw [show S (WeakGrushin.tDir j) = r • WeakGrushin.tDir j from
    nuclearKSAnisotropicScaleCLM_tDir i r j] at hv
  simpa only [S, nuclearKSAnisotropicScaleCLM_apply] using hv.symm

theorem nuclearKSPotential_rescaled_spectator_abs_le
    (Z E : ℝ) {r : ℝ} (hr : 0 < r) (t0 : Position) (ht0 : ‖t0‖ = 1)
    {q : NuclearKSSpace (0 : Fin 2)} (hq : q ∈ nuclearChartOpen t0)
    (j : SpectatorCoordinate (0 : Fin 2)) :
    |fderiv ℝ (nuclearKSPotential (0 : Fin 2) Z E)
      (nuclearKSAnisotropicScale (0 : Fin 2) r q) (r • WeakGrushin.tDir j)| ≤
      (8 / 9 : ℝ) * |Z| + 128 / 121 := by
  rw [nuclearKSPotential_scaled_spectator_derivative (0 : Fin 2) Z E hr
    (nuclearChartOpen_subset_coefficientPatch t0 ht0 hq)]
  exact nuclearKSPotential_spectator_abs_le_of_mem_nuclearChartOpen Z (r * E) t0 ht0 hq j

theorem nuclearChartScaledOpen_anisotropicScale_iff {r : ℝ} (hr : 0 < r)
    (t0 : Position) (q : NuclearKSSpace (0 : Fin 2)) :
    nuclearKSAnisotropicScale (0 : Fin 2) r q ∈ nuclearChartScaledOpen r (r • t0) ↔
      q ∈ nuclearChartOpen t0 := by
  change ‖Real.sqrt r • q.1‖ ^ 2 < r / 16 ∧
    ‖position (nuclearKSLift (0 : Fin 2) (nuclearKSAnisotropicScale (0 : Fin 2) r q)) 1 -
      r • t0‖ < r / 4 ↔ _
  rw [nuclearKSLift_anisotropicScale (0 : Fin 2) hr.le, position_real_smul, ← smul_sub]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    abs_of_nonneg (Real.sqrt_nonneg r), mul_pow, Real.sq_sqrt hr.le]
  rw [show r / 16 = r * (1 / 16) by ring, show r / 4 = r * (1 / 4) by ring,
    mul_lt_mul_iff_right₀ hr, mul_lt_mul_iff_right₀ hr]
  have hy : ‖q.1‖ ^ 2 < (1 / 16 : ℝ) ↔ ‖q.1‖ < 1 / 4 := by
    constructor <;> intro h <;> nlinarith [norm_nonneg q.1]
  exact and_congr_left (fun _ => hy)

theorem nuclearKSPotential_rescaled_norm_le
    (Z E : ℝ) {r : ℝ} (hr : 0 < r) (t0 : Position) (ht0 : ‖t0‖ = 1)
    {q : NuclearKSSpace (0 : Fin 2)} (hq : q ∈ nuclearChartOpen t0) :
    ‖nuclearKSPotential (0 : Fin 2) Z E
      (nuclearKSAnisotropicScale (0 : Fin 2) r q)‖ ≤
      (26 / 3 : ℝ) * |Z| + 8 / 11 + r * |E| / 2 := by
  rw [nuclearKSPotential_anisotropicScale (0 : Fin 2) Z E hr]
  simpa only [abs_mul, abs_of_pos hr] using
    nuclearKSPotential_norm_le_of_mem_nuclearChartOpen Z (r * E) t0 ht0 hq

#print axioms nuclearChartScaledOpen_anisotropicScale_iff
#print axioms nuclearKSPotential_rescaled_norm_le

#print axioms nuclearKSCoefficientPatch_anisotropicScale_iff
#print axioms nuclearKSPotential_scaled_spectator_derivative
#print axioms nuclearKSPotential_rescaled_spectator_abs_le

#print axioms ksMap_real_smul
#print axioms nuclearKSLift_anisotropicScale
#print axioms coulombWithoutSelectedNucleus_real_smul
#print axioms nuclearKSPotential_anisotropicScale
end ManyBody.S8
