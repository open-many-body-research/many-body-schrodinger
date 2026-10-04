import ManyBody.S8.Internal.NuclearKSAnisotropicScaling
import SecondDirectionalLinearAt_v1
import GrushinHoleCommutator_v1

/-! Exact pointwise rescaling of the actual split Grushin test operator.
The rescaled potential includes the required factor r. This is a smooth-test
operator identity; weak integral transport is a separate statement.
-/
noncomputable section
open scoped ContDiff BigOperators
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin

namespace ManyBody.S8

theorem second_directional_scaled_vectors {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    {φ : A → ℝ} (hφ : ContDiff ℝ ∞ φ) (p v w : A) (a b : ℝ) :
    fderiv ℝ (fun x => fderiv ℝ φ x (a • v)) p (b • w) =
      a * b * fderiv ℝ (fun x => fderiv ℝ φ x v) p w := by
  have h2 : ContDiffAt ℝ 2 φ p := hφ.contDiffAt.of_le (by simp)
  rw [second_directional_fderiv_evaluation_at p (a • v) (b • w) h2,
    second_directional_fderiv_evaluation_at p v w h2]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

theorem nuclearKSAnisotropicScaleCLM_yDir {N : ℕ} (i : Fin N) (r : ℝ)
    (j : Fin 4) :
    nuclearKSAnisotropicScaleCLM i r (ksBasis j, 0) = Real.sqrt r • (ksBasis j, 0) := by
  simp [nuclearKSAnisotropicScaleCLM]

theorem nuclearKSAnisotropicScale_second_y {N : ℕ} (i : Fin N) {r : ℝ}
    (hr : 0 < r) {φ : NuclearKSSpace i → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (q : NuclearKSSpace i) (j : Fin 4) :
    fderiv ℝ (fun x => fderiv ℝ (φ ∘ nuclearKSAnisotropicScaleCLM i r) x (ksBasis j, 0))
      q (ksBasis j, 0) = r *
    fderiv ℝ (fun x => fderiv ℝ φ x (ksBasis j, 0))
      (nuclearKSAnisotropicScale i r q) (ksBasis j, 0) := by
  rw [second_directional_linear_at (nuclearKSAnisotropicScaleCLM i r) q _ _
    (hφ.contDiffAt.of_le (by simp)), nuclearKSAnisotropicScaleCLM_yDir,
    second_directional_scaled_vectors hφ, nuclearKSAnisotropicScaleCLM_apply]
  rw [← pow_two, Real.sq_sqrt hr.le]

theorem nuclearKSAnisotropicScale_second_t {N : ℕ} (i : Fin N) (r : ℝ)
    {φ : NuclearKSSpace i → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (q : NuclearKSSpace i) (j : SpectatorCoordinate i) :
    fderiv ℝ (fun x => fderiv ℝ (φ ∘ nuclearKSAnisotropicScaleCLM i r) x (tDir j))
      q (tDir j) = r ^ 2 *
    fderiv ℝ (fun x => fderiv ℝ φ x (tDir j))
      (nuclearKSAnisotropicScale i r q) (tDir j) := by
  rw [second_directional_linear_at (nuclearKSAnisotropicScaleCLM i r) q _ _
    (hφ.contDiffAt.of_le (by simp)), nuclearKSAnisotropicScaleCLM_tDir,
    second_directional_scaled_vectors hφ, nuclearKSAnisotropicScaleCLM_apply]
  rw [← pow_two]

theorem splitGrushin_nuclear_anisotropicScale {N : ℕ} (i : Fin N) {r : ℝ}
    (hr : 0 < r) (c : ℝ) (B : NuclearKSSpace i → ℝ)
    {φ : NuclearKSSpace i → ℝ} (hφ : ContDiff ℝ ∞ φ) (q : NuclearKSSpace i) :
    splitGrushin c oscillatorBasis
      (fun p => r * B (nuclearKSAnisotropicScale i r p))
      (φ ∘ nuclearKSAnisotropicScaleCLM i r) q =
    r * splitGrushin c oscillatorBasis B φ (nuclearKSAnisotropicScale i r q) := by
  unfold splitGrushin
  change -(∑ j : Fin 4, fderiv ℝ
      (fun x => fderiv ℝ (φ ∘ nuclearKSAnisotropicScaleCLM i r) x (ksBasis j,0))
      q (ksBasis j,0)) - c * ‖q.1‖ ^ 2 *
      (∑ j : SpectatorCoordinate i, fderiv ℝ
        (fun x => fderiv ℝ (φ ∘ nuclearKSAnisotropicScaleCLM i r) x (tDir j))
        q (tDir j)) + _ = _
  simp_rw [nuclearKSAnisotropicScale_second_y i hr hφ,
    nuclearKSAnisotropicScale_second_t i r hφ, ← Finset.mul_sum]
  change -(r * _) - c * ‖q.1‖ ^ 2 * (r ^ 2 * _) +
      (r * B (nuclearKSAnisotropicScale i r q)) * φ (nuclearKSAnisotropicScale i r q) =
    r * (-_ - c * ‖Real.sqrt r • q.1‖ ^ 2 * _ +
      B (nuclearKSAnisotropicScale i r q) * φ (nuclearKSAnisotropicScale i r q))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg r),
    mul_pow, Real.sq_sqrt hr.le]
  simp only [tDir]
  ring

theorem splitGrushin_physical_nuclear_anisotropicScale {N : ℕ} (i : Fin N)
    (Z E : ℝ) {r : ℝ} (hr : 0 < r)
    {φ : NuclearKSSpace i → ℝ} (hφ : ContDiff ℝ ∞ φ) (q : NuclearKSSpace i) :
    splitGrushin 4 oscillatorBasis (fun p => r * nuclearKSPotential i Z (r * E) p)
      (φ ∘ nuclearKSAnisotropicScaleCLM i r) q =
    r * splitGrushin 4 oscillatorBasis (nuclearKSPotential i Z E)
      φ (nuclearKSAnisotropicScale i r q) := by
  have he : (fun p => r * nuclearKSPotential i Z (r * E) p) =
      (fun p => r * nuclearKSPotential i Z E (nuclearKSAnisotropicScale i r p)) := by
    funext p
    rw [nuclearKSPotential_anisotropicScale i Z E hr]
  rw [he]
  exact splitGrushin_nuclear_anisotropicScale i hr 4 _ hφ q

#print axioms second_directional_scaled_vectors
#print axioms nuclearKSAnisotropicScale_second_y
#print axioms nuclearKSAnisotropicScale_second_t
#print axioms splitGrushin_nuclear_anisotropicScale
#print axioms splitGrushin_physical_nuclear_anisotropicScale
end ManyBody.S8
