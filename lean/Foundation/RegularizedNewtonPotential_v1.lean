import RegularizedRadialPower_v1
import LocalWeakLaplacian_v1
import AtomicSobolevExponent_v1

/-! Smooth Newton potentials with their exact positive Laplacians. The
normalization by surface area is not yet applied in this module. -/
noncomputable section
open scoped BigOperators ContDiff
namespace TheoremT.Continuum

def regularizedNewtonPotential (N : ℕ) (δ : ℝ) (x : Configuration N) : ℝ :=
  (2-(3*N:ℝ))⁻¹*regularizedRadialPower N δ ((2-(3*N:ℝ))/2) x

theorem regularizedNewtonPotential_contDiff (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ ∞ (regularizedNewtonPotential N δ) :=
  contDiff_const.mul (regularizedRadialPower_contDiff N hδ _)

theorem regularizedNewtonPotential_partial {N : ℕ} (hN : 0 < N)
    {δ : ℝ} (hδ : 0 < δ) (x : Configuration N) (k : Coordinate N) :
    fderiv ℝ (regularizedNewtonPotential N δ) x (coordinateVector k) =
      (‖x‖^2+δ)^(-(3*N:ℝ)/2)*x k := by
  have hd : 2-(3*N:ℝ) ≠ 0 := by
    have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
    linarith
  rw [show regularizedNewtonPotential N δ =
    (fun y => (2-(3*N:ℝ))⁻¹*regularizedRadialPower N δ ((2-(3*N:ℝ))/2) y) from rfl,
    real_fderiv_const_mul_apply (regularizedRadialPower_contDiff N hδ _) _ x (coordinateVector k),
    regularizedRadialPower_partial hδ]
  rw [show (2-(3*N:ℝ))/2-1= -(3*N:ℝ)/2 by ring]
  field_simp
  <;> ring

theorem regularizedNewtonPotential_laplacian {N : ℕ} (hN : 0 < N)
    {δ : ℝ} (hδ : 0 < δ) (x : Configuration N) :
    realTestLaplacian (regularizedNewtonPotential N δ) x =
      (3*N:ℝ)*δ*(‖x‖^2+δ)^(-((3*N:ℝ)+2)/2) := by
  have hd : 2-(3*N:ℝ) ≠ 0 := by
    have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
    linarith
  change (∑ k : Coordinate N, fderiv ℝ (fun y => fderiv ℝ
    (fun z => (2-(3*N:ℝ))⁻¹*regularizedRadialPower N δ ((2-(3*N:ℝ))/2) z)
      y (coordinateVector k)) x (coordinateVector k)) = _
  simp_rw [real_mixed_const_mul_apply (regularizedRadialPower_contDiff N hδ _)]
  rw [← Finset.mul_sum,regularizedRadialPower_laplacian hδ]
  have hs : 0 < ‖x‖^2+δ := by positivity
  have hr : (‖x‖^2+δ)^((2-(3*N:ℝ))/2-1) =
      (‖x‖^2+δ)^(-((3*N:ℝ)+2)/2)*(‖x‖^2+δ) := by
    calc
      _ = (‖x‖^2+δ)^(-((3*N:ℝ)+2)/2+1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hs,Real.rpow_one]
  rw [hr,show (2-(3*N:ℝ))/2-2= -((3*N:ℝ)+2)/2 by ring]
  field_simp
  <;> ring

#print axioms regularizedNewtonPotential_laplacian
end TheoremT.Continuum
