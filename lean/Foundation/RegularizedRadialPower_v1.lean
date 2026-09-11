import RegularizedConfigurationRadius_v1
import SmoothRealDerivativeSums_v1
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Smooth powers of the true squared configuration radius plus positive delta.
These are the regularized Newton potentials, not softened Hamiltonians. -/
noncomputable section
open scoped ContDiff BigOperators
namespace TheoremT.Continuum

def regularizedRadialPower (N : ℕ) (δ β : ℝ) (x : Configuration N) : ℝ := (‖x‖^2+δ)^β

theorem regularizedRadialPower_contDiff (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (β : ℝ) :
    ContDiff ℝ ∞ (regularizedRadialPower N δ β) :=
  ((contDiff_norm_sq ℝ).add contDiff_const).rpow_const_of_ne (fun x => by positivity)

theorem regularizedRadialPower_partial {N : ℕ} {δ : ℝ} (hδ : 0 < δ) (β : ℝ)
    (x : Configuration N) (k : Coordinate N) :
    fderiv ℝ (regularizedRadialPower N δ β) x (coordinateVector k) =
      2*β*(‖x‖^2+δ)^(β-1)*x k := by
  have hh := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const δ).rpow_const
    (p := β) (Or.inl (by positivity : ‖x‖^2+δ ≠ 0))
  change HasFDerivAt (regularizedRadialPower N δ β) _ x at hh
  rw [hh.fderiv]
  have hi : inner ℝ x (coordinateVector k)=x k := by
    simp [coordinateVector,EuclideanSpace.inner_single_right]
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,
    innerSL_apply_apply,smul_eq_mul,two_smul]
  rw [hi]
  ring

theorem regularizedRadialPower_mixed {N : ℕ} {δ : ℝ} (hδ : 0 < δ) (β : ℝ)
    (x : Configuration N) (k l : Coordinate N) :
    fderiv ℝ (fun y => fderiv ℝ (regularizedRadialPower N δ β) y (coordinateVector k)) x
      (coordinateVector l) = 2*β*(‖x‖^2+δ)^(β-1)*(coordinateVector l k)+
        4*β*(β-1)*(‖x‖^2+δ)^(β-2)*(x k*x l) := by
  have hf : (fun y => fderiv ℝ (regularizedRadialPower N δ β) y (coordinateVector k)) =
      (fun y => 2*β*regularizedRadialPower N δ (β-1) y*y k) := by
    funext y; exact regularizedRadialPower_partial hδ β y k
  rw [hf]
  have hr := ((regularizedRadialPower_contDiff N hδ (β-1)).differentiable (by simp) x).hasFDerivAt
  have hk := (EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt (x := x)
  have hh := (hr.const_mul (2*β)).mul hk
  change HasFDerivAt (fun y => 2*β*regularizedRadialPower N δ (β-1) y*y k) _ x at hh
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
    EuclideanSpace.coe_proj,regularizedRadialPower_partial hδ,regularizedRadialPower]
  rw [show β-1-1=β-2 by ring]
  ring

theorem regularizedRadialPower_laplacian {N : ℕ} {δ : ℝ} (hδ : 0 < δ) (β : ℝ)
    (x : Configuration N) :
    (∑ k : Coordinate N, fderiv ℝ
      (fun y => fderiv ℝ (regularizedRadialPower N δ β) y (coordinateVector k)) x (coordinateVector k)) =
      2*β*(3*N:ℝ)*(‖x‖^2+δ)^(β-1)+4*β*(β-1)*(‖x‖^2+δ)^(β-2)*‖x‖^2 := by
  simp_rw [regularizedRadialPower_mixed hδ β]
  simp only [coordinateVector,PiLp.single_apply,ite_true,mul_one,
    Finset.sum_add_distrib,Finset.sum_const,← Finset.mul_sum,← sq]
  rw [← EuclideanSpace.real_norm_sq_eq]
  simp only [Finset.card_univ,Coordinate,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
  ring

#print axioms regularizedRadialPower_laplacian
end TheoremT.Continuum
