import ManyBody.S8.Internal.RealRationalAmbientProfile
import Mathlib.Analysis.Calculus.ContDiff.Bounds
/-! Actual real coordinate-product derivative bounds through order two.

The product estimate uses the genuine binomial derivative formula on a local
open neighborhood. No product derivative identity or higher derivative is
assumed. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology BigOperators ContDiff
namespace ManyBody.S8

theorem real_distance_coordinate_first_norm_le (j : Fin 3) (p : Fin 3 → ℝ) :
    ‖iteratedFDeriv ℝ 1 (fun q : Fin 3 → ℝ => q j) p‖≤1 := by
  rw [norm_iteratedFDeriv_one]
  change ‖fderiv ℝ (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ) p‖≤1
  rw [ContinuousLinearMap.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  simpa only [ContinuousLinearMap.proj_apply,one_mul] using norm_le_pi_norm q j

theorem real_distance_coordinate_second_zero (j : Fin 3) (p : Fin 3 → ℝ) :
    iteratedFDeriv ℝ 2 (fun q : Fin 3 → ℝ => q j) p=0 := by
  have hconst : iteratedFDeriv ℝ 1 (fun q : Fin 3 → ℝ => q j)=
      fun _ => iteratedFDeriv ℝ 1 (fun q : Fin 3 → ℝ => q j) 0 := by
    funext q
    ext v
    simp only [iteratedFDeriv_one_apply]
    change (fderiv ℝ (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ) q) (v 0)=
      (fderiv ℝ (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ) 0) (v 0)
    rw [ContinuousLinearMap.fderiv,ContinuousLinearMap.fderiv]
  apply norm_eq_zero.mp
  rw [←norm_fderiv_iteratedFDeriv (n:=1),hconst]
  rw [fderiv_const_apply]
  change ‖(0 : (Fin 3 → ℝ) →L[ℝ] ((Fin 3 → ℝ) [×1]→L[ℝ] ℝ))‖=0
  exact norm_zero (E := (Fin 3 → ℝ) →L[ℝ] ((Fin 3 → ℝ) [×1]→L[ℝ] ℝ))

theorem real_distance_coordinate_jet_norm_le (j : Fin 3) (p : Fin 3 → ℝ) (i : ℕ) (hi : i≤2) :
    ‖iteratedFDeriv ℝ i (fun q : Fin 3 → ℝ => q j) p‖≤1+|p j| := by
  interval_cases i
  · rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs]; linarith
  · exact (real_distance_coordinate_first_norm_le j p).trans (by linarith [abs_nonneg (p j)])
  · rw [real_distance_coordinate_second_zero,norm_zero]; positivity

theorem real_coordinate_product_C2_bound {V : (Fin 3 → ℝ) → ℝ}
    (j : Fin 3) {p : Fin 3 → ℝ} {η : ℝ} (hη : 0≤η)
    (hV : ContDiffAt ℝ 2 V p)
    (hbound : ∀ i : ℕ, i≤2 → ‖iteratedFDeriv ℝ i V p‖≤η) (k : Fin 3) :
    ‖iteratedFDeriv ℝ (k:ℕ) (fun q : Fin 3 → ℝ => q j*V q) p‖≤
      4*(1+|p j|)*η := by
  obtain ⟨u,hu,hVu⟩ := hV.contDiffOn le_rfl (by norm_num)
  obtain ⟨s,hsu,hs,hps⟩ := _root_.mem_nhds_iff.mp hu
  have hVs := hVu.mono hsu
  have hcoord : ContDiffOn ℝ 2 (fun q : Fin 3 → ℝ => q j) s :=
    (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).contDiff.contDiffOn
  have hk : (k:ℕ)≤(2:ℕ∞ω) := by exact_mod_cast (show (k:ℕ)≤2 by omega)
  have hh := norm_iteratedFDerivWithin_mul_le hcoord hVs hs.uniqueDiffOn hps hk
  rw [iteratedFDerivWithin_of_isOpen _ hs hps] at hh
  simp_rw [iteratedFDerivWithin_of_isOpen _ hs hps] at hh
  apply hh.trans
  have heach (i : ℕ) (hi : i∈Finset.range ((k:ℕ)+1)) :
      (((k:ℕ).choose i : ℕ):ℝ)*‖iteratedFDeriv ℝ i (fun q : Fin 3 → ℝ => q j) p‖*
        ‖iteratedFDeriv ℝ ((k:ℕ)-i) V p‖≤
      (((k:ℕ).choose i : ℕ):ℝ)*(1+|p j|)*η := by
    have hi2 : i≤2 := by have := Finset.mem_range.mp hi; have := k.isLt; omega
    have hki : (k:ℕ)-i≤2 := by have := k.isLt; omega
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (real_distance_coordinate_jet_norm_le j p i hi2) (by positivity))
      (hbound _ hki) (norm_nonneg _) (by positivity)
  have hsum := Finset.sum_le_sum heach
  apply hsum.trans
  fin_cases k <;> norm_num [Finset.sum_range_succ] <;>
    nlinarith [abs_nonneg (p j),mul_nonneg (abs_nonneg (p j)) hη]

#print axioms real_distance_coordinate_second_zero
#print axioms real_coordinate_product_C2_bound
end ManyBody.S8
