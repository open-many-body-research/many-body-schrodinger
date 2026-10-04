import ManyBody.S8.Internal.PhysicalDistanceCompositionGeometry
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic
/-! Actual first and second Fréchet chain rules for the physical three-distance map. The derivative formulas are proved off the collision set; collision extension is handled by separate weak-closure arguments. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set Metric
open scoped Topology ContDiff BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

theorem actual_composition_mixed_fderiv
    {d : Configuration 2 → (Fin 3 → ℝ)} {g : (Fin 3 → ℝ) → ℂ}
    {x : Configuration 2} (hd : ContDiffAt ℝ 2 d x) (hg : ContDiffAt ℝ 2 g (d x))
    (v w : Configuration 2) :
    fderiv ℝ (fun y => fderiv ℝ (g∘d) y v) x w=
      fderiv ℝ (fderiv ℝ g) (d x) (fderiv ℝ d x w) (fderiv ℝ d x v)+
      fderiv ℝ g (d x) (fderiv ℝ (fun y => fderiv ℝ d y v) x w) := by
  have heq : (fun y => fderiv ℝ (g∘d) y v)=ᶠ[𝓝 x]
      (fun y => fderiv ℝ g (d y) (fderiv ℝ d y v)) := by
    have hgd : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 g (d y) :=
      hd.continuousAt.eventually (hg.eventually (by norm_num))
    filter_upwards [hgd,hd.eventually (by norm_num)] with y hy hz
    rw [fderiv_comp y (hy.differentiableAt (by norm_num))
      (hz.differentiableAt (by norm_num)),ContinuousLinearMap.comp_apply]
  rw [heq.fderiv_eq]
  have hdd := (hd.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have hgg := (hg.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have hc := hgg.comp x (hd.differentiableAt (by norm_num))
  have hu := hdd.clm_apply (differentiableAt_const v)
  change DifferentiableAt ℝ (fun y => fderiv ℝ d y v) x at hu
  change DifferentiableAt ℝ (fun y => fderiv ℝ g (d y)) x at hc
  rw [fderiv_clm_apply hc hu]
  have hec := fderiv_comp x hgg (hd.differentiableAt (by norm_num))
  change fderiv ℝ (fun y => fderiv ℝ g (d y)) x=_ at hec
  rw [hec]
  simp only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply]
  abel

def physicalDistanceCompositionFirst (g : (Fin 3 → ℝ) → ℂ)
    (x v : Configuration 2) : ℂ :=
  fderiv ℝ g (physicalDistanceTriple x) (physicalDistanceGradient x v)

def physicalDistanceCompositionSecond (g : (Fin 3 → ℝ) → ℂ)
    (x v w : Configuration 2) : ℂ :=
  fderiv ℝ (fderiv ℝ g) (physicalDistanceTriple x)
      (physicalDistanceGradient x w) (physicalDistanceGradient x v)+
    fderiv ℝ g (physicalDistanceTriple x) (physicalDistanceHessian x v w)

theorem physical_distance_composition_first {g : (Fin 3 → ℝ) → ℂ}
    {x : Configuration 2} (hx : collisionFree x)
    (hg : DifferentiableAt ℝ g (physicalDistanceTriple x)) (v : Configuration 2) :
    fderiv ℝ (g∘physicalDistanceTriple) x v=physicalDistanceCompositionFirst g x v := by
  rw [fderiv_comp x hg (physical_distance_triple_hasFDerivAt hx).differentiableAt,
    ContinuousLinearMap.comp_apply,physical_distance_triple_fderiv hx]
  rfl

theorem physical_distance_composition_second {g : (Fin 3 → ℝ) → ℂ}
    {x : Configuration 2} (hx : collisionFree x)
    (hg : ContDiffAt ℝ 2 g (physicalDistanceTriple x)) (v w : Configuration 2) :
    fderiv ℝ (fun y => fderiv ℝ (g∘physicalDistanceTriple) y v) x w=
      physicalDistanceCompositionSecond g x v w := by
  rw [actual_composition_mixed_fderiv ((physical_distance_triple_contDiffAt hx).of_le (by simp)) hg,
    physical_distance_triple_fderiv hx,physical_distance_triple_fderiv hx,
    physical_distance_triple_mixed_fderiv hx]
  rfl

theorem physical_distance_composition_first_norm_le (g : (Fin 3 → ℝ) → ℂ)
    (x v : Configuration 2) :
    ‖physicalDistanceCompositionFirst g x v‖≤
      2*‖iteratedFDeriv ℝ 1 g (physicalDistanceTriple x)‖*‖v‖ := by
  rw [norm_iteratedFDeriv_one]
  exact ((fderiv ℝ g (physicalDistanceTriple x)).le_opNorm _).trans
    (by have hh := mul_le_mul_of_nonneg_left (physical_distance_gradient_norm_le x v)
          (norm_nonneg (fderiv ℝ g (physicalDistanceTriple x)))
        nlinarith)

theorem physical_distance_composition_second_norm_le (g : (Fin 3 → ℝ) → ℂ)
    {x : Configuration 2} (hx : collisionFree x) (v w : Configuration 2) :
    ‖physicalDistanceCompositionSecond g x v w‖≤
      (4*‖iteratedFDeriv ℝ 2 g (physicalDistanceTriple x)‖+
        8*‖iteratedFDeriv ℝ 1 g (physicalDistanceTriple x)‖*physicalInverseDistanceBudget x)*‖v‖*‖w‖ := by
  have he : ‖fderiv ℝ (fderiv ℝ g) (physicalDistanceTriple x)‖=
      ‖iteratedFDeriv ℝ 2 g (physicalDistanceTriple x)‖ := by
    rw [←norm_iteratedFDeriv_one (fderiv ℝ g),norm_iteratedFDeriv_fderiv]
  have h0 : ‖physicalDistanceGradient x w‖*‖physicalDistanceGradient x v‖≤4*‖v‖*‖w‖ := by
    have hh := mul_le_mul (physical_distance_gradient_norm_le x w)
      (physical_distance_gradient_norm_le x v) (norm_nonneg _) (by positivity)
    nlinarith
  have h1 := (fderiv ℝ (fderiv ℝ g) (physicalDistanceTriple x)
      (physicalDistanceGradient x w)).le_opNorm (physicalDistanceGradient x v)
  have h1' := (fderiv ℝ (fderiv ℝ g) (physicalDistanceTriple x)).le_opNorm
      (physicalDistanceGradient x w)
  have h2 := (fderiv ℝ g (physicalDistanceTriple x)).le_opNorm (physicalDistanceHessian x v w)
  have ha := mul_le_mul_of_nonneg_right h1' (norm_nonneg (physicalDistanceGradient x v))
  have hb := mul_le_mul_of_nonneg_left h0 (norm_nonneg (fderiv ℝ (fderiv ℝ g) (physicalDistanceTriple x)))
  have hc := mul_le_mul_of_nonneg_left (physical_distance_hessian_norm_le hx v w)
    (norm_nonneg (fderiv ℝ g (physicalDistanceTriple x)))
  have hh := norm_add_le
    (fderiv ℝ (fderiv ℝ g) (physicalDistanceTriple x)
      (physicalDistanceGradient x w) (physicalDistanceGradient x v))
    (fderiv ℝ g (physicalDistanceTriple x) (physicalDistanceHessian x v w))
  rw [←norm_iteratedFDeriv_one g] at hc
  rw [he] at hb ha
  rw [←norm_iteratedFDeriv_one g] at h2
  change ‖physicalDistanceCompositionSecond g x v w‖≤_ at hh
  nlinarith

#print axioms physical_distance_composition_second
#print axioms physical_distance_composition_second_norm_le
end ManyBody.S8