import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Tactic
/-! Quantitative Cauchy bounds for genuine complex Frechet derivatives.

A bounded holomorphic map on an actual Banach-space ball has first derivative
operator norm at most C/d whenever a closed complex line disc of radius d
stays in that ball. This is derived from the pinned one-variable Cauchy
estimate for every unit input direction.

Applying that estimate to the genuine iterated derivative fields on n
successively smaller balls gives C*(2*n/R)^n on the half ball. The proved
Stirling inequality converts it to C*(2*exp(1)/R)^n*n!.
No derivative bound or series coefficient bound is an input premise.
-/

set_option autoImplicit false
noncomputable section
open Metric Set
namespace ManyBody.S8
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem holomorphic_fderiv_ball_bound {f : E → F} {a x : E} {R d C : ℝ}
    (hd : 0<d) (hC : 0≤C) (hxd : ‖x-a‖+d<R)
    (hf : AnalyticOnNhd ℂ f (ball a R))
    (hb : ∀ y ∈ ball a R, ‖f y‖≤C) : ‖fderiv ℂ f x‖≤C/d := by
  have hx : x∈ball a R := by rw [mem_ball,dist_eq_norm]; linarith
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg hC hd.le)
  intro v hv
  let l : ℂ → E := fun z => x+z • v
  have hmem (z : ℂ) (hz : z∈closedBall 0 d) : l z∈ball a R := by
    have hzn : ‖z‖≤d := by simpa only [mem_closedBall,dist_zero_right] using hz
    rw [mem_ball,dist_eq_norm]
    have ht := norm_add_le (x-a) (z • v)
    rw [norm_smul,hv,mul_one] at ht
    have he : l z-a=(x-a)+z • v := by dsimp [l]; abel
    rw [he]
    linarith
  have hline (z : ℂ) : AnalyticAt ℂ l z :=
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hdiff : DiffContOnCl ℂ (f∘l) (ball 0 d) := by
    apply DifferentiableOn.diffContOnCl_ball (U:=closedBall 0 d)
    · intro z hz
      exact ((hf (l z) (hmem z hz)).comp (hline z)).differentiableAt.differentiableWithinAt
    · exact fun z hz => hz
  have hcircle (z : ℂ) (hz : z∈sphere 0 d) : ‖(f∘l) z‖≤C :=
    hb (l z) (hmem z (sphere_subset_closedBall hz))
  have hderiv : HasDerivAt (f∘l) (fderiv ℂ f x v) 0 := by
    have hl : HasDerivAt l v 0 := by
      simpa only [l,one_smul] using ((hasDerivAt_id' (0:ℂ)).smul_const v).const_add x
    exact (hf x hx).differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp [l])
  rw [←hderiv.deriv]
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hd hdiff hcircle

#print axioms holomorphic_fderiv_ball_bound

theorem real_nat_pow_le_exp_factorial (n : ℕ) :
    (n:ℝ)^n≤(Real.exp 1)^n*(n.factorial:ℝ) := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  have hnR : 1≤(n:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hin : 1≤2*Real.pi*n := by
    have hh := mul_le_mul_of_nonneg_left hnR (by positivity : 0≤2*Real.pi)
    nlinarith [Real.one_le_pi_div_two]
  have hs : 1≤Real.sqrt (2*Real.pi*n) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hin
  have hh : ((n:ℝ)/Real.exp 1)^n≤(n.factorial:ℝ) :=
    (le_mul_of_one_le_left (by positivity) hs).trans (Stirling.le_factorial_stirling n)
  calc
    (n:ℝ)^n=(Real.exp 1)^n*((n:ℝ)/Real.exp 1)^n := by
      rw [←mul_pow]
      congr 1
      field_simp
    _≤_ := mul_le_mul_of_nonneg_left hh (by positivity)

theorem holomorphic_iteratedFDeriv_half_ball_bound [CompleteSpace F] {f : E → F} {a x : E} {R C : ℝ}
    (hR : 0<R) (hC : 0≤C) (hx : ‖x-a‖<R/2)
    (hf : AnalyticOnNhd ℂ f (ball a R)) (hb : ∀ y ∈ ball a R, ‖f y‖≤C)
    (n : ℕ) :
    ‖iteratedFDeriv ℂ n f x‖≤C*(2*Real.exp 1/R)^n*(n.factorial:ℝ) := by
  obtain rfl | hn := eq_or_ne n 0
  · simpa only [norm_iteratedFDeriv_zero,pow_zero,Nat.factorial_zero,Nat.cast_one,mul_one]
      using hb x (by rw [mem_ball,dist_eq_norm]; linarith)
  have hnR : 0<(n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  let d : ℝ := R/(2*n)
  have hd : 0<d := by dsimp [d]; positivity
  have hnd : (n:ℝ)*d=R/2 := by dsimp [d]; field_simp
  have hInd : ∀ k : ℕ, k≤n → ∀ y : E, ‖y-a‖<R-k*d →
      ‖iteratedFDeriv ℂ k f y‖≤C*(d⁻¹)^k := by
    intro k
    induction k with
    | zero =>
      intro _ y hy
      simpa only [Nat.cast_zero,zero_mul,sub_zero,norm_iteratedFDeriv_zero,pow_zero,mul_one]
        using hb y (by simpa only [Nat.cast_zero,zero_mul,sub_zero,mem_ball,dist_eq_norm] using hy)
    | succ k ih =>
      intro hk y hy
      have hk' : k≤n := (Nat.le_succ k).trans hk
      have hkR : 0≤(k:ℝ)*d := mul_nonneg (Nat.cast_nonneg _) hd.le
      have han : AnalyticOnNhd ℂ (iteratedFDeriv ℂ k f) (ball a (R-k*d)) := by
        intro z hz
        apply hf.iteratedFDeriv k z
        rw [mem_ball,dist_eq_norm] at hz ⊢
        linarith
      have hbudget : 0≤C*(d⁻¹)^k := by positivity
      have hdist : ‖y-a‖+d<R-k*d := by
        push_cast at hy
        nlinarith
      have hstep := holomorphic_fderiv_ball_bound hd hbudget hdist han
        (fun z hz => ih hk' z (by simpa only [mem_ball,dist_eq_norm] using hz))
      rw [norm_fderiv_iteratedFDeriv] at hstep
      calc
        _≤(C*(d⁻¹)^k)/d := hstep
        _=C*(d⁻¹)^(k+1) := by rw [pow_succ]; ring
  have hxn : ‖x-a‖<R-(n:ℝ)*d := by rw [hnd]; linarith
  have hraw := hInd n le_rfl x hxn
  have hdInv : d⁻¹=2*(n:ℝ)/R := by dsimp [d]; field_simp
  rw [hdInv] at hraw
  calc
    _≤C*(2*(n:ℝ)/R)^n := hraw
    _=C*(2/R)^n*(n:ℝ)^n := by rw [div_eq_mul_inv,div_eq_mul_inv,mul_pow]; ring
    _≤C*(2/R)^n*((Real.exp 1)^n*(n.factorial:ℝ)) :=
      mul_le_mul_of_nonneg_left (real_nat_pow_le_exp_factorial n) (by positivity)
    _=C*(2*Real.exp 1/R)^n*(n.factorial:ℝ) := by
      have he : 2*Real.exp 1/R=(2/R)*Real.exp 1 := by ring
      rw [he,mul_pow]
      ring

#print axioms real_nat_pow_le_exp_factorial
#print axioms holomorphic_iteratedFDeriv_half_ball_bound

end ManyBody.S8
