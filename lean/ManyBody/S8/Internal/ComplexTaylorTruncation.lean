import ManyBody.S8.Internal.HolomorphicBallDerivativeBounds
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic
/-! Actual complex Taylor sums and quantitative local polynomial truncation.

The Taylor terms are exactly factorial-inverse times the actual complex
iterated Frechet derivative at the stated center, evaluated diagonally. A
local actual multilinear power series is selected from holomorphic data;
one-variable power-series uniqueness identifies its affine-line restriction
with the actual Cauchy series. The true Cauchy circle estimate then bounds
these same coefficients and sums, giving an explicit geometric error.

On the quarter ball, the value Taylor polynomial has error at most
(3/2)*C*3^(-N). Every genuine derivative field has its own actual Taylor
polynomial, with error at most 3*C*(2*exp(1)/R)^k*k!*(2/3)^N.
These derivative-field polynomial approximants are stated directly. This
module does not assert that they are derivatives of one truncated value
polynomial, or that the actual coefficients are rational or computable.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Metric
open scoped Topology BigOperators NNReal ENNReal
namespace ManyBody.S8
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

def complexTaylorCoefficient (f : E → F) (a : E) (n : ℕ) (h : E) : F :=
  (n.factorial:ℂ)⁻¹ • iteratedFDeriv ℂ n f a (fun _ => h)

def complexTaylorPolynomial (f : E → F) (a : E) (N : ℕ) (q : E) : F :=
  ∑ n∈Finset.range N, complexTaylorCoefficient f a n (q-a)

theorem actual_power_series_diagonal_coefficient
    {f : E → F} {p : FormalMultilinearSeries ℂ E F} {a : E}
    (hp : HasFPowerSeriesAt f p a) (n : ℕ) (h : E) :
    p n (fun _ => h)=complexTaylorCoefficient f a n h := by
  obtain ⟨r,hp⟩ := hp
  have hn : (n.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  dsimp only [complexTaylorCoefficient]
  rw [←hp.factorial_smul h n,←Nat.cast_smul_eq_nsmul ℂ,smul_smul,inv_mul_cancel₀ hn,one_smul]

theorem holomorphic_taylor_line_sum_and_error
    {f : E → F} {p : FormalMultilinearSeries ℂ E F} {a h : E} {R C ρ : ℝ}
    (hp : HasFPowerSeriesAt f p a) (hρ : 1<ρ) (hmargin : ρ*‖h‖<R)
    (hf : AnalyticOnNhd ℂ f (ball a R)) (hb : ∀ q∈ball a R, ‖f q‖≤C) :
    HasSum (fun n => complexTaylorCoefficient f a n h) (f (a+h)) ∧
    ∀ N : ℕ, ‖f (a+h)-complexTaylorPolynomial f a N (a+h)‖≤
      C*(ρ⁻¹)^N/(1-ρ⁻¹) := by
  have hρpos : 0<ρ := lt_trans zero_lt_one hρ
  let l : ℂ → E := fun z => a+z • h
  let L : ℂ →L[ℂ] E := (ContinuousLinearMap.id ℂ ℂ).smulRight h
  have hmem (z : ℂ) (hz : z∈closedBall 0 ρ) : l z∈ball a R := by
    have hn : ‖z‖≤ρ := by simpa only [mem_closedBall,dist_zero_right] using hz
    rw [mem_ball,dist_eq_norm]
    simp only [l,add_sub_cancel_left,norm_smul]
    exact (mul_le_mul_of_nonneg_right hn (norm_nonneg h)).trans_lt hmargin
  have hline (z : ℂ) : AnalyticAt ℂ l z :=
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hdiff : DifferentiableOn ℂ (f∘l) (closedBall 0 ρ) :=
    fun z hz => ((hf _ (hmem z hz)).comp (hline z)).differentiableAt.differentiableWithinAt
  let rad : ℝ≥0 := ⟨ρ,hρpos.le⟩
  have hcauchy := hdiff.hasFPowerSeriesOnBall (R:=rad) (by exact hρpos)
  have hshift : HasFPowerSeriesAt (fun y : E => f (a+y)) p 0 := by
    simpa only [sub_neg_eq_add,add_neg_cancel,add_comm] using hp.comp_sub (-a)
  have hrestricted : HasFPowerSeriesAt (f∘l) (p.compContinuousLinearMap L) 0 := by
    simpa only [L,l,Function.comp_def,ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply,map_zero] using (show HasFPowerSeriesAt (fun y : E => f (a+y)) p (L 0) by simpa only [map_zero] using hshift).compContinuousLinearMap (u:=L) (x:=0)
  have heq := hcauchy.hasFPowerSeriesAt.eq_formalMultilinearSeries hrestricted
  change cauchyPowerSeries (f∘l) 0 ρ=p.compContinuousLinearMap L at heq
  have hcoeff (n : ℕ) : cauchyPowerSeries (f∘l) 0 ρ n (fun _ => (1:ℂ))=
      complexTaylorCoefficient f a n h := by
    rw [heq,FormalMultilinearSeries.compContinuousLinearMap_apply]
    simp only [Function.comp_def,L,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,one_smul]
    exact actual_power_series_diagonal_coefficient hp n h
  have hsum : HasSum (fun n => complexTaylorCoefficient f a n h) (f (a+h)) := by
    have hm : (1:ℂ)∈eball (0:ℂ) (rad:ℝ≥0∞) := by
      rw [Metric.mem_eball,edist_zero_right]
      simpa only [enorm_one,ENNReal.one_lt_coe_iff] using (show (1:ℝ≥0)<rad by exact_mod_cast hρ)
    have hraw := hcauchy.hasSum hm
    change HasSum (fun n => cauchyPowerSeries (f∘l) 0 ρ n (fun _ => (1:ℂ))) ((f∘l) (0+1)) at hraw
    have hraw' : HasSum (fun n => cauchyPowerSeries (f∘l) 0 ρ n (fun _ => (1:ℂ))) (f (a+h)) := by
      simpa only [Function.comp_apply,l,one_smul,zero_add] using hraw
    simpa only [hcoeff] using hraw'
  have hbound (n : ℕ) : ‖complexTaylorCoefficient f a n h‖≤C*(ρ⁻¹)^n := by
    rw [←hcoeff,cauchyPowerSeries_apply]
    have hh := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
      hρpos.le (f:=fun z : ℂ => (1/(z-0))^n • (z-0)⁻¹ • (f∘l) z) (c:=0) (R:=ρ)
      (C:=(ρ⁻¹)^n*ρ⁻¹*C) (by
        intro z hz
        have hzn : ‖z‖=ρ := by simpa only [mem_sphere,dist_zero_right] using hz
        have hzb := hb (l z) (hmem z (sphere_subset_closedBall hz))
        simp only [sub_zero,norm_smul,norm_pow,norm_inv,hzn,one_div,
          Function.comp_apply]
        calc
          _≤(ρ⁻¹)^n*(ρ⁻¹*C) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hzb (inv_nonneg.mpr hρpos.le))
              (pow_nonneg (inv_nonneg.mpr hρpos.le) n)
          _=_ := by ring)
    calc
      _≤ρ*((ρ⁻¹)^n*ρ⁻¹*C) := hh
      _=C*(ρ⁻¹)^n := by field_simp [hρpos.ne']
  refine ⟨hsum,?_⟩
  intro N
  have hratio : ρ⁻¹<1 := (inv_lt_one₀ hρpos).mpr hρ
  have ht := norm_sub_le_of_geometric_bound_of_hasSum hratio hbound hsum N
  simpa only [complexTaylorPolynomial,add_sub_cancel_left,norm_sub_rev] using ht

#print axioms actual_power_series_diagonal_coefficient
#print axioms holomorphic_taylor_line_sum_and_error

def ComplexDistanceTaylorData (f : E → F) (a : E) (R C : ℝ) : Prop :=
  (∃ p : FormalMultilinearSeries ℂ E F, HasFPowerSeriesAt f p a ∧
    ∀ n : ℕ, ∀ h : E, p n (fun _ => h)=complexTaylorCoefficient f a n h) ∧
  (∀ q : E, ‖q-a‖<R/4 →
    HasSum (fun n => complexTaylorCoefficient f a n (q-a)) (f q) ∧
    ∀ N : ℕ, ‖f q-complexTaylorPolynomial f a N q‖≤(3/2)*C*(1/3:ℝ)^N) ∧
  (∀ k : ℕ, ∀ q : E, ‖q-a‖<R/4 →
    HasSum (fun n => complexTaylorCoefficient (iteratedFDeriv ℂ k f) a n (q-a))
      (iteratedFDeriv ℂ k f q) ∧
    ∀ N : ℕ, ‖iteratedFDeriv ℂ k f q-
      complexTaylorPolynomial (iteratedFDeriv ℂ k f) a N q‖≤
      3*C*(2*Real.exp 1/R)^k*(k.factorial:ℝ)*(2/3:ℝ)^N)

theorem bounded_holomorphic_complex_taylor_data
    {f : E → F} {a : E} {R C : ℝ} (hR : 0<R)
    (hf : AnalyticOnNhd ℂ f (ball a R)) (hb : ∀ q∈ball a R, ‖f q‖≤C) :
    ComplexDistanceTaylorData f a R C := by
  obtain ⟨p,hp⟩ := hf a (mem_ball_self hR)
  have hC : 0≤C := (norm_nonneg (f a)).trans (hb a (mem_ball_self hR))
  refine ⟨⟨p,hp,fun n h => actual_power_series_diagonal_coefficient hp n h⟩,?_,?_⟩
  · intro q hq
    have hm : (3:ℝ)*‖q-a‖<R := by linarith
    have hh := holomorphic_taylor_line_sum_and_error hp (by norm_num : (1:ℝ)<3) hm hf hb
    have he : a+(q-a)=q := by abel
    rw [he] at hh
    refine ⟨hh.1,?_⟩
    intro N
    calc
      _≤C*((3:ℝ)⁻¹)^N/(1-(3:ℝ)⁻¹) := hh.2 N
      _=(3/2)*C*(1/3:ℝ)^N := by norm_num; ring
  · intro k q hq
    have hhalf : 0<R/2 := by positivity
    have hAn : AnalyticOnNhd ℂ (iteratedFDeriv ℂ k f) (ball a (R/2)) := by
      intro z hz
      apply hf.iteratedFDeriv k z
      rw [mem_ball,dist_eq_norm] at hz ⊢
      linarith
    have hbD : ∀ z∈ball a (R/2), ‖iteratedFDeriv ℂ k f z‖≤
        C*(2*Real.exp 1/R)^k*(k.factorial:ℝ) := by
      intro z hz
      exact holomorphic_iteratedFDeriv_half_ball_bound hR hC
        (by simpa only [mem_ball,dist_eq_norm] using hz) hf hb k
    obtain ⟨pk,hpk⟩ := hAn a (mem_ball_self hhalf)
    have hm : (3/2:ℝ)*‖q-a‖<R/2 := by linarith
    have hh := holomorphic_taylor_line_sum_and_error hpk (by norm_num : (1:ℝ)<3/2) hm hAn hbD
    have he : a+(q-a)=q := by abel
    rw [he] at hh
    refine ⟨hh.1,?_⟩
    intro N
    calc
      _≤(C*(2*Real.exp 1/R)^k*(k.factorial:ℝ))*((3/2:ℝ)⁻¹)^N/(1-(3/2:ℝ)⁻¹) := hh.2 N
      _=3*C*(2*Real.exp 1/R)^k*(k.factorial:ℝ)*(2/3:ℝ)^N := by norm_num; ring

#print axioms bounded_holomorphic_complex_taylor_data
end ManyBody.S8