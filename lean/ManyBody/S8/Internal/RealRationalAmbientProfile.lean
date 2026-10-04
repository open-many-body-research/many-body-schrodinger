import ManyBody.S8.Internal.RealTaylorDistanceDictionary
import ManyBody.S8.Internal.ComplexTaylorPolynomialDerivatives
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.SpecificLimits.Basic
/-! Genuine real distance profiles and simultaneous rational C2 approximation.

Actual cast and real-output continuous linear maps transport every real jet
exactly to the genuine complex derivative. The canonical real Taylor
polynomial is the real part of the SAME complex polynomial, so its true
derivatives inherit the proved coupled Taylor remainders. A genuine finite
unshifted monomial representation and rational density then select ONE finite
rational polynomial approximating value, gradient, and Hessian uniformly on
the closed inner distance box. No C2 approximation or derivative identity is
assumed, and no effective coefficient-selection rate is asserted. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology BigOperators ContDiff
namespace ManyBody.S8

def ambientRealScalarProfile (f : (Fin 3 → ℂ) → ℂ) (p : Fin 3 → ℝ) : ℝ :=
  (f (ambientRealCast p)).re

theorem ambientRealScalarProfile_iteratedFDeriv
    {f : (Fin 3 → ℂ) → ℂ} {p : Fin 3 → ℝ}
    (hf : AnalyticAt ℂ f (ambientRealCast p)) (n : ℕ) (v : Fin n → (Fin 3 → ℝ)) :
    iteratedFDeriv ℝ n (ambientRealScalarProfile f) p v=
      (iteratedFDeriv ℂ n f (ambientRealCast p) (fun j => ambientRealCast (v j))).re := by
  have hfr : ContDiffAt ℝ n (f ∘ ambientRealCast) p :=
    (hf.restrictScalars.comp (ambientRealCast.analyticAt p)).contDiffAt
  rw [show ambientRealScalarProfile f=Complex.reCLM ∘ (f ∘ ambientRealCast) from rfl,
    Complex.reCLM.iteratedFDeriv_comp_left hfr le_rfl]
  change (iteratedFDeriv ℝ n (f ∘ ambientRealCast) p v).re=_
  rw [ambient_real_iteratedFDeriv_complex_restriction hf]

theorem ambientRealScalarProfile_derivative_difference_le
    {f g : (Fin 3 → ℂ) → ℂ} {p : Fin 3 → ℝ}
    (hf : AnalyticAt ℂ f (ambientRealCast p)) (hg : AnalyticAt ℂ g (ambientRealCast p))
    (n : ℕ) :
    ‖iteratedFDeriv ℝ n (ambientRealScalarProfile f) p-
        iteratedFDeriv ℝ n (ambientRealScalarProfile g) p‖≤
      ‖iteratedFDeriv ℂ n f (ambientRealCast p)-iteratedFDeriv ℂ n g (ambientRealCast p)‖ := by
  apply (iteratedFDeriv ℝ n (ambientRealScalarProfile f) p-
    iteratedFDeriv ℝ n (ambientRealScalarProfile g) p).opNorm_le_bound (norm_nonneg _)
  intro v
  rw [sub_apply,
    ambientRealScalarProfile_iteratedFDeriv hf,
    ambientRealScalarProfile_iteratedFDeriv hg]
  rw [←Complex.sub_re]
  calc
    _≤‖iteratedFDeriv ℂ n f (ambientRealCast p) (fun j => ambientRealCast (v j))-
      iteratedFDeriv ℂ n g (ambientRealCast p) (fun j => ambientRealCast (v j))‖ :=
        by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm _
    _≤_ := by
      simpa only [sub_apply,ambientRealCast_norm] using
        (iteratedFDeriv ℂ n f (ambientRealCast p)-iteratedFDeriv ℂ n g (ambientRealCast p)).le_opNorm
          (fun j => ambientRealCast (v j))

theorem realTaylorCoefficient_complex_restriction
    {f : (Fin 3 → ℂ) → ℂ} {a : Fin 3 → ℝ}
    (hf : AnalyticAt ℂ f (ambientRealCast a)) (n : ℕ) (h : Fin 3 → ℝ) :
    realTaylorCoefficient (ambientRealScalarProfile f) a n h=
      (complexTaylorCoefficient f (ambientRealCast a) n (ambientRealCast h)).re := by
  unfold realTaylorCoefficient complexTaylorCoefficient
  rw [ambientRealScalarProfile_iteratedFDeriv hf]
  simp [smul_eq_mul,Complex.mul_re]

theorem realTaylorPolynomial_complex_restriction
    {f : (Fin 3 → ℂ) → ℂ} {a : Fin 3 → ℝ}
    (hf : AnalyticAt ℂ f (ambientRealCast a)) (N : ℕ) :
    realTaylorPolynomial (ambientRealScalarProfile f) a N=
      ambientRealScalarProfile (complexTaylorPolynomial f (ambientRealCast a) N) := by
  funext p
  change (∑ n∈Finset.range N, realTaylorCoefficient (ambientRealScalarProfile f) a n (p-a))=
    Complex.reCLM (∑ n∈Finset.range N,
      complexTaylorCoefficient f (ambientRealCast a) n (ambientRealCast p-ambientRealCast a))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [realTaylorCoefficient_complex_restriction hf]
  congr 2
  exact map_sub ambientRealCast p a

theorem ambient_real_coupled_taylor_error
    {f : (Fin 3 → ℂ) → ℂ} {a p : Fin 3 → ℝ} {R C : ℝ}
    (hdata : ComplexDistanceTaylorData f (ambientRealCast a) R C)
    (hf : AnalyticAt ℂ f (ambientRealCast p)) (hp : ‖p-a‖<R/4) (N n : ℕ) :
    ‖iteratedFDeriv ℝ n (ambientRealScalarProfile f) p-
      iteratedFDeriv ℝ n (realTaylorPolynomial (ambientRealScalarProfile f) a N) p‖≤
      3*C*(2*Real.exp 1/R)^n*(n.factorial:ℝ)*(2/3:ℝ)^(N-n) := by
  have hc := actual_taylor_data_coupled hdata
  have hfa : AnalyticAt ℂ f (ambientRealCast a) := ⟨hdata.1.choose,hdata.1.choose_spec.1⟩
  rw [realTaylorPolynomial_complex_restriction hfa]
  have hg : AnalyticAt ℂ (complexTaylorPolynomial f (ambientRealCast a) N) (ambientRealCast p) :=
    (hc.1 N (ambientRealCast p) (mem_univ _)).analyticAt
  apply (ambientRealScalarProfile_derivative_difference_le hf hg n).trans
  have hpc : ‖ambientRealCast p-ambientRealCast a‖<R/4 := by
    rw [←map_sub,ambientRealCast_norm]
    exact hp
  exact (hc.2.2 N (ambientRealCast p) hpc).2 n

#print axioms ambientRealScalarProfile_derivative_difference_le
#print axioms realTaylorPolynomial_complex_restriction
#print axioms ambient_real_coupled_taylor_error

theorem rational_ambient_profile_uniform_C2
    {f : (Fin 3 → ℂ) → ℂ} {a : Fin 3 → ℝ} {R C : ℝ}
    (hR : 0<R) (hdata : ComplexDistanceTaylorData f (ambientRealCast a) R C)
    (hf : AnalyticOnNhd ℂ f (ball (ambientRealCast a) R))
    {ε : ℝ} (hε : 0<ε) :
    ∃ s : Finset DistanceMultiIndex, ∃ r : DistanceMultiIndex → ℚ,
      ∀ p : Fin 3 → ℝ, ‖p-a‖≤R/8 → ∀ k : Fin 3,
        ‖iteratedFDeriv ℝ (k:ℕ) (ambientRealScalarProfile f) p-
          iteratedFDeriv ℝ (k:ℕ) (realDistancePolynomial s (fun α => (r α:ℝ))) p‖<ε := by
  classical
  let B : Fin 3 → ℝ := fun k => 3*C*(2*Real.exp 1/R)^(k:ℕ)*((k:ℕ).factorial:ℝ)
  let K : ℝ := 1+∑ k : Fin 3, |B k|
  have hK : 0<K := by
    have hs : 0≤∑ k : Fin 3, |B k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    dsimp [K]
    linarith
  have hBk (k : Fin 3) : B k≤K := by
    have hs := Finset.single_le_sum (fun j _ => abs_nonneg (B j)) (Finset.mem_univ k)
    dsimp [K]
    linarith [le_abs_self (B k)]
  have hlim : Tendsto (fun n : ℕ => K*(2/3:ℝ)^n) atTop (𝓝 0) := by
    convert (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(2/3:ℝ))
      (by norm_num : (2/3:ℝ)<1)).const_mul K using 1
    simp
  obtain ⟨N0,hN0⟩ := (hlim.eventually (gt_mem_nhds (by linarith : (0:ℝ)<ε/2))).exists
  let N := N0+2
  obtain ⟨s,r,hr⟩ := rational_realTaylorPolynomial_uniform_C2
    (ambientRealScalarProfile f) a N (‖a‖+R/8) (by linarith : 0<ε/2)
  refine ⟨s,r,?_⟩
  intro p hp k
  have hpb : ‖p‖≤‖a‖+R/8 := by
    calc _=‖(p-a)+a‖ := by rw [sub_add_cancel]
         _≤‖p-a‖+‖a‖ := norm_add_le _ _
         _≤R/8+‖a‖ := add_le_add hp le_rfl
         _=_ := add_comm _ _
  have hpquarter : ‖p-a‖<R/4 := by linarith
  have hpc : ambientRealCast p∈ball (ambientRealCast a) R := by
    rw [mem_ball,dist_eq_norm,←map_sub,ambientRealCast_norm]
    linarith
  have hk : N0≤N-(k:ℕ) := by have := k.isLt; dsimp [N]; omega
  have hpow : (2/3:ℝ)^(N-(k:ℕ))≤(2/3:ℝ)^N0 :=
    (pow_le_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num)).mpr hk
  have he : ‖iteratedFDeriv ℝ (k:ℕ) (ambientRealScalarProfile f) p-
      iteratedFDeriv ℝ (k:ℕ) (realTaylorPolynomial (ambientRealScalarProfile f) a N) p‖<ε/2 := by
    calc _≤B k*(2/3:ℝ)^(N-(k:ℕ)) := ambient_real_coupled_taylor_error hdata (hf _ hpc) hpquarter N _
         _≤K*(2/3:ℝ)^(N-(k:ℕ)) := mul_le_mul_of_nonneg_right (hBk k) (by positivity)
         _≤K*(2/3:ℝ)^N0 := mul_le_mul_of_nonneg_left hpow hK.le
         _<ε/2 := hN0
  calc
    _≤‖iteratedFDeriv ℝ (k:ℕ) (ambientRealScalarProfile f) p-
        iteratedFDeriv ℝ (k:ℕ) (realTaylorPolynomial (ambientRealScalarProfile f) a N) p‖+
       ‖iteratedFDeriv ℝ (k:ℕ) (realTaylorPolynomial (ambientRealScalarProfile f) a N) p-
        iteratedFDeriv ℝ (k:ℕ) (realDistancePolynomial s (fun α => (r α:ℝ))) p‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _<ε/2+ε/2 := add_lt_add he (hr p hpb k)
    _=ε := by ring

#print axioms rational_ambient_profile_uniform_C2
end ManyBody.S8
