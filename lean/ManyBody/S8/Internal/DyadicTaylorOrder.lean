import ManyBody.S8.Internal.RealRationalAmbientProfile

/-! One fixed prefactor offset and a linear order in the requested dyadic
precision control the genuine derivatives of one canonical Taylor polynomial. -/
set_option autoImplicit false
noncomputable section
open Filter Metric
open scoped Topology BigOperators
namespace ManyBody.S8

theorem geometric_two_thirds_dyadic (p : ℕ) :
    (2/3:ℝ)^(2*p)≤(1/2:ℝ)^p := by
  rw [pow_mul]
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) p

theorem taylor_prefactor_fixed_dyadic_offset (B : Fin 3 → ℝ) :
    ∃ m : ℕ, ∀ p : ℕ, ∀ k : Fin 3,
      B k*(2/3:ℝ)^(2*p+m+2-(k:ℕ))≤(1/2:ℝ)^p := by
  let K : ℝ := 1+∑ k : Fin 3, |B k|
  have hK : 0<K := by
    have hs : 0≤∑ k : Fin 3, |B k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    dsimp [K]
    linarith
  have hBk (k : Fin 3) : B k≤K := by
    have hs := Finset.single_le_sum (fun j _ => abs_nonneg (B j)) (Finset.mem_univ k)
    dsimp [K]
    linarith [le_abs_self (B k)]
  have hlim : Tendsto (fun m : ℕ => K*(2/3:ℝ)^m) atTop (𝓝 0) := by
    convert (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(2/3:ℝ))
      (by norm_num : (2/3:ℝ)<1)).const_mul K using 1
    simp
  obtain ⟨m,hm⟩ := (hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))).exists
  refine ⟨m,?_⟩
  intro p k
  have hk : 2*p+m≤2*p+m+2-(k:ℕ) := by have := k.isLt; omega
  have hpow : (2/3:ℝ)^(2*p+m+2-(k:ℕ))≤(2/3:ℝ)^(2*p+m) :=
    (pow_le_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num)).mpr hk
  calc
    _≤K*(2/3:ℝ)^(2*p+m+2-(k:ℕ)) := mul_le_mul_of_nonneg_right (hBk k) (by positivity)
    _≤K*(2/3:ℝ)^(2*p+m) := mul_le_mul_of_nonneg_left hpow hK.le
    _=(K*(2/3:ℝ)^m)*(2/3:ℝ)^(2*p) := by rw [pow_add]; ring
    _≤1*(1/2:ℝ)^p := mul_le_mul hm.le (geometric_two_thirds_dyadic p) (by positivity) (by norm_num)
    _=(1/2:ℝ)^p := one_mul _

theorem complex_coupled_taylor_dyadic_order
    {f : (Fin 3 → ℂ) → ℂ} {a : Fin 3 → ℂ} {R C : ℝ}
    (hdata : CoupledComplexDistanceTaylorData f a R C) :
    ∃ m : ℕ, ∀ p : ℕ, ∀ q : Fin 3 → ℂ, ‖q-a‖<R/4 → ∀ k : Fin 3,
      ‖iteratedFDeriv ℂ (k:ℕ) f q-
        iteratedFDeriv ℂ (k:ℕ) (complexTaylorPolynomial f a (2*p+m+2)) q‖≤(1/2:ℝ)^p := by
  obtain ⟨m,hm⟩ := taylor_prefactor_fixed_dyadic_offset
    (fun k : Fin 3 => 3*C*(2*Real.exp 1/R)^(k:ℕ)*((k:ℕ).factorial:ℝ))
  exact ⟨m,fun p q hq k => ((hdata.2.2 (2*p+m+2) q hq).2 (k:ℕ)).trans (hm p k)⟩

theorem real_coupled_taylor_dyadic_order
    {f : (Fin 3 → ℂ) → ℂ} {a : Fin 3 → ℝ} {R C : ℝ}
    (hdata : ComplexDistanceTaylorData f (ambientRealCast a) R C)
    (hf : AnalyticOnNhd ℂ f (ball (ambientRealCast a) R)) :
    ∃ m : ℕ, ∀ p : ℕ, ∀ q : Fin 3 → ℝ, ‖q-a‖<R/4 → ∀ k : Fin 3,
      ‖iteratedFDeriv ℝ (k:ℕ) (ambientRealScalarProfile f) q-
        iteratedFDeriv ℝ (k:ℕ) (realTaylorPolynomial (ambientRealScalarProfile f) a (2*p+m+2)) q‖≤(1/2:ℝ)^p := by
  obtain ⟨m,hm⟩ := taylor_prefactor_fixed_dyadic_offset
    (fun k : Fin 3 => 3*C*(2*Real.exp 1/R)^(k:ℕ)*((k:ℕ).factorial:ℝ))
  refine ⟨m,?_⟩
  intro p q hq k
  have hR : 0<R := by nlinarith [norm_nonneg (q-a)]
  have hqc : ambientRealCast q∈ball (ambientRealCast a) R := by
    rw [mem_ball,dist_eq_norm,←map_sub,ambientRealCast_norm]
    linarith
  exact (ambient_real_coupled_taylor_error hdata (hf _ hqc) hq (2*p+m+2) (k:ℕ)).trans (hm p k)

theorem real_three_profiles_common_dyadic_order
    {f : Fin 3 → (Fin 3 → ℂ) → ℂ} {a : Fin 3 → ℝ} {R : ℝ} {C : Fin 3 → ℝ}
    (hR : 0<R)
    (hdata : ∀ j, ComplexDistanceTaylorData (f j) (ambientRealCast a) R (C j))
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) (ball (ambientRealCast a) R)) :
    ∃ m : ℕ, ∀ p : ℕ, ∀ q : Fin 3 → ℝ, ‖q-a‖<R/4 → ∀ j k : Fin 3,
      ‖iteratedFDeriv ℝ (k:ℕ) (ambientRealScalarProfile (f j)) q-
        iteratedFDeriv ℝ (k:ℕ) (realTaylorPolynomial (ambientRealScalarProfile (f j)) a (2*p+m+2)) q‖≤(1/2:ℝ)^p := by
  let C0 : ℝ := ∑ j : Fin 3, |C j|
  have hC (j : Fin 3) : C j≤C0 :=
    (le_abs_self (C j)).trans (Finset.single_le_sum (fun i _ => abs_nonneg (C i)) (Finset.mem_univ j))
  obtain ⟨m,hm⟩ := taylor_prefactor_fixed_dyadic_offset
    (fun k : Fin 3 => 3*C0*(2*Real.exp 1/R)^(k:ℕ)*((k:ℕ).factorial:ℝ))
  refine ⟨m,?_⟩
  intro p q hq j k
  have hqc : ambientRealCast q∈ball (ambientRealCast a) R := by
    rw [mem_ball,dist_eq_norm,←map_sub,ambientRealCast_norm]
    linarith
  have hcoef : 3*C j*(2*Real.exp 1/R)^(k:ℕ)*((k:ℕ).factorial:ℝ)≤
      3*C0*(2*Real.exp 1/R)^(k:ℕ)*((k:ℕ).factorial:ℝ) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hC j) (by norm_num))
        (by positivity)) (by positivity)
  exact (ambient_real_coupled_taylor_error (hdata j) (hf j _ hqc) hq (2*p+m+2) (k:ℕ)).trans
    ((mul_le_mul_of_nonneg_right hcoef (by positivity)).trans (hm p k))

#print axioms real_three_profiles_common_dyadic_order
#print axioms geometric_two_thirds_dyadic
#print axioms taylor_prefactor_fixed_dyadic_offset
#print axioms complex_coupled_taylor_dyadic_order
#print axioms real_coupled_taylor_dyadic_order
end ManyBody.S8
