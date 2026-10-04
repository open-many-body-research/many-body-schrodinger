import ManyBody.S8.Internal.AmbientRealDerivativeTransport
import ManyBody.S8.Internal.ComplexTaylorPolynomialDerivatives
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic
/-! Genuine complex-valued Taylor C2 errors on real distance inputs.

Actual full-ball holomorphy and coupled derivatives of the SAME canonical
Taylor value polynomial imply local real C-infinity regularity and arbitrarily
small value, first and second real Frechet norms of its literal complex-valued
remainder, uniformly on the closed inner eighth box. Exact scalar restriction
and the cast isometry provide the derivative/operator transport. The common
explicit rate is K*(2/3)^(N-2); no C2 approximation or derivative budget is
assumed, and no real projection substitutes for the original complex values. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology ContDiff BigOperators
namespace ManyBody.S8

def ambientComplexTaylorError (h : (Fin 3 → ℂ) → ℂ) (a : Fin 3 → ℝ)
    (N : ℕ) (p : Fin 3 → ℝ) : ℂ :=
  h (ambientRealCast p)-complexTaylorPolynomial h (ambientRealCast a) N (ambientRealCast p)

def ambientComplexTaylorC2Prefactor (R C : ℝ) : ℝ :=
  1+∑ k : Fin 3, |3*C*(2*Real.exp 1/R)^(k:ℕ)*((k:ℕ).factorial:ℝ)|

theorem ambientComplexTaylorError_contDiffOn
    {h : (Fin 3 → ℂ) → ℂ} {a : Fin 3 → ℝ} {R C : ℝ}
    (hhol : AnalyticOnNhd ℂ h (ball (ambientRealCast a) R))
    (hdata : CoupledComplexDistanceTaylorData h (ambientRealCast a) R C) (N : ℕ) :
    ContDiffOn ℝ ∞ (ambientComplexTaylorError h a N) (ball a R) := by
  have hana : AnalyticOnNhd ℝ (ambientComplexTaylorError h a N) (ball a R) := by
    intro p hp
    have hpc : ambientRealCast p∈ball (ambientRealCast a) R := by
      rw [mem_ball,dist_eq_norm,←map_sub,ambientRealCast_norm]
      simpa only [mem_ball,dist_eq_norm] using hp
    have hPN : AnalyticAt ℂ (complexTaylorPolynomial h (ambientRealCast a) N)
        (ambientRealCast p) := (hdata.1 N _ (mem_univ _)).analyticAt
    change AnalyticAt ℝ ((h-complexTaylorPolynomial h (ambientRealCast a) N) ∘ ambientRealCast) p
    exact ((hhol _ hpc).sub hPN).restrictScalars.comp (ambientRealCast.analyticAt p)
  exact hana.contDiffOn_of_completeSpace

theorem ambientComplexTaylorError_C2_bound
    {h : (Fin 3 → ℂ) → ℂ} {a p : Fin 3 → ℝ} {R C : ℝ}
    (hR : 0<R) (hhol : AnalyticOnNhd ℂ h (ball (ambientRealCast a) R))
    (hdata : CoupledComplexDistanceTaylorData h (ambientRealCast a) R C)
    (hp : ‖p-a‖≤R/8) (N : ℕ) (k : Fin 3) :
    ‖iteratedFDeriv ℝ (k:ℕ) (ambientComplexTaylorError h a N) p‖≤
      ambientComplexTaylorC2Prefactor R C*(2/3:ℝ)^(N-2) := by
  have hpc : ambientRealCast p∈ball (ambientRealCast a) R := by
    rw [mem_ball,dist_eq_norm,←map_sub,ambientRealCast_norm]
    linarith
  have hquarter : ‖ambientRealCast p-ambientRealCast a‖<R/4 := by
    rw [←map_sub,ambientRealCast_norm]
    linarith
  have hPN : AnalyticAt ℂ (complexTaylorPolynomial h (ambientRealCast a) N)
      (ambientRealCast p) := (hdata.1 N _ (mem_univ _)).analyticAt
  have hnorm := ambient_real_iteratedFDeriv_norm_le_complex ((hhol _ hpc).sub hPN) (k:ℕ)
  change ‖iteratedFDeriv ℝ (k:ℕ) (ambientComplexTaylorError h a N) p‖≤
    ‖iteratedFDeriv ℂ (k:ℕ) (h-complexTaylorPolynomial h (ambientRealCast a) N) (ambientRealCast p)‖ at hnorm
  rw [iteratedFDeriv_sub_apply ((hhol _ hpc).contDiffAt) hPN.contDiffAt] at hnorm
  have hactual := (hdata.2.2 N _ hquarter).2 (k:ℕ)
  have hK : 0<ambientComplexTaylorC2Prefactor R C := by
    have hsum : 0≤∑ l : Fin 3, |3*C*(2*Real.exp 1/R)^(l:ℕ)*((l:ℕ).factorial:ℝ)| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    unfold ambientComplexTaylorC2Prefactor
    linarith
  have hBk : 3*C*(2*Real.exp 1/R)^(k:ℕ)*((k:ℕ).factorial:ℝ)≤
      ambientComplexTaylorC2Prefactor R C := by
    have hs := Finset.single_le_sum
      (fun (l : Fin 3) _ => abs_nonneg (3*C*(2*Real.exp 1/R)^(l:ℕ)*((l:ℕ).factorial:ℝ)))
      (Finset.mem_univ k)
    unfold ambientComplexTaylorC2Prefactor
    linarith [le_abs_self (3*C*(2*Real.exp 1/R)^(k:ℕ)*((k:ℕ).factorial:ℝ))]
  have hk : N-2≤N-(k:ℕ) := by have := k.isLt; omega
  have hpow : (2/3:ℝ)^(N-(k:ℕ))≤(2/3:ℝ)^(N-2) :=
    (pow_le_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num)).mpr hk
  exact hnorm.trans (hactual.trans ((mul_le_mul_of_nonneg_right hBk (by positivity)).trans
    (mul_le_mul_of_nonneg_left hpow hK.le)))

theorem ambientComplexTaylorError_C2_arbitrarily_small
    {h : (Fin 3 → ℂ) → ℂ} {a : Fin 3 → ℝ} {R C : ℝ}
    (hR : 0<R) (hhol : AnalyticOnNhd ℂ h (ball (ambientRealCast a) R))
    (hdata : CoupledComplexDistanceTaylorData h (ambientRealCast a) R C)
    (N0 : ℕ) {ζ : ℝ} (hζ : 0<ζ) :
    ∃ N : ℕ, N0≤N ∧ 2≤N ∧
      ContDiffOn ℝ ∞ (ambientComplexTaylorError h a N) (ball a R) ∧
      ∀ p∈closedBall a (R/8),
        ‖ambientComplexTaylorError h a N p‖≤ζ ∧
        ‖fderiv ℝ (ambientComplexTaylorError h a N) p‖≤ζ ∧
        ‖fderiv ℝ (fderiv ℝ (ambientComplexTaylorError h a N)) p‖≤ζ := by
  have hlim : Tendsto (fun n : ℕ => ambientComplexTaylorC2Prefactor R C*(2/3:ℝ)^n)
      atTop (𝓝 0) := by
    convert (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(2/3:ℝ))
      (by norm_num : (2/3:ℝ)<1)).const_mul (ambientComplexTaylorC2Prefactor R C) using 1
    simp
  obtain ⟨n,hn0,hn⟩ := ((eventually_ge_atTop N0).and (hlim.eventually (gt_mem_nhds hζ))).exists
  refine ⟨n+2,by omega,by omega,ambientComplexTaylorError_contDiffOn hhol hdata _,?_⟩
  intro p hp
  have hpn : ‖p-a‖≤R/8 := by simpa only [mem_closedBall,dist_eq_norm] using hp
  have hbound (k : Fin 3) :
      ‖iteratedFDeriv ℝ (k:ℕ) (ambientComplexTaylorError h a (n+2)) p‖≤ζ := by
    apply (ambientComplexTaylorError_C2_bound hR hhol hdata hpn (n+2) k).trans
    simpa only [Nat.add_sub_cancel] using hn.le
  refine ⟨?_,?_,?_⟩
  · simpa only [Fin.val_zero,norm_iteratedFDeriv_zero] using hbound 0
  · simpa only [Fin.val_one,norm_iteratedFDeriv_one] using hbound 1
  · rw [←norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv (n:=1)]
    exact hbound 2

#print axioms ambientComplexTaylorError_contDiffOn
#print axioms ambientComplexTaylorError_C2_bound
#print axioms ambientComplexTaylorError_C2_arbitrarily_small
end ManyBody.S8
