import ManyBody.S8.Internal.ComplexTaylorTruncation
import Mathlib.Analysis.Analytic.CPolynomialDef
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic
/-! Genuine derivatives of one canonical finite Taylor polynomial.

A coefficient-truncated actual multilinear series represents the literal
canonical Taylor polynomial globally. Differentiating this finite series
k times gives its actual iterated Frechet derivative. The coefficient at
index n of a differentiated series depends only on the original coefficient
at n+k; matching with the actual series of the original derivative field
proves D^k(Taylor_N f)=Taylor_(N-k)(D^k f), including N<=k.

The existing actual Taylor remainder estimates consequently become joint
value, gradient and Hessian estimates for one and the same polynomial.
All coefficients remain the actual factorial-inverse derivative values.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Metric
open scoped Topology BigOperators NNReal ENNReal
namespace ManyBody.S8
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

def complexTaylorFiniteSeries (p : FormalMultilinearSeries ℂ E F) (N : ℕ) :
    FormalMultilinearSeries ℂ E F := fun n => if n<N then p n else 0

theorem deriv_series_coefficient_congr {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℂ G] (p q : FormalMultilinearSeries ℂ E G) (n : ℕ)
    (h : p (n+1)=q (n+1)) : p.derivSeries n=q.derivSeries n := by
  have h' : p (1+n)=q (1+n) := by rw [Nat.add_comm 1 n]; exact h
  simp only [FormalMultilinearSeries.derivSeries,
    ContinuousLinearMap.compFormalMultilinearSeries_apply]
  congr 1
  simp only [FormalMultilinearSeries.changeOriginSeries]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [FormalMultilinearSeries.changeOriginSeriesTerm,h']

omit [CompleteSpace F] in
theorem iterated_series_coefficient_congr (p q : FormalMultilinearSeries ℂ E F)
    (k n : ℕ) (h : p (n+k)=q (n+k)) :
    p.iteratedFDerivSeries k n=q.iteratedFDerivSeries k n := by
  induction k generalizing n with
  | zero =>
    have h' : p n=q n := by simpa only [Nat.add_zero] using h
    simp only [FormalMultilinearSeries.iteratedFDerivSeries,
      ContinuousLinearMap.compFormalMultilinearSeries_apply,h']
  | succ k ih =>
    have h' : p ((n+1)+k)=q ((n+1)+k) := by
      have he : (n+1)+k=n+(k+1) := by omega
      rw [he]
      exact h
    have hh := deriv_series_coefficient_congr (p.iteratedFDerivSeries k)
      (q.iteratedFDerivSeries k) n (ih (n+1) h')
    simp only [FormalMultilinearSeries.iteratedFDerivSeries,
      ContinuousLinearMap.compFormalMultilinearSeries_apply,hh]

theorem complexTaylorPolynomial_has_finite_series
    {f : E → F} {p : FormalMultilinearSeries ℂ E F} {a : E}
    (hp : HasFPowerSeriesAt f p a) (N : ℕ) :
    HasFiniteFPowerSeriesOnBall (complexTaylorPolynomial f a N)
      (complexTaylorFiniteSeries p N) a N ⊤ := by
  apply HasFiniteFPowerSeriesOnBall.mk'
  · intro n hn
    simp only [complexTaylorFiniteSeries,ite_eq_right (not_lt.mpr hn)]
  · simp
  · intro h hh
    simp only [complexTaylorPolynomial,add_sub_cancel_left]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [complexTaylorFiniteSeries,ite_eq_left (Finset.mem_range.mp hn)]
    exact actual_power_series_diagonal_coefficient hp n h

omit [CompleteSpace F] in
theorem finite_series_iteratedFDeriv
    {f : E → F} {p : FormalMultilinearSeries ℂ E F} {a : E} {N : ℕ}
    {r : ℝ≥0∞} (hp : HasFiniteFPowerSeriesOnBall f p a N r) (k : ℕ) :
    HasFiniteFPowerSeriesOnBall (iteratedFDeriv ℂ k f)
      (p.iteratedFDerivSeries k) a (N-k) r := by
  induction k with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℂ E F).symm
      |>.toContinuousLinearEquiv.toContinuousLinearMap.comp_hasFiniteFPowerSeriesOnBall hp
  | succ k ih =>
    rw [iteratedFDeriv_succ_eq_comp_left]
    have hd := ih.fderiv'
    have he : N-k-1=N-(k+1) := by omega
    rw [he] at hd
    exact (continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (k+1) => E) F).symm
      |>.toContinuousLinearEquiv.toContinuousLinearMap.comp_hasFiniteFPowerSeriesOnBall hd

theorem actual_series_iteratedFDeriv
    {f : E → F} {p : FormalMultilinearSeries ℂ E F} {a : E}
    {r : ℝ≥0∞} (hp : HasFPowerSeriesOnBall f p a r) (k : ℕ) :
    HasFPowerSeriesOnBall (iteratedFDeriv ℂ k f)
      (p.iteratedFDerivSeries k) a r := by
  induction k with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℂ E F).symm
      |>.toContinuousLinearEquiv.toContinuousLinearMap.comp_hasFPowerSeriesOnBall hp
  | succ k ih =>
    rw [iteratedFDeriv_succ_eq_comp_left]
    exact (continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (k+1) => E) F).symm
      |>.toContinuousLinearEquiv.toContinuousLinearMap.comp_hasFPowerSeriesOnBall ih.fderiv

theorem complexTaylorPolynomial_iteratedFDeriv
    {f : E → F} {p : FormalMultilinearSeries ℂ E F} {a : E}
    (hp : HasFPowerSeriesAt f p a) (N k : ℕ) (q : E) :
    iteratedFDeriv ℂ k (complexTaylorPolynomial f a N) q =
      complexTaylorPolynomial (iteratedFDeriv ℂ k f) a (N-k) q := by
  have hfinite := finite_series_iteratedFDeriv
    (complexTaylorPolynomial_has_finite_series hp N) k
  rw [hfinite.eq_partialSum' q (by simp) (N-k) le_rfl]
  obtain ⟨r,hpball⟩ := hp
  have hactual := (actual_series_iteratedFDeriv hpball k).hasFPowerSeriesAt
  simp only [FormalMultilinearSeries.partialSum,complexTaylorPolynomial]
  apply Finset.sum_congr rfl
  intro n hn
  have hnk : n+k<N := by have := Finset.mem_range.mp hn; omega
  rw [iterated_series_coefficient_congr (complexTaylorFiniteSeries p N) p k n
    (by simp only [complexTaylorFiniteSeries,ite_eq_left hnk])]
  exact actual_power_series_diagonal_coefficient hactual n (q-a)

#print axioms complexTaylorPolynomial_iteratedFDeriv
def CoupledComplexDistanceTaylorData (f : E → F) (a : E) (R C : ℝ) : Prop :=
  (∀ N : ℕ, CPolynomialOn ℂ (complexTaylorPolynomial f a N) Set.univ) ∧
  (∀ N k : ℕ, ∀ q : E,
    iteratedFDeriv ℂ k (complexTaylorPolynomial f a N) q =
      complexTaylorPolynomial (iteratedFDeriv ℂ k f) a (N-k) q) ∧
  (∀ N : ℕ, ∀ q : E, ‖q-a‖<R/4 →
    ‖f q-complexTaylorPolynomial f a N q‖≤(3/2)*C*(1/3:ℝ)^N ∧
    ∀ k : ℕ, ‖iteratedFDeriv ℂ k f q-
      iteratedFDeriv ℂ k (complexTaylorPolynomial f a N) q‖≤
      3*C*(2*Real.exp 1/R)^k*(k.factorial:ℝ)*(2/3:ℝ)^(N-k))

theorem actual_taylor_data_coupled
    {f : E → F} {a : E} {R C : ℝ} (hdata : ComplexDistanceTaylorData f a R C) :
    CoupledComplexDistanceTaylorData f a R C := by
  obtain ⟨p,hp,_⟩ := hdata.1
  refine ⟨?_,complexTaylorPolynomial_iteratedFDeriv hp,?_⟩
  · intro N q hq
    exact (complexTaylorPolynomial_has_finite_series hp N).cpolynomialAt_of_mem (by simp)
  · intro N q hq
    refine ⟨(hdata.2.1 q hq).2 N,?_⟩
    intro k
    rw [complexTaylorPolynomial_iteratedFDeriv hp]
    exact (hdata.2.2 k q hq).2 (N-k)

omit [CompleteSpace F] in
theorem coupled_taylor_joint_value_gradient_hessian_error
    {f : E → F} {a q : E} {R C : ℝ}
    (hdata : CoupledComplexDistanceTaylorData f a R C)
    (hq : ‖q-a‖<R/4) (N : ℕ) :
    ‖f q-complexTaylorPolynomial f a N q‖≤(3/2)*C*(1/3:ℝ)^N ∧
    ‖iteratedFDeriv ℂ 1 f q-
      iteratedFDeriv ℂ 1 (complexTaylorPolynomial f a N) q‖≤
      3*C*(2*Real.exp 1/R)*(2/3:ℝ)^(N-1) ∧
    ‖iteratedFDeriv ℂ 2 f q-
      iteratedFDeriv ℂ 2 (complexTaylorPolynomial f a N) q‖≤
      6*C*(2*Real.exp 1/R)^2*(2/3:ℝ)^(N-2) := by
  have hh := hdata.2.2 N q hq
  refine ⟨hh.1,?_,?_⟩
  · simpa only [pow_one,Nat.factorial_one,Nat.cast_one,mul_one] using hh.2 1
  · convert hh.2 2 using 1; norm_num; ring

#print axioms actual_taylor_data_coupled
#print axioms coupled_taylor_joint_value_gradient_hessian_error
end ManyBody.S8