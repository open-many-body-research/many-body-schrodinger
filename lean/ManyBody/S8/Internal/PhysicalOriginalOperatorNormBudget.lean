import ManyBody.S8.Internal.PhysicalDescentOperatorNormBounds
/-! Literal original-scale Frechet operator norm budgets. The A constant is
retained exactly at order zero; scaling is proved on every real direction. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace ManyBody.S8
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin

theorem physical_iteratedFDeriv_rescaled_collision_A
    (a : Position × Position → ℂ) (u0 : ℂ) {ε : ℝ} (hε : 0<ε)
    (p : Position × Position) (n : ℕ) (v : Fin n → Position × Position)
    (ha : AnalyticAt ℝ a (ε⁻¹ • p)) :
    iteratedFDeriv ℝ n (physicalRescaledCollisionA ε u0 a) p v=
      (if n=0 then u0 else 0)+
      (ε*(ε⁻¹)^n) • iteratedFDeriv ℝ n a (ε⁻¹ • p) v := by
  have hscale : AnalyticAt ℝ (fun q : Position × Position => ε⁻¹ • q) p := by
    exact (analyticAt_const : AnalyticAt ℝ (fun _ : Position × Position => ε⁻¹) p).smul analyticAt_id
  have has : AnalyticAt ℝ (fun q : Position × Position => a (ε⁻¹ • q)) p :=
    AnalyticAt.comp ha hscale
  have hfun : physicalRescaledCollisionA ε u0 a=
      (fun _ : Position × Position => u0)+ε • (fun q => a (ε⁻¹ • q)) := by
    funext q
    simp [physicalRescaledCollisionA,Complex.real_smul]
  have hconst (j : ℕ) (w : Fin j → Position × Position) :
      iteratedFDeriv ℝ j (fun _ : Position × Position => u0) p w=if j=0 then u0 else 0 := by
    cases j
    · simp only [ite_true,iteratedFDeriv_zero_apply]
    · simp only [Nat.succ_ne_zero,ite_false,iteratedFDeriv_succ_const,Pi.zero_apply,zero_apply]
  rw [hfun,iteratedFDeriv_add_apply (f:=fun _ : Position × Position => u0)
    (g:=ε • (fun q => a (ε⁻¹ • q))) contDiffAt_const (has.contDiffAt.const_smul ε)]
  rw [iteratedFDeriv_const_smul_apply (a:=ε) (f:=fun q => a (ε⁻¹ • q)) has.contDiffAt]
  simp only [add_apply,smul_apply]
  rw [physical_iteratedFDeriv_inverse_scale a hε p n v,smul_smul,hconst]

def PhysicalOriginalCollisionOperatorAtBudget
    (f : Space (Fin 3) → ℂ) (t0 : Position) (ε : ℝ) (u0 : ℂ)
    (m M A Csrc CH12 : ℝ) (ψ : SpinSpace 2) (p : Position × Position) : Prop :=
  ∀ n : ℕ,
    ‖iteratedFDeriv ℝ n (physicalRescaledCollisionA ε u0 (physicalDescentAReal f t0)) p‖≤
      ((if n=0 then m else 0)+ε*(ε⁻¹)^n*physicalKSDescentOperatorBudget M A Csrc CH12 n)*‖ψ‖ ∧
    ‖iteratedFDeriv ℝ n (physicalRescaledCollisionB ε (physicalDescentBReal f t0)) p‖≤
      ((ε⁻¹)^n*(32*(7*physicalKSPointwiseRate M A)^2)*
        physicalKSDescentOperatorBudget M A Csrc CH12 n)*‖ψ‖

theorem physical_original_collision_operator_at_budget
    {f : Space (Fin 3) → ℂ} {v : Position → Position → ℂ} {t0 : Position}
    {ε m M A Csrc CH12 : ℝ} {u0 : ℂ} {ψ : SpinSpace 2}
    (hε : 0<ε) (hm : 0≤m) (hA : 1≤A) (hsrc : 0≤Csrc) (hH12 : 0≤CH12)
    (hdata : PhysicalKSBoxOriginalNormAnalyticDerivativeData f v t0 M A Csrc CH12 ψ)
    (hbal : ∀ j γ e, e∈(ksRealPolynomialToSpinor
      (physicalKSTaylorEvenSpectatorFamily f (0,t0) j γ)).support → e 0+e 1=e 2+e 3)
    (hu0 : ‖u0‖≤m*‖ψ‖) (p : Position × Position)
    (hX : (32*(7*physicalKSPointwiseRate M A)^2)*‖(ε⁻¹ • p).1‖≤1/4)
    (hT : (7*physicalKSPointwiseRate M A)*‖(ε⁻¹ • p).2-t0‖≤1/4) :
    PhysicalOriginalCollisionOperatorAtBudget f t0 ε u0 m M A Csrc CH12 ψ p := by
  let q := ε⁻¹ • p
  let D : ℝ := 32*(7*physicalKSPointwiseRate M A)^2
  have hD : 0≤D := by dsimp [D]; positivity
  have hS : 0<7*physicalKSPointwiseRate M A := mul_pos (by norm_num) (physicalKSPointwiseRate_pos hA)
  have hF0 : 0≤Csrc*‖ψ‖ := mul_nonneg hsrc (norm_nonneg _)
  have hXc := (mul_le_mul_of_nonneg_left
    (physicalComplexCoordinatesCLM_left_norm_le (q.1,q.2-t0)) hD).trans hX
  have hTc := (mul_le_mul_of_nonneg_left
    (physicalComplexCoordinatesCLM_right_norm_le (q.1,q.2-t0)) hS.le).trans hT
  have hmem : D*‖fun i : Fin 3 => physicalComplexCoordinatesAt t0 q (.inl i)‖<1 ∧
      (7*physicalKSPointwiseRate M A)*‖fun i : Fin 3 => physicalComplexCoordinatesAt t0 q (.inr i)‖<1 :=
    ⟨lt_of_le_of_lt hXc (by norm_num),lt_of_le_of_lt hTc (by norm_num)⟩
  have ha : AnalyticAt ℝ (physicalDescentAReal f t0) q :=
    AnalyticAt.comp (f:=physicalComplexCoordinatesAt t0) (g:=physicalKSAnalyticDescentA f t0)
      ((hdata.1.1.2.1 _ hmem).restrictScalars (𝕜:=ℝ)) (physicalComplexCoordinatesAt_analytic t0 q)
  intro n
  let Q := physicalKSDescentOperatorBudget M A Csrc CH12 n
  have hQ : 0≤Q := physicalKSDescentOperatorBudget_nonneg hA hsrc n
  have hb := physical_descent_operator_norm_of_balanced hdata.1.1.1 hA hF0 hbal q hX hT n
  rw [physicalKSDescentOperatorBudget_original_norm ψ M A Csrc CH12 hH12 n] at hb
  have hcoeff : 0≤ε*(ε⁻¹)^n := mul_nonneg hε.le (pow_nonneg (inv_nonneg.mpr hε.le) n)
  have hinv : 0≤(ε⁻¹)^n := pow_nonneg (inv_nonneg.mpr hε.le) n
  constructor
  · apply (iteratedFDeriv ℝ n (physicalRescaledCollisionA ε u0 (physicalDescentAReal f t0)) p).opNorm_le_bound (by split_ifs <;> positivity)
    intro w
    have hprod : 0≤∏ i,‖w i‖ := Finset.prod_nonneg (fun _ _ => norm_nonneg _)
    have hconst : ‖if n=0 then u0 else 0‖≤((if n=0 then m else 0)*‖ψ‖)*∏ i,‖w i‖ := by
      cases n
      · simpa using hu0
      · simp
    rw [physical_iteratedFDeriv_rescaled_collision_A _ _ hε p n w ha]
    calc
      _≤‖if n=0 then u0 else 0‖+‖(ε*(ε⁻¹)^n) • iteratedFDeriv ℝ n (physicalDescentAReal f t0) q w‖ :=
        norm_add_le _ _
      _=‖if n=0 then u0 else 0‖+(ε*(ε⁻¹)^n)*‖iteratedFDeriv ℝ n (physicalDescentAReal f t0) q w‖ := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hcoeff]
      _≤((if n=0 then m else 0)*‖ψ‖)*∏ i,‖w i‖+
          (ε*(ε⁻¹)^n)*((Q*‖ψ‖)*∏ i,‖w i‖) := by
        apply add_le_add hconst
        apply mul_le_mul_of_nonneg_left _ hcoeff
        exact ((iteratedFDeriv ℝ n (physicalDescentAReal f t0) q).le_opNorm w).trans
          (mul_le_mul_of_nonneg_right hb.1 hprod)
      _=(((if n=0 then m else 0)+ε*(ε⁻¹)^n*Q)*‖ψ‖)*∏ i,‖w i‖ := by ring
  · apply (iteratedFDeriv ℝ n (physicalRescaledCollisionB ε (physicalDescentBReal f t0)) p).opNorm_le_bound (by positivity)
    intro w
    change ‖iteratedFDeriv ℝ n (fun z => physicalDescentBReal f t0 (ε⁻¹ • z)) p w‖≤_
    rw [physical_iteratedFDeriv_inverse_scale (physicalDescentBReal f t0) hε p n w,
      norm_smul,Real.norm_eq_abs,abs_of_nonneg hinv]
    have hprod : 0≤∏ i,‖w i‖ := Finset.prod_nonneg (fun _ _ => norm_nonneg _)
    calc
      _≤(ε⁻¹)^n*((D*(Q*‖ψ‖))*∏ i,‖w i‖) := by
        apply mul_le_mul_of_nonneg_left _ hinv
        exact ((iteratedFDeriv ℝ n (physicalDescentBReal f t0) q).le_opNorm w).trans
          (mul_le_mul_of_nonneg_right hb.2 hprod)
      _=(((ε⁻¹)^n*D*Q)*‖ψ‖)*∏ i,‖w i‖ := by ring

#print axioms physical_iteratedFDeriv_rescaled_collision_A
#print axioms physical_original_collision_operator_at_budget
end ManyBody.S8