import GrushinMixedCutoffOutputBound_v1
import GrushinFactorialBoxProfile_v1
import GrushinFactorialProfileLowerBudgets_v1
import GrushinFactorialSourceBudget_v1

/-! Actual-profile input to the compact cutoff output estimate. The lower
profile is the finite maximum of actual weighted L2 norms on the current
box. All its representatives and the source representative are constructed.
The source's analytic squared budgets remain explicit data hypotheses. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem factorial_mixed_cutoff_actual_profile_bound
    (a : Space (Fin 3)) (ha : a.1 = 0) (c : ℝ)
    {aY aT ρ t e C1 C2 : ℝ} (he : 0 < e) (ht0 : 0 ≤ t) (hte : t+e ≤ ρ)
    (hρy : ρ < aY) (hρt : ρ < aT)
    (hC1 : ∀ x, |deriv Real.smoothTransition x| ≤ C1)
    (hC2 : ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ C2)
    (r : ℕ) (hr : 2 ≤ r) (V0 : ℝ)
    (F : FactorialRawJetFamily)
    (hF : ∀ α β, (∑ i,α i)+(∑ j,β j) ≤ r+2 →
      RegionL2Budget (F α β) (rectangularOpenBox a (aY-t) (aT-t)) V0)
    (hY : ∀ α β i, (∑ k,α k)+(∑ j,β j) < r+2 →
      ProductLocalWeakDirectional (rectangularOpenBox a (aY-t) (aT-t))
        (F α β) (F (α+Pi.single i 1) β) (yDir i))
    (hT : ∀ α β j, (∑ i,α i)+(∑ k,β k) < r+2 →
      ProductLocalWeakDirectional (rectangularOpenBox a (aY-t) (aT-t))
        (F α β) (F α (β+Pi.single j 1)) (tDir j))
    (B : Space (Fin 3) → ℝ) (src : Space (Fin 3) → ℂ)
    (hB : ContDiffOn ℝ ∞ B (rectangularOpenBox a (aY-t) (aT-t)))
    (hsrc : ContDiffOn ℝ ∞ src (rectangularOpenBox a (aY-t) (aT-t)))
    (M A F0 : ℝ) (hM : 0 ≤ M) (hA : 1 ≤ A) (hF0 : 0 ≤ F0)
    (hBb : ∀ w, w.length ≤ r → ∀ p ∈ rectangularOpenBox a (aY-t) (aT-t),
      |directionalWordDeriv productCoordinateDirection B w p| ≤ M*A^w.length*(w.length.factorial : ℝ))
    (hP : ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ rectangularOpenBox a (aY-t) (aT-t) →
      (∫ p, splitGrushin c oscillatorBasis B φ p • F 0 0 p) = ∫ p,φ p • src p)
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (hc : factorialMultiDerivativeCost α β ≤ r)
    (hSourceBudget : ∀ w : List (Fin 4 ⊕ Fin 3),
      RegionL2Budget (complexDirectionalWordDeriv productCoordinateDirection src w)
        (rectangularOpenBox a aY aT) ((F0*A^w.length*(w.length.factorial : ℝ))^2)) :
    ∃ U H : Lp ℂ 2 (volume : Measure (Space (Fin 3))),
    ∃ d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3))), ∃ q : Jet (Fin 3),
      U =ᵐ[volume] (fun p => factorialRectCutoff a aY aT t e p • F α β p) ∧
      (∀ v, WeakProductL2Directional U (d v) v) ∧
      (∀ v w, WeakProductL2Directional (d v) (q v w) w) ∧
      (∀ᵐ p ∂volume, p ∉ tsupport (factorialRectCutoff a aY aT t e) → U p = 0) ∧
      H =ᵐ[volume] principal c q ∧
      (∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • U p) = ∫ p, φ p • H p) ∧
      ‖H‖ ≤ F0*A^r*(r.factorial : ℝ)+
        M*(∑ j ∈ Finset.range r, (r.choose (j+1) : ℝ)*A^(j+1)*((j+1).factorial : ℝ)*(factorialBoxProfile F a aY aT (r-(j+1)) t))+
        (6*|c| *(r : ℝ)*(factorialBoxProfile F a aY aT (r-1) t)+3*|c| *((r*(r-1) : ℕ) : ℝ)*(factorialBoxProfile F a aY aT (r-2) t))+
        M*(factorialBoxProfile F a aY aT (r-1) t)+
        ((((8/3 : ℝ)*C1)/e)*(8/(aY-ρ)^2+6*|c|)*(factorialBoxProfile F a aY aT (r-1) t)+
          (((32/9 : ℝ)*(C2+C1^2))/e^2)*(4/(aY-ρ)^2+3*|c|)*(factorialBoxProfile F a aY aT (r-2) t)) := by
  let Ω := rectangularOpenBox a (aY-t) (aT-t)
  have hYwidth : 0 ≤ aY-t := by linarith
  have hTwidth : 0 ≤ aT-t := by linarith
  have hmem : FactorialLocalMemLp F Ω (r-1) :=
    factorialLocalMemLp_rectangular F a hYwidth hTwidth (by omega)
      (fun α β hdegree => (hF α β hdegree).1)
  obtain ⟨W,hW⟩ := factorialLocalProfile_coherent_lower_representatives hmem
  have hsub : Ω ⊆ rectangularOpenBox a aY aT := by
    simpa only [Ω,factorialProfileBox,sub_zero] using factorialProfileBox_antitone a aY aT ht0
  obtain ⟨HS,hHS,hHSn⟩ := factorial_source_budget_representative hsub src hF0 hA
    hSourceBudget α β hc
  simpa only [factorialBoxProfile,factorialProfileBox,Ω] using
    factorial_mixed_cutoff_output_bound a ha c he hte hρy hρt hC1 hC2 r hr V0 F
      hF hY hT W (fun k => factorialLocalProfile F Ω k)
      (fun k => factorialLocalProfile_nonneg F Ω k)
      (fun α β hcost => (hW (r-1) le_rfl α β hcost).1)
      (fun k hk α β hcost => (hW k hk α β hcost).2.2)
      B src hB hsrc M A hM (zero_le_one.trans hA) hBb hP α β hc
      HS (F0*A^r*(r.factorial : ℝ)) hHS hHSn

end TheoremT.Continuum.WeakGrushin
