import GrushinMixedCutoffActualProfile_v1
import WeakFactorialPlateauOuterBound_v1
import GrushinFactorialMaximalGeometry_v1
import GrushinFactorialProfileUpperBound_v1

/-! The localized estimate for the literal solution profile. Genuine finite
weak jets and the original equation suffice: the compact cutoff, its H2
jets, its output and the inner comparison are all constructed. Constants
depend on geometry and coefficients, never on derivative order or gap. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
set_option maxRecDepth 8192
namespace TheoremT.Continuum.WeakGrushin

def factorialProfileGraphConstant (c aY : ℝ) : ℝ :=
  498*(max 1 (2*aY))^2*(4*aY^2+2*aY+2+2/c)

def factorialProfileCutoffFirst (c aY ρ C1 : ℝ) : ℝ :=
  ((8/3 : ℝ)*C1)*(8/(aY-ρ)^2+6*|c|)

def factorialProfileCutoffSecond (c aY ρ C1 C2 : ℝ) : ℝ :=
  ((32/9 : ℝ)*(C2+C1^2))*(4/(aY-ρ)^2+3*|c|)

theorem factorial_actual_profile_localized_bound
    (a : Space (Fin 3)) (ha : a.1 = 0) (c : ℝ) (hcpos : 0 < c)
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
    (hSourceBudget : ∀ w : List (Fin 4 ⊕ Fin 3),
      RegionL2Budget (complexDirectionalWordDeriv productCoordinateDirection src w)
        (rectangularOpenBox a aY aT) ((F0*A^w.length*(w.length.factorial : ℝ))^2)) :
    factorialBoxProfile F a aY aT r (t+e) ≤ factorialProfileGraphConstant c aY *
      (F0*A^r*(r.factorial : ℝ)+
        M*(∑ j ∈ Finset.range r, (r.choose (j+1) : ℝ)*A^(j+1)*((j+1).factorial : ℝ)*(factorialBoxProfile F a aY aT (r-(j+1)) t))+
        (6*|c| *(r : ℝ)*(factorialBoxProfile F a aY aT (r-1) t)+3*|c| *((r*(r-1) : ℕ) : ℝ)*(factorialBoxProfile F a aY aT (r-2) t))+
        M*(factorialBoxProfile F a aY aT (r-1) t)+
        ((((8/3 : ℝ)*C1)/e)*(8/(aY-ρ)^2+6*|c|)*(factorialBoxProfile F a aY aT (r-1) t)+
          (((32/9 : ℝ)*(C2+C1^2))/e^2)*(4/(aY-ρ)^2+3*|c|)*(factorialBoxProfile F a aY aT (r-2) t))) := by
  apply factorialLocalProfile_le_of_outerNorm_le
  intro α β hc
  obtain ⟨U,H,d,q,hU,hd,hq,hs,hprincipal,hPU,hHbound⟩ :=
    factorial_mixed_cutoff_actual_profile_bound a ha c he ht0 hte hρy hρt
      hC1 hC2 r hr V0 F hF hY hT B src hB hsrc M A F0 hM hA hF0 hBb hP α β hc hSourceBudget
  obtain ⟨hχ,hcompact,hval,hplateau,hclosed,hopen⟩ :=
    factorialRectCutoff_geometry a he hte hρy hρt
  have hab : (∑ i,α i)+(∑ j,β j) ≤ r :=
    (factorialDerivativeCost_total_le (∑ i,α i) (∑ j,β j)).trans hc
  have hFY : ∀ α' β' i, (∑ k,α' k)+(∑ j,β' j) < 2 →
      ProductLocalWeakDirectional (rectangularOpenBox a (aY-t) (aT-t))
        (F (α+α') (β+β')) (F ((α+α')+Pi.single i 1) (β+β')) (yDir i) := by
    intro α' β' i ho
    apply hY
    simp only [Pi.add_apply,Finset.sum_add_distrib]
    omega
  have hFT : ∀ α' β' j, (∑ i,α' i)+(∑ k,β' k) < 2 →
      ProductLocalWeakDirectional (rectangularOpenBox a (aY-t) (aT-t))
        (F (α+α') (β+β')) (F (α+α') ((β+β')+Pi.single j 1)) (tDir j) := by
    intro α' β' j ho
    apply hT
    simp only [Pi.add_apply,Finset.sum_add_distrib]
    omega
  have hsub : rectangularOpenBox a (aY-(t+e)) (aT-(t+e)) ⊆
      rectangularOpenBox a (aY-t) (aT-t) :=
    factorialProfileBox_antitone a aY aT (by linarith)
  obtain ⟨hR,hS,hK,hsK,hslab,hSK,hplat⟩ :=
    factorialRectCutoff_maximal_geometry a ha ht0 he hte hρy hρt
  have hout := (factorial_local_outer_le_plateau_grushin_output hcpos d q hd hq hK hs hPU
    0 hR (hslab 0) (max 1 (2*aY)) hS hSK
    (rectangularOpenBox_isOpen a _ _) hsub F α β hFY hFT hU hplateau).2
  have hC0 : 0 ≤ factorialProfileGraphConstant c aY := by
    unfold factorialProfileGraphConstant
    positivity
  exact hout.trans (mul_le_mul_of_nonneg_left hHbound hC0)

end TheoremT.Continuum.WeakGrushin
