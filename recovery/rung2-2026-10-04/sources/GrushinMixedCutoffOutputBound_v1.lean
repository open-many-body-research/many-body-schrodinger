import WeakGrushinMixedCutoffEquation_v1
import RestrictedL2OutputNorm_v1
import GrushinDifferentiatedSourceBound_v1
import GrushinFactorialIndexedCutoffBound_v1
import GrushinFactorialUnweightedComponent_v1

/-! The actual compact mixed-derivative output estimate underlying R18.
The source is constructed from the original weak PDE, genuine finite weak
jets, ordinary coefficient derivatives, and lower weighted norms. This unit
supplies the operator-output side; the compact maximal estimate and plateau
comparison are separate and do not occur as hidden premises. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem factorial_mixed_cutoff_output_bound
    (a : Space (Fin 3)) (ha : a.1 = 0) (c : ℝ)
    {aY aT ρ t e C1 C2 : ℝ} (he : 0 < e) (hte : t+e ≤ ρ)
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
    (W : (Fin 4 → ℕ) → (Fin 3 → ℕ) → FactorialOuterIndex →
      Lp ℂ 2 (volume.restrict (rectangularOpenBox a (aY-t) (aT-t))))
    (N : ℕ → ℝ) (hN0 : ∀ k, 0 ≤ N k)
    (hW : ∀ α β, factorialMultiDerivativeCost α β ≤ r-1 → FactorialShiftedOuterL2Rep F W α β)
    (hN : ∀ k, k ≤ r-1 → ∀ α β, factorialMultiDerivativeCost α β ≤ k → factorialOuterNorm (W α β) ≤ N k)
    (B : Space (Fin 3) → ℝ) (src : Space (Fin 3) → ℂ)
    (hB : ContDiffOn ℝ ∞ B (rectangularOpenBox a (aY-t) (aT-t)))
    (hsrc : ContDiffOn ℝ ∞ src (rectangularOpenBox a (aY-t) (aT-t)))
    (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hBb : ∀ w, w.length ≤ r → ∀ p ∈ rectangularOpenBox a (aY-t) (aT-t),
      |directionalWordDeriv productCoordinateDirection B w p| ≤ M*A^w.length*(w.length.factorial : ℝ))
    (hP : ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ rectangularOpenBox a (aY-t) (aT-t) →
      (∫ p, splitGrushin c oscillatorBasis B φ p • F 0 0 p) = ∫ p,φ p • src p)
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (hc : factorialMultiDerivativeCost α β ≤ r)
    (HS : Lp ℂ 2 (volume.restrict (rectangularOpenBox a (aY-t) (aT-t)))) (S0 : ℝ)
    (hS : HS =ᵐ[volume.restrict (rectangularOpenBox a (aY-t) (aT-t))]
      complexDirectionalWordDeriv productCoordinateDirection src (mixedMultiIndexWord α β))
    (hSn : ‖HS‖ ≤ S0) :
    ∃ U H : Lp ℂ 2 (volume : Measure (Space (Fin 3))),
    ∃ d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3))), ∃ q : Jet (Fin 3),
      U =ᵐ[volume] (fun p => factorialRectCutoff a aY aT t e p • F α β p) ∧
      (∀ v, WeakProductL2Directional U (d v) v) ∧
      (∀ v w, WeakProductL2Directional (d v) (q v w) w) ∧
      (∀ᵐ p ∂volume, p ∉ tsupport (factorialRectCutoff a aY aT t e) → U p = 0) ∧
      H =ᵐ[volume] principal c q ∧
      (∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • U p) = ∫ p, φ p • H p) ∧
      ‖H‖ ≤ S0+
        M*(∑ j ∈ Finset.range r, (r.choose (j+1) : ℝ)*A^(j+1)*((j+1).factorial : ℝ)*N (r-(j+1)))+
        (6*|c| *(r : ℝ)*N (r-1)+3*|c| *((r*(r-1) : ℕ) : ℝ)*N (r-2))+
        M*N (r-1)+
        ((((8/3 : ℝ)*C1)/e)*(8/(aY-ρ)^2+6*|c|)*N (r-1)+
          (((32/9 : ℝ)*(C2+C1^2))/e^2)*(4/(aY-ρ)^2+3*|c|)*N (r-2)) := by
  let Ω := rectangularOpenBox a (aY-t) (aT-t)
  let χ := factorialRectCutoff a aY aT t e
  have hΩ : IsOpen Ω := rectangularOpenBox_isOpen a _ _
  have hab : (∑ i,α i)+(∑ j,β j) ≤ r := by
    unfold factorialMultiDerivativeCost factorialDerivativeCost at hc
    omega
  obtain ⟨hχ,hcχ,hval,_,_,hχΩ⟩ := factorialRectCutoff_geometry a he hte hρy hρt
  obtain ⟨U,H,d,q,hU,hd,hq,hUs,hHq,hformula,hTests⟩ :=
    weak_grushin_mixed_cutoff_equation c hΩ hB hsrc F hF hY hT hP α β hab hχ hcχ hχΩ
  have hBm (w : List (Fin 4 ⊕ Fin 3)) (_ : w.length ≤ r) :
      AEStronglyMeasurable (directionalWordDeriv productCoordinateDirection B w) (volume.restrict Ω) :=
    (directionalWordDeriv_contDiffOn productCoordinateDirection hΩ hB w).continuousOn.aestronglyMeasurable hΩ.measurableSet
  have hBound (w : List (Fin 4 ⊕ Fin 3)) (hw : w.length ≤ r) :
      ∀ᵐ p ∂volume.restrict Ω, |directionalWordDeriv productCoordinateDirection B w p| ≤
        M*A^w.length*(w.length.factorial : ℝ) := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with p hp
    exact hBb w hw p hp
  obtain ⟨HD,hD,hDn⟩ := factorial_differentiated_source_L2 c F W r N hN0 hW hN
    B M A hM hA hBm hBound src α β hc HS S0 hS hSn
  obtain ⟨HF,hf,hfn⟩ := factorial_unweighted_lower_order_L2 F W r (N (r-1)) (by omega)
    hW (hN (r-1) le_rfl) α β hc
  have hgy (i : Fin 4) : AEStronglyMeasurable (F (α+Pi.single i 1) β) (volume.restrict Ω) := by
    apply (hF _ _ ?_).1.aestronglyMeasurable
    simp only [Pi.add_apply,Finset.sum_add_distrib,Pi.single_apply,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    omega
  obtain ⟨HE,hE,hEn⟩ := factorial_indexed_cutoff_error_L2 a ha c he hte hρy hC1 hC2 F W r hr
    (N (r-1)) (N (r-2)) hW (hN (r-1) le_rfl) (hN (r-2) (by omega)) α β hc
    (hF α β (by omega)).1.aestronglyMeasurable hgy
  have hcb : ∀ᵐ p ∂volume.restrict Ω, ‖χ p‖ ≤ 1 :=
    Eventually.of_forall (fun p => by simpa only [χ,Real.norm_eq_abs,abs_of_nonneg (hval p).1] using (hval p).2)
  have hbb : ∀ᵐ p ∂volume.restrict Ω, ‖B p‖ ≤ M := by
    simpa only [directionalWordDeriv,List.length_nil,pow_zero,Nat.factorial_zero,Nat.cast_one,mul_one,Real.norm_eq_abs]
      using hBound [] (by simp)
  have hnorm := restricted_cutoff_output_norm Ω hΩ.measurableSet χ B (F α β)
    (mixedMultiIndexGrushinSource c B F src α β)
    (rawGrushinCutoffError c χ (F α β) (fun i => F (α+Pi.single i 1) β) (fun j => F α (β+Pi.single j 1)))
    (memLp_top_of_bound (hχ.continuous.aestronglyMeasurable) 1 hcb)
    (memLp_top_of_bound (hB.continuousOn.aestronglyMeasurable hΩ.measurableSet) M hbb)
    hcb hbb HF HD HE hf hD hE H hformula
    (fun p hp => image_eq_zero_of_notMem_tsupport (fun ht => hp (hχΩ ht)))
    (fun p hp => rawGrushinCutoffError_zero_off c χ _ _ _ (fun ht => hp (hχΩ ht)))
  refine ⟨U,H,d,q,hU,hd,hq,hUs,hHq,hTests,hnorm.trans ?_⟩
  exact add_le_add (add_le_add hDn (mul_le_mul_of_nonneg_left hfn hM)) hEn

end TheoremT.Continuum.WeakGrushin
