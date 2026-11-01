import ProductLocalWeakWordsPhysicalRepresentative_v1
import FactorialProfilePointwiseWordBudgets_v1

/-! Actual R24 profile-to-pointwise embedding for one genuine all-order weak
mixed jet family. The physical-product representative is smooth, all its
coordinate words are identified, and the reserve is exactly k+11. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem grushin_actual_profile_smooth_representative
    {Ω O ΩN : Set (Space (Fin 3))} (hΩ : IsOpen Ω) (hO : IsOpen O)
    {χ : Space (Fin 3) → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ Ω)
    (hpχ : ∀ p ∈ O, χ p = 1)
    {a b : Fin 7 → ℝ} (hab : ∀ i, a i < b i)
    (hKO : MapsTo sevenToProduct (tensorClosedBox7 a b) O)
    (hKN : MapsTo sevenToProduct (tensorClosedBox7 a b) ΩN)
    {U : Set (Fin 7 → ℝ)} (hU : IsOpen U) (hUK : U ⊆ tensorClosedBox7 a b)
    (F : FactorialRawJetFamily)
    (hL2 : ∀ α β, ProductLocallyL2On (F α β) Ω)
    (hY : ∀ α β i, ProductLocalWeakDirectional Ω (F α β) (F (α+Pi.single i 1) β) (yDir i))
    (hT : ∀ α β j, ProductLocalWeakDirectional Ω (F α β) (F α (β+Pi.single j 1)) (tDir j))
    (hN : ∀ r, FactorialLocalMemLp F ΩN r) :
    ∃ f : Space (Fin 3) → ℂ,
      ContDiffOn ℝ ∞ f (Set.image sevenToProduct U) ∧
      F 0 0 =ᵐ[volume.restrict (Set.image sevenToProduct U)] f ∧
      (∀ w, mixedMultiIndexWordFamily F w =ᵐ[volume.restrict (Set.image sevenToProduct U)]
        complexDirectionalWordDeriv productCoordinateDirection f w) ∧
      (∀ w p, p ∈ Set.image sevenToProduct U →
        ‖complexDirectionalWordDeriv productCoordinateDirection f w p‖ ≤
          boxEvaluationConstant a b * factorialLocalProfile F ΩN (w.length+11)) := by
  have hD (w : List (Fin 4 ⊕ Fin 3)) (i : Fin 4 ⊕ Fin 3) :
      ProductLocalWeakDirectional Ω (mixedMultiIndexWordFamily F w)
        (mixedMultiIndexWordFamily F (i :: w)) (productCoordinateDirection i) :=
    mixedMultiIndexWordFamily_localD F (m := w.length+1)
      (fun α β i _ => hY α β i) (fun α β j _ => hT α β j) w i (Nat.lt_succ_self _)
  obtain ⟨f,hfs,hfw,hfb⟩ := product_local_weak_words_physical_quantitative_representative
    hΩ hO hχ hcχ hsχ hpχ hab hKO hKN hU hUK (mixedMultiIndexWordFamily F)
    (fun w => hL2 _ _) hD (factorial_profile_word_memLp hN)
    (fun w => factorialLocalProfile F ΩN (w.length+11))
    (fun w => factorialLocalProfile_nonneg F ΩN _) (fun w s => (factorial_profile_mixed_subset_word_norms hN w s).2)
  refine ⟨f,hfs,?_,hfw,?_⟩
  · simpa only [mixedMultiIndexWordFamily_nil,complexDirectionalWordDeriv] using hfw []
  · intro w p hp
    simpa only [List.length_map] using hfb w p hp

end TheoremT.Continuum.WeakGrushin
