import ProductLocalWeakWordsQuantitativeRepresentative_v1
import SevenCoordinateRepresentativeReturn_v1
import ProductSevenPullbackL2Budget_v2

/-! Physical-product endpoint of local all-order weak representative recovery.
The norm inputs are actual restricted product L2 norms on a containing region;
measure-preserving transport and inverse coordinate return are discharged. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum
open WeakGrushin

theorem product_local_weak_words_physical_quantitative_representative
    {Ω O ΩN : Set (Space (Fin 3))} (hΩ : IsOpen Ω) (hO : IsOpen O)
    {χ : Space (Fin 3) → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ Ω)
    (hpχ : ∀ p ∈ O, χ p = 1)
    {a b : Fin 7 → ℝ} (hab : ∀ i, a i < b i)
    (hKO : MapsTo sevenToProduct (tensorClosedBox7 a b) O)
    (hKN : MapsTo sevenToProduct (tensorClosedBox7 a b) ΩN)
    {U : Set (Fin 7 → ℝ)} (hU : IsOpen U) (hUK : U ⊆ tensorClosedBox7 a b)
    (D : List (Fin 4 ⊕ Fin 3) → Space (Fin 3) → ℂ)
    (hL2 : ∀ w, ProductLocallyL2On (D w) Ω)
    (hD : ∀ w i, ProductLocalWeakDirectional Ω (D w) (D (i :: w)) (productCoordinateDirection i))
    (hN : ∀ w, MemLp (D w) 2 (volume.restrict ΩN))
    (M : List (Fin 7) → ℝ) (hM : ∀ w, 0 ≤ M w)
    (hDM : ∀ w s,
      (eLpNorm (D ((canonicalSubsetWord7 s ++ w).map sevenCoordinateEquiv)) 2
        (volume.restrict ΩN)).toReal ≤ M w) :
    ∃ f : Space (Fin 3) → ℂ,
      ContDiffOn ℝ ∞ f (Set.image sevenToProduct U) ∧
      (∀ w, D w =ᵐ[volume.restrict (Set.image sevenToProduct U)]
        complexDirectionalWordDeriv productCoordinateDirection f w) ∧
      (∀ w p, p ∈ Set.image sevenToProduct U →
        ‖complexDirectionalWordDeriv productCoordinateDirection f w p‖ ≤
          boxEvaluationConstant a b * M (w.map sevenCoordinateEquiv.symm)) := by
  have hDM' (w : List (Fin 7)) (s : Finset (Fin 7)) :
      Real.sqrt (∫ x in tensorClosedBox7 a b,
        ‖D ((canonicalSubsetWord7 s ++ w).map sevenCoordinateEquiv) (sevenToProduct x)‖^2) ≤ M w :=
    (seven_coordinate_sqrt_integral_le_eLpNorm hKN (hN _)).trans (hDM w s)
  obtain ⟨g,hgc,hgs,hg0,hgw,hgb⟩ :=
    product_local_weak_words7_quantitative_representative hΩ hO hχ hcχ hsχ hpχ hab hKO hU hUK
      D hL2 hD M hM hDM'
  exact ⟨g ∘ sevenToProduct.symm,
    seven_coordinate_smooth_representative_return hU D g hgs hgw
      (fun w => boxEvaluationConstant a b * M w) hgb⟩

end TheoremT.Continuum
