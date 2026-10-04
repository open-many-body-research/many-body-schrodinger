import WeakFactorialJetTests_v1
import ProductWeakFiniteFamilyUnique_v1

/-! Canonical global weak H2 jets agree locally with any genuine natural
weak derivative family of the same local input. The proof compares literal
coordinate weak chains, so no pointwise mixed compatibility or smoothness
of either input is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem weakFactorialJet_ae_local_of_natural_chains
    (U : Lp ℂ 2 (volume : Measure (Space (Fin 3))))
    (d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))) (e : Jet (Fin 3))
    (hd : ∀ v, WeakProductL2Directional U (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {V : Set (Space (Fin 3))} (hV : IsOpen V)
    (G : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ)
    (h0 : ∀ᵐ p ∂volume, p ∈ V → U p = G 0 0 p)
    (hY : ∀ a b i, (∑ k,a k)+(∑ j,b j) < 2 →
      ProductLocalWeakDirectional V (G a b) (G (a+Pi.single i 1) b) (yDir i))
    (hT : ∀ a b j, (∑ i,a i)+(∑ k,b k) < 2 →
      ProductLocalWeakDirectional V (G a b) (G a (b+Pi.single j 1)) (tDir j))
    (a : Fin 4 → ℕ) (b : Fin 3 → ℕ) (hab : (∑ i,a i)+(∑ j,b j) ≤ 2) :
    ∀ᵐ p ∂volume, p ∈ V → weakFactorialJet U d e a b p = G a b p := by
  have h := product_local_weak_word_families_unique hV productCoordinateDirection
    (fun w => (weakCoordinateJet U d e w : Space (Fin 3) → ℂ))
    (mixedMultiIndexWordFamily G)
    (by simpa only [weakCoordinateJet,mixedMultiIndexWordFamily_nil] using h0)
    (fun w i hw => ProductLocalWeakDirectional.of_global
      (weakCoordinateJet_directional U d e hd he w hw i) V)
    (mixedMultiIndexWordFamily_localD G hY hT)
    (mixedMultiIndexWord a b) (by rwa [mixedMultiIndexWord_length])
  simpa only [weakFactorialJet,mixedMultiIndexWordFamily_canonical] using h

end TheoremT.Continuum.WeakGrushin
