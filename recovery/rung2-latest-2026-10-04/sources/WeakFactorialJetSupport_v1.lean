import WeakFactorialJetTests_v1
import ProductWeakJetClosedSupport_v1

/-! Original closed-support preservation and global identification of the
canonical order-two jets from local compact tests. The latter only adds
proved support information to local distributional uniqueness. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem weakCoordinateJet_closed_support
    (f : Lp ℂ 2 (volume : Measure (Space (Fin 3))))
    (d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))) (e : Jet (Fin 3))
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {K : Set (Space (Fin 3))} (hK : IsClosed K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0) (w : List (Fin 4 ⊕ Fin 3)) :
    ∀ᵐ p ∂volume, p ∉ K → weakCoordinateJet f d e w p = 0 := by
  cases w with
  | nil => exact hs
  | cons i w =>
    cases w with
    | nil => exact weakProductL2Directional_closed_support (hd _) hK hs
    | cons j w => exact weakProductL2Second_closed_support (hd _) (he _ _) hK hs

theorem weakFactorialJet_closed_support
    (f : Lp ℂ 2 (volume : Measure (Space (Fin 3))))
    (d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))) (e : Jet (Fin 3))
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {K : Set (Space (Fin 3))} (hK : IsClosed K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0) (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) :
    ∀ᵐ p ∂volume, p ∉ K → weakFactorialJet f d e α β p = 0 :=
  weakCoordinateJet_closed_support f d e hd he hK hs _

theorem weakFactorialJet_ae_eq_of_local_tests_support
    (f : Lp ℂ 2 (volume : Measure (Space (Fin 3))))
    (d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))) (e : Jet (Fin 3))
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (horder : (∑ i, α i)+(∑ j, β j) ≤ 2)
    {K Ω : Set (Space (Fin 3))} (hK : IsClosed K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0)
    {D : Space (Fin 3) → ℂ} (hD : ProductLocallyL2On D Ω)
    (hsD : ∀ᵐ p ∂volume, p ∉ K → D p = 0)
    (hTest : ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, φ p • D p) = ((-1 : ℝ)^((∑ i, α i)+(∑ j, β j))) •
        (∫ p, productCoordinateTestWord (mixedMultiIndexWord α β) φ p • f p)) :
    D =ᵐ[volume] (weakFactorialJet f d e α β : Space (Fin 3) → ℂ) := by
  have hl := weakFactorialJet_ae_eq_local_of_tests f d e hd he α β horder hΩ hD hTest
  have hj := weakFactorialJet_closed_support f d e hd he hK hs α β
  filter_upwards [hl,hsD,hj] with p hp hd0 hj0
  by_cases hin : p ∈ Ω
  · exact hp hin
  · have hk : p ∉ K := fun h => hin (hKΩ h)
    rw [hd0 hk,hj0 hk]

end TheoremT.Continuum.WeakGrushin
