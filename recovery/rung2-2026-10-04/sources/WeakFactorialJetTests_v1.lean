import WeakFactorialJet_v1
import ProductCoordinateWeakWordTests_v1
import LocalProductDirectionalWeakUnique_v1

/-! Literal compact-test identities for the canonical weak factorial jet.
The fields are derivatives of the same L2 input, with the exact canonical
coordinate word and distributional sign. No smooth input or derivative
bound is assumed; the order limit is exactly two. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem weakCoordinateJet_directional
    (f : Lp ℂ 2 (volume : Measure (Space (Fin 3))))
    (d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))) (e : Jet (Fin 3))
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    (w : List (Fin 4 ⊕ Fin 3)) (hw : w.length < 2) (i : Fin 4 ⊕ Fin 3) :
    WeakProductL2Directional (weakCoordinateJet f d e w)
      (weakCoordinateJet f d e (i :: w)) (productCoordinateDirection i) := by
  cases w with
  | nil => exact hd (productCoordinateDirection i)
  | cons j w =>
    cases w with
    | nil => exact he (productCoordinateDirection j) (productCoordinateDirection i)
    | cons k w => simp only [List.length_cons] at hw; omega

theorem weakCoordinateJet_test_identity
    (f : Lp ℂ 2 (volume : Measure (Space (Fin 3))))
    (d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))) (e : Jet (Fin 3))
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    (w : List (Fin 4 ⊕ Fin 3)) (hw : w.length ≤ 2)
    {φ : Space (Fin 3) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ p, φ p • weakCoordinateJet f d e w p) =
      ((-1 : ℝ)^w.length) • (∫ p, productCoordinateTestWord w φ p • f p) := by
  exact product_coordinate_family_test_identity
    (fun w => (weakCoordinateJet f d e w : Space (Fin 3) → ℂ)) rfl
    (fun w i hw => ProductLocalWeakDirectional.of_global (weakCoordinateJet_directional f d e hd he w hw i) Set.univ)
    w hw hφ hc (Set.subset_univ _)

theorem weakCoordinateJet_tests_integrable
    (f : Lp ℂ 2 (volume : Measure (Space (Fin 3))))
    (d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))) (e : Jet (Fin 3))
    (w : List (Fin 4 ⊕ Fin 3))
    {φ : Space (Fin 3) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Integrable (fun p => φ p • weakCoordinateJet f d e w p) ∧
      Integrable (fun p => productCoordinateTestWord w φ p • f p) := by
  exact ⟨((Lp.memLp (weakCoordinateJet f d e w)).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      hφ.continuous hc,
    ((Lp.memLp f).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      (productCoordinateTestWord_contDiff w hφ).continuous
      (productCoordinateTestWord_compact w hc)⟩

theorem weakFactorialJet_tests
    (f : Lp ℂ 2 (volume : Measure (Space (Fin 3))))
    (d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))) (e : Jet (Fin 3))
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (horder : (∑ i, α i)+(∑ j, β j) ≤ 2)
    {φ : Space (Fin 3) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Integrable (fun p => φ p • weakFactorialJet f d e α β p) ∧
    Integrable (fun p => productCoordinateTestWord (mixedMultiIndexWord α β) φ p • f p) ∧
    (∫ p, φ p • weakFactorialJet f d e α β p) =
      ((-1 : ℝ)^((∑ i, α i)+(∑ j, β j))) •
        (∫ p, productCoordinateTestWord (mixedMultiIndexWord α β) φ p • f p) := by
  have hi := weakCoordinateJet_tests_integrable f d e (mixedMultiIndexWord α β) hφ hc
  have ht := weakCoordinateJet_test_identity f d e hd he (mixedMultiIndexWord α β)
    (by rwa [mixedMultiIndexWord_length]) hφ hc
  exact ⟨hi.1,hi.2,by simpa only [weakFactorialJet,mixedMultiIndexWord_length] using ht⟩

theorem weakFactorialJet_ae_eq_local_of_tests
    (f : Lp ℂ 2 (volume : Measure (Space (Fin 3))))
    (d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))) (e : Jet (Fin 3))
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (horder : (∑ i, α i)+(∑ j, β j) ≤ 2)
    {Ω : Set (Space (Fin 3))} (hΩ : IsOpen Ω)
    {D : Space (Fin 3) → ℂ} (hD : ProductLocallyL2On D Ω)
    (hTest : ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, φ p • D p) = ((-1 : ℝ)^((∑ i, α i)+(∑ j, β j))) •
        (∫ p, productCoordinateTestWord (mixedMultiIndexWord α β) φ p • f p)) :
    ∀ᵐ p ∂volume, p ∈ Ω → D p = weakFactorialJet f d e α β p := by
  have hl : LocallyIntegrableOn (fun p => D p - weakFactorialJet f d e α β p) Ω volume :=
    (productLocallyL2On_locallyIntegrableOn hΩ hD).sub
      (((Lp.memLp (weakFactorialJet f d e α β)).locallyIntegrable (by norm_num)).locallyIntegrableOn Ω)
  have hz := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hl (fun φ hφ hc hs => by
    have hu := weakFactorialJet_tests f d e hd he α β horder hφ hc
    have hdi := product_raw_locallyL2_compact_smul_integrable hD hφ.continuous hc hs
    simp only [smul_sub]
    rw [integral_sub hdi hu.1,hTest φ hφ hc hs,hu.2.2,sub_self])
  filter_upwards [hz] with p hp hin
  exact sub_eq_zero.mp (hp hin)

end TheoremT.Continuum.WeakGrushin
