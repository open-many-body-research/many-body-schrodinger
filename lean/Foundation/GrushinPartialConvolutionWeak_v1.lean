import PartialSpectatorAETestPairing_v1
import GrushinTestTranslation_v1
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ContDiff
namespace TheoremT.Continuum
variable {T : Type*} [NormedAddCommGroup T] [InnerProductSpace ℝ T]
  [FiniteDimensional ℝ T] [MeasurableSpace T] [BorelSpace T]
variable {ι : Type*} [Fintype ι]

theorem splitGrushin_partial_convolution_weak_local
    (c : ℝ) (v : ι → T) {Ω : Set (KSSpace × T)}
    {K : T → ℝ} {G f : KSSpace × T → ℂ}
    (hKi : Integrable K volume)
    (hG : MemLp G 2 (volume : Measure (KSSpace × T)))
    (hf : MemLp f 2 (volume : Measure (KSSpace × T)))
    (hweak : ∀ ψ : KSSpace × T → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω → (∫ p, splitGrushin c v (fun _ => 0) ψ p • G p) = ∫ p, ψ p • f p)
    {φ : KSSpace × T → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hshift : ∀ s : T, K s ≠ 0 → tsupport (fun q => φ (q+(0,s))) ⊆ Ω) :
    (∫ p, splitGrushin c v (fun _ => 0) φ p • partialSpectatorConvolution (ν := volume) K G p) =
      ∫ p, φ p • partialSpectatorConvolution (ν := volume) K f p := by
  have hP := splitGrushin_continuous c v (B := fun _ => 0) continuous_const hφ
  have hcP := splitGrushin_compact c v (fun _ => 0) hcφ
  change (∫ p, splitGrushin c v (fun _ => 0) φ p • partialSpectatorConvolution (ν := volume) K G p
      ∂(volume : Measure KSSpace).prod volume) =
    ∫ p, φ p • partialSpectatorConvolution (ν := volume) K f p ∂(volume : Measure KSSpace).prod volume
  rw [partialSpectatorConvolution_ae_test_pairing hKi hG hP hcP,
    partialSpectatorConvolution_ae_test_pairing hKi hf hφ.continuous hcφ]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro s
  by_cases hs : K s = 0
  · simp [hs]
  · have hw := hweak (fun q => φ (q+(0,s))) (spectator_translated_test_contDiff hφ s)
      (spectator_translated_test_hasCompactSupport hcφ s) (hshift s hs)
    simp_rw [splitGrushin_spectator_translate] at hw
    have he (q : KSSpace × T) : q+(0,s) = (q.1,q.2+s) := by ext <;> simp
    simp_rw [he] at hw
    exact congrArg (fun z : ℂ => K s • z) hw

theorem splitGrushin_partial_convolution_weak
    (c : ℝ) (v : ι → T) {K : T → ℝ} {G f : KSSpace × T → ℂ}
    (hKi : Integrable K volume)
    (hG : MemLp G 2 (volume : Measure (KSSpace × T)))
    (hf : MemLp f 2 (volume : Measure (KSSpace × T)))
    (hweak : ∀ ψ : KSSpace × T → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ p, splitGrushin c v (fun _ => 0) ψ p • G p) = ∫ p, ψ p • f p)
    {φ : KSSpace × T → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) :
    (∫ p, splitGrushin c v (fun _ => 0) φ p • partialSpectatorConvolution (ν := volume) K G p) =
      ∫ p, φ p • partialSpectatorConvolution (ν := volume) K f p := by
  apply splitGrushin_partial_convolution_weak_local c v (Ω := Set.univ) hKi hG hf
    (fun ψ hψ hcψ _ => hweak ψ hψ hcψ) hφ hcφ
  exact fun s _ => Set.subset_univ _

#print axioms splitGrushin_partial_convolution_weak_local
#print axioms splitGrushin_partial_convolution_weak
end TheoremT.Continuum
