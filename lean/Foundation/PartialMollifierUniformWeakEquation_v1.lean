import PartialMollifierWeakEquation_v1
import GrushinPartialMollifierUniformSupport_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum
variable {T : Type*} [NormedAddCommGroup T] [InnerProductSpace ℝ T]
  [FiniteDimensional ℝ T] [MeasurableSpace T] [BorelSpace T]
variable {ι : Type*} [Fintype ι]

theorem partialMollifyLp_splitGrushin_weak_uniformly_eventually
    (c : ℝ) (v : ι → T) {Ω C : Set (KSSpace × T)}
    (hΩ : IsOpen Ω) (hC : IsCompact C) (hCΩ : C ⊆ Ω)
    (G f : Lp ℂ 2 (volume : Measure (KSSpace × T)))
    (hweak : ∀ ψ : KSSpace × T → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω → (∫ p, splitGrushin c v (fun _ => 0) ψ p • G p) = ∫ p, ψ p • f p) :
    ∀ᶠ n : ℕ in atTop, ∀ φ : KSSpace × T → ℝ,
      ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ C →
        (∫ p, splitGrushin c v (fun _ => 0) φ p • partialMollifyLp n G p) =
          ∫ p, φ p • partialMollifyLp n f p := by
  filter_upwards [partial_mollifier_shifted_support_uniform_eventually hΩ hC hCΩ]
    with n hn φ hφ hcφ hsφ
  rw [partialMollifyLp_test_eq,partialMollifyLp_test_eq]
  exact splitGrushin_partial_convolution_weak_local c v
    (GenericMollifier.mollifierKernel_integrable n) (Lp.memLp G) (Lp.memLp f) hweak hφ hcφ
    (hn φ hsφ)

#print axioms partialMollifyLp_splitGrushin_weak_uniformly_eventually
end TheoremT.Continuum
