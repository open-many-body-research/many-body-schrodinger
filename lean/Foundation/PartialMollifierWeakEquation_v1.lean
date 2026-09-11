import GrushinPartialMollifierSupport_v1
import PartialSpectatorWeakJets_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum
variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

theorem partialMollifyLp_test_eq (n : ℕ) (f : Lp ℂ 2 (volume : Measure (Y × T)))
    (φ : Y × T → ℝ) :
    (∫ p, φ p • partialMollifyLp n f p) =
      ∫ p, φ p • partialSpectatorConvolution (ν := volume) (GenericMollifier.mollifierKernel n) f p := by
  apply integral_congr_ae
  filter_upwards [partialMollifyLp_ae n f] with p hp
  rw [hp]

theorem partialMollifyLp_eq_jet_nil (n : ℕ) (f : Lp ℂ 2 (volume : Measure (Y × T))) :
    partialMollifyLp n f = partialSpectatorJetLp (GenericMollifier.mollifierKernel_contDiff n)
      (GenericMollifier.mollifierKernel_hasCompactSupport n) (Lp.memLp f) [] := rfl

variable {ι : Type*} [Fintype ι]

theorem partialMollifyLp_splitGrushin_weak_eventually
    (c : ℝ) (v : ι → T) {Ω : Set (KSSpace × T)} (hΩ : IsOpen Ω)
    (G f : Lp ℂ 2 (volume : Measure (KSSpace × T)))
    (hweak : ∀ ψ : KSSpace × T → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω → (∫ p, splitGrushin c v (fun _ => 0) ψ p • G p) = ∫ p, ψ p • f p)
    {φ : KSSpace × T → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Ω) :
    ∀ᶠ n : ℕ in atTop,
      (∫ p, splitGrushin c v (fun _ => 0) φ p • partialMollifyLp n G p) =
        ∫ p, φ p • partialMollifyLp n f p := by
  filter_upwards [partial_mollifier_shifted_support_eventually hΩ hcφ hsφ] with n hn
  rw [partialMollifyLp_test_eq,partialMollifyLp_test_eq]
  exact splitGrushin_partial_convolution_weak_local c v
    (GenericMollifier.mollifierKernel_integrable n) (Lp.memLp G) (Lp.memLp f) hweak hφ hcφ hn

#print axioms partialMollifyLp_test_eq
#print axioms partialMollifyLp_eq_jet_nil
#print axioms partialMollifyLp_splitGrushin_weak_eventually
end TheoremT.Continuum
