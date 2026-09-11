import GrushinContinuousRemovability_v1
import GrushinLocalCoefficient_v1
import FiniteDimSmoothCutoff_v1

/-! Removal of the transverse zero set with coefficients smooth only on the
actual open coefficient patch. Both integrability and the weak identity are
conclusions; no value of a totalized nonintegrable integral is used. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology
namespace TheoremT.Continuum

theorem nuclear_KS_local_coefficient_Grushin_removability {N : ℕ} (i : Fin N)
    {ι : Type*} [Fintype ι] (c : ℝ) (v : ι → SpectatorConfiguration i)
    {Ω : Set (NuclearKSSpace i)} (hΩ : IsOpen Ω)
    {B : NuclearKSSpace i → ℝ} (hB : ∀ q ∈ Ω, ContDiffAt ℝ ∞ B q)
    {u f : NuclearKSSpace i → ℂ} (hu : Continuous u) (hf : Continuous f)
    (hweak : ∀ ψ : NuclearKSSpace i → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω \ {q | q.1=0} →
      (∫ q, (splitGrushin c v B ψ q : ℂ)*u q) = ∫ q, (ψ q : ℂ)*f q)
    {φ : NuclearKSSpace i → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ω) :
    Integrable (fun q => (splitGrushin c v B φ q : ℂ)*u q) volume ∧
    Integrable (fun q => (φ q : ℂ)*f q) volume ∧
    (∫ q, (splitGrushin c v B φ q : ℂ)*u q) = ∫ q, (φ q : ℂ)*f q := by
  obtain ⟨η,hη,hcη,hsη,h1⟩ := finiteDim_compact_exists_smooth_cutoff hc.isCompact hΩ hs
  let C : NuclearKSSpace i → ℝ := fun q => η q*B q
  have hC : ContDiff ℝ ∞ C := smooth_mul_of_smooth_on_tsupport hη (fun q hq => hB q (hsη hq))
  let Ω' : Set (NuclearKSSpace i) := Ω ∩ {q | η q=1}
  have hs' : tsupport φ ⊆ Ω' := by
    intro q hq
    exact ⟨hs hq,(h1 q hq).self_of_nhds⟩
  have heq {ψ : NuclearKSSpace i → ℝ} (hψ : tsupport ψ ⊆ Ω') :
      splitGrushin c v C ψ=splitGrushin c v B ψ := by
    apply splitGrushin_coefficient_congr
    intro q hq
    change η q*B q=B q
    rw [(hψ hq).2,one_mul]
  have hw : ∀ ψ : NuclearKSSpace i → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω' \ {q | q.1=0} →
      (∫ q, (splitGrushin c v C ψ q : ℂ)*u q) = ∫ q, (ψ q : ℂ)*f q := by
    intro ψ hψ hcψ hsψ
    rw [heq (fun q hq => (hsψ hq).1)]
    exact hweak ψ hψ hcψ (fun q hq => ⟨(hsψ hq).1.1,(hsψ hq).2⟩)
  have hid := nuclear_KS_continuous_Grushin_removability i c v hC.continuous hu hf Ω' hw hφ hc hs'
  rw [heq hs'] at hid
  refine ⟨?_,nuclear_KS_real_test_mul_integrable i hφ.continuous hc hf,hid⟩
  exact nuclear_KS_real_test_mul_integrable i
    (splitGrushin_continuous_local_coefficient c v hφ (fun q hq => hB q (hs hq)))
    (splitGrushin_compact c v B hc) hu

#print axioms nuclear_KS_local_coefficient_Grushin_removability
end TheoremT.Continuum
