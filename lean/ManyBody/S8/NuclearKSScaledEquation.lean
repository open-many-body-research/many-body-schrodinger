import ManyBody.S8.Internal.NuclearKSGrushinScaling
import ManyBody.S8.Internal.NuclearKSMeasureScaling
import CoulombNuclearKSWeak_v1

/-! Exact weak equation transport under the actual nuclear KS dilation.
True integrability is transported along with the zero weak integral. The
rescaled equation has coefficient r*B(Z,rE), including across the selected
collision fiber. No pushforward or transformed PDE is supplied as a premise
in the physical scalar theorem.
-/
noncomputable section
open MeasureTheory
open scoped ContDiff
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin

namespace ManyBody.S8

theorem weak_grushin_nuclear_anisotropicScale {N : ℕ} (i : Fin N) {r : ℝ}
    (hr : 0 < r) (c : ℝ) (B : NuclearKSSpace i → ℝ)
    (raw : NuclearKSSpace i → ℂ) (Ω : Set (NuclearKSSpace i))
    (hP : ∀ ψ : NuclearKSSpace i → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω →
      Integrable (fun p => splitGrushin c oscillatorBasis B ψ p • raw p) volume ∧
      (∫ p, splitGrushin c oscillatorBasis B ψ p • raw p) = 0)
    {φ : NuclearKSSpace i → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ (nuclearKSAnisotropicEquiv i hr) ⁻¹' Ω) :
    Integrable (fun q => splitGrushin c oscillatorBasis
      (fun p => r * B (nuclearKSAnisotropicScale i r p)) φ q •
      raw (nuclearKSAnisotropicScale i r q)) volume ∧
    (∫ q, splitGrushin c oscillatorBasis
      (fun p => r * B (nuclearKSAnisotropicScale i r p)) φ q •
      raw (nuclearKSAnisotropicScale i r q)) = 0 := by
  let e := nuclearKSAnisotropicEquiv i hr
  let ψ := φ ∘ e.symm
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp e.symm.contDiff
  have hcψ : HasCompactSupport ψ := hcφ.comp_homeomorph e.symm.toHomeomorph
  have hsψ : tsupport ψ ⊆ Ω := by
    intro p hp
    have ht : e.symm p ∈ tsupport φ := by
      have hh := (Set.ext_iff.mp (tsupport_comp_eq_preimage φ e.symm.toHomeomorph) p).mp hp
      exact hh
    have ho := hsφ ht
    simpa only [Set.mem_preimage, e, ContinuousLinearEquiv.apply_symm_apply] using ho
  have heφ : ψ ∘ nuclearKSAnisotropicScaleCLM i r = φ := by
    funext q
    change φ (e.symm (nuclearKSAnisotropicScaleCLM i r q)) = φ q
    rw [← nuclearKSAnisotropicEquiv_clm i hr]
    exact congrArg φ (e.symm_apply_apply q)
  have hlocal := hP ψ hψ hcψ hsψ
  let H : NuclearKSSpace i → ℂ := fun p => splitGrushin c oscillatorBasis B ψ p • raw p
  obtain ⟨J, _hJ, htransport⟩ := nuclearKSAnisotropicEquiv_integral_transport i hr
  have hI : Integrable (H ∘ e) volume := (htransport H).1.mp hlocal.1
  have hpoint (q : NuclearKSSpace i) :
      splitGrushin c oscillatorBasis (fun p => r * B (nuclearKSAnisotropicScale i r p))
        φ q • raw (nuclearKSAnisotropicScale i r q) = r • H (e q) := by
    have ho := splitGrushin_nuclear_anisotropicScale i hr c B hψ q
    rw [heφ] at ho
    rw [ho]
    simp only [H, e, nuclearKSAnisotropicEquiv_apply, mul_smul]
  constructor
  · exact (hI.smul r).congr (Filter.Eventually.of_forall (fun q => (hpoint q).symm))
  · calc
      _ = ∫ q, r • H (e q) := integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ = r • ∫ q, H (e q) := integral_smul _ _
      _ = r • (J • ∫ p, H p) := by rw [(htransport H).2]
      _ = 0 := by simp only [H, hlocal.2, smul_zero]

theorem scalar_coulomb_nuclear_KS_scaled_weak {N : ℕ} (i : Fin N) (Z E : ℝ)
    {r : ℝ} (hr : 0 < r) {f : SpatialL2 N}
    (hgraph : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    {g : Configuration N → ℂ} (hg : Continuous g)
    (hfg : (f : Configuration N → ℂ) =ᵐ[volume] g)
    {φ : NuclearKSSpace i → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ nuclearKSCoefficientPatch i) :
    Integrable (fun q => splitGrushin 4 oscillatorBasis
      (fun p => r * nuclearKSPotential i Z (r * E) p) φ q •
      g (nuclearKSLift i (nuclearKSAnisotropicScale i r q))) volume ∧
    (∫ q, splitGrushin 4 oscillatorBasis
      (fun p => r * nuclearKSPotential i Z (r * E) p) φ q •
      g (nuclearKSLift i (nuclearKSAnisotropicScale i r q))) = 0 := by
  have hP : ∀ ψ : NuclearKSSpace i → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ nuclearKSCoefficientPatch i →
      Integrable (fun p => splitGrushin 4 oscillatorBasis (nuclearKSPotential i Z E) ψ p •
        g (nuclearKSLift i p)) volume ∧
      (∫ p, splitGrushin 4 oscillatorBasis (nuclearKSPotential i Z E) ψ p •
        g (nuclearKSLift i p)) = 0 := by
    intro ψ hψ hcψ hsψ
    have hBasis : (spectatorBasis : SpectatorCoordinate i → SpectatorConfiguration i) =
        oscillatorBasis := by
      funext j
      simp only [spectatorBasis, oscillatorBasis, EuclideanSpace.single, PiLp.single]
    have hh := scalar_coulomb_nuclear_KS_weak i hgraph hg hfg hψ hcψ hsψ
    rw [hBasis] at hh
    simpa only [Function.comp_apply, Complex.real_smul] using hh
  have hs : tsupport φ ⊆ (nuclearKSAnisotropicEquiv i hr) ⁻¹' nuclearKSCoefficientPatch i := by
    intro q hq
    exact (nuclearKSCoefficientPatch_anisotropicScale_iff i hr q).2 (hsφ hq)
  have hh := weak_grushin_nuclear_anisotropicScale i hr 4 (nuclearKSPotential i Z E)
    (fun p => g (nuclearKSLift i p)) (nuclearKSCoefficientPatch i) hP hφ hcφ hs
  have hb : (fun p => r * nuclearKSPotential i Z E (nuclearKSAnisotropicScale i r p)) =
      (fun p => r * nuclearKSPotential i Z (r * E) p) := by
    funext p
    rw [nuclearKSPotential_anisotropicScale i Z E hr]
  rw [hb] at hh
  exact hh

#print axioms weak_grushin_nuclear_anisotropicScale
#print axioms scalar_coulomb_nuclear_KS_scaled_weak
end ManyBody.S8
