import ManyBody.S8.Internal.NuclearPhysicalInitialization
import GrushinTestSupport_v1

/-! Exact preservation of the actual weak potential equation on a cutoff plateau.
The raw physical pullback need not be globally square integrable in KS coordinates.
-/
noncomputable section
open MeasureTheory
open scoped ContDiff
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin

namespace ManyBody.S8
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem weak_potential_output_on_plateau (c : ℝ) (B : Space κ → ℝ)
    {raw : Space κ → ℂ} {U : Lp ℂ 2 (volume : Measure (Space κ))}
    {χ : Space κ → ℝ}
    (hU : (U : Space κ → ℂ) =ᵐ[volume] (fun p => χ p • raw p))
    {V Ω : Set (Space κ)} (hVO : V ⊆ Ω) (hχ1 : ∀ p ∈ V, χ p = 1)
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis B φ p • raw p) = 0) :
    ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∫ p, splitGrushin c oscillatorBasis B φ p • U p) = 0 := by
  intro φ hφ hcφ hsφ
  calc
    _ = ∫ p, splitGrushin c oscillatorBasis B φ p • raw p := by
      apply integral_congr_ae
      filter_upwards [hU] with p hp
      by_cases ht : p ∈ tsupport φ
      · rw [hp, hχ1 p (hsφ ht), one_smul]
      · rw [splitGrushin_zero_off_test c oscillatorBasis B ht]
        simp only [zero_smul]
    _ = 0 := hP φ hφ hcφ (hsφ.trans hVO)

theorem scalar_nuclear_output_on_plateau {N : ℕ} (i : Fin N) (Z E : ℝ)
    {f : SpatialL2 N} (hgraph : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    {g : Configuration N → ℂ} (hg : Continuous g)
    (hfg : (f : Configuration N → ℂ) =ᵐ[volume] g)
    {U : Lp ℂ 2 (volume : Measure (NuclearKSSpace i))} {χ : NuclearKSSpace i → ℝ}
    (hU : (U : NuclearKSSpace i → ℂ) =ᵐ[volume]
      (fun p => χ p • g (nuclearKSLift i p)))
    {V Ω : Set (NuclearKSSpace i)} (hVO : V ⊆ Ω)
    (hΩpatch : Ω ⊆ nuclearKSCoefficientPatch i) (hχ1 : ∀ p ∈ V, χ p = 1) :
    ∀ φ : NuclearKSSpace i → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∫ p, splitGrushin 4 oscillatorBasis (nuclearKSPotential i Z E) φ p • U p) = 0 := by
  apply weak_potential_output_on_plateau 4 (nuclearKSPotential i Z E) hU hVO hχ1
  intro φ hφ hcφ hsφ
  have hBasis : (spectatorBasis : SpectatorCoordinate i → SpectatorConfiguration i) =
      oscillatorBasis := by
    funext j
    simp only [spectatorBasis, oscillatorBasis, EuclideanSpace.single, PiLp.single]
  have hh := (scalar_coulomb_nuclear_KS_weak i hgraph hg hfg hφ hcφ
    (hsφ.trans hΩpatch)).2
  rw [hBasis] at hh
  simpa only [Function.comp_apply, Complex.real_smul] using hh

#print axioms weak_potential_output_on_plateau
#print axioms scalar_nuclear_output_on_plateau
end ManyBody.S8