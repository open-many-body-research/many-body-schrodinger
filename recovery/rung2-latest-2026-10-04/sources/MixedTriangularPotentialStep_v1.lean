import MixedTriangularYGainStep_v1
import MixedGrushinYEquations_v1
import MixedYEquationSourceL2Bound_v1
import MixedYIterationBudget_v1
import SpectatorIterationGeometry_v1

/-! An actual quantitative triangular potential-equation step. The new
Y jets, every differentiated PDE, and the forcing norm bounds are derived
from the original weak PDE, the existing triangular reserve, finite source
jets, and pointwise coefficient bounds. Only source/coefficient orders
through m-2 are consumed. All constants are explicit finite expressions.
-/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

set_option maxHeartbeats 1200000 in
theorem mixedTriangularState_potential_step
    (c : ℝ) {Ω O V : Set (Space κ)} {χ η : Space κ → ℝ}
    (M A L D Q K0 Q0 H0 W : ℝ)
    (hGeom : SpectatorStepGeometry 0 Ω O V χ η M A L D Q) (hO : IsOpen O)
    {B : Space κ → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    {r m : ℕ} (hr : 1 ≤ r) (hW : 0 ≤ W)
    (f : Space κ → ℂ) (S : List (Fin 4) → List κ → Space κ → ℂ)
    (hf : MixedTriangularState Ω f r m W)
    (hS : ∀ a b, a.length+b.length+2 ≤ m → RegionL2Budget (S a b) Ω H0)
    (hSY : ∀ a b i, a.length+b.length+2 < m →
      ProductLocalWeakDirectional Ω (S a b) (S (i :: a) b) (yDir i))
    (hST : ∀ b j, b.length+2 < m →
      ProductLocalWeakDirectional Ω (S [] b) (S [] (j :: b)) (tDir j))
    (hCoeff : ∀ a b, a.length+b.length+2 ≤ m → ∀ p ∈ Ω,
      |directionalWordDeriv yDir (spectatorWordDeriv B b) a p| ≤ K0)
    (hQuad : ∀ a, a.length+2 ≤ m → ∀ p ∈ Ω,
      |directionalWordDeriv yDir (fun p : Space κ => ‖p.1‖^2) a p| ≤ Q0)
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis B φ p • f p) = ∫ p, φ p • S [] [] p) :
    MixedTriangularState O f (r+2) m
      (mixedYIterationNext c M A L D Q K0 Q0 H0 m (Fintype.card κ) W) := by
  have hOΩ := hGeom.domain_subset
  obtain ⟨hΩ,hχ,hcχ,hη,hcη,hηΩ,hV,hχV,hη1,hL0,hD0,hQ0,hM,hA,hL,hD,hQ,hχ1⟩ := hGeom
  obtain ⟨F,h0,hF,hY,hT⟩ := hf
  have hT0 (b : List κ) (j : κ) (hb : b.length < m) := hT [] b j (by simp) (by simpa using hb)
  have hP0 : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis B φ p • F [] [] p) = ∫ p, φ p • S [] [] p := by
    simpa only [h0] using hP
  have hEq := mixed_grushin_y_equations c hΩ hB F S
    (fun a b ha hab => (hF a b ha hab).local) hY hT0
    (fun a b hab => (hS a b hab).local) hSY hST hP0
  have hSource (a : List (Fin 4)) (b : List κ) (ha : a.length ≤ r)
      (hab : a.length+b.length+2 ≤ m) :
      RegionL2Budget (mixedYEquationSource c B F S a b) Ω
        (mixedYSourceBudget c K0 Q0 H0 m (Fintype.card κ) W) := by
    have hn := mixedYEquationSource_region_L2_bound c hΩ hB F S
      (fun a b ha hab => (hF a b ha hab).1) a b ha hab (hS a b hab).1
      (fun ya tb hya htb p hp => hCoeff ya tb (by omega) p hp)
      (fun ya hya p hp => hQuad ya (by omega) p hp)
      (fun a b ha hab => (hF a b ha hab).2) (hS a b hab).2
    refine ⟨hn.1,hn.2.2.trans ?_⟩
    have hu := mixedYEquationSource_budget_le_uniform (κ := κ) a b hab c K0 Q0 W H0 hW
    unfold mixedYSourceBudget
    exact hu.trans_eq (by ring)
  have hout := mixed_triangular_y_gain_step hΩ hχ hcχ hη hcη hηΩ hV hχV hη1
    M A L D Q hL0 hD0 hQ0 hM hA hL hD hQ hO hOΩ hχ1 hr
    W (mixedYSourceBudget c K0 Q0 H0 m (Fintype.card κ) W) F (mixedYEquationSource c B F S)
    hF hY hT0 (fun a b ha _ hab => hSource a b ha hab)
    (fun a b ha _ hab φ hφ hc hs => ((hEq a b ha hab).2 φ hφ hc hs).2.2)
  simpa only [mixedYIterationNext,h0] using hout

#print axioms mixedTriangularState_potential_step
end TheoremT.Continuum.WeakGrushin
