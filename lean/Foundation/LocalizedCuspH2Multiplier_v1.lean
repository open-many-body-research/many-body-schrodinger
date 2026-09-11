import LocalizedCuspMultiplierLimits_v1
import WeakH2MultiplierLimit_v1

/-! Actual multiplication by chi exp(-F) preserves the unchanged weak H2
configuration domain for every finite N and real Z. The auxiliary Hessian map
is used only on H1 inputs; its value outside that domain is irrelevant.
This is a mathematical Sobolev theorem, not an executable integration routine. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology
namespace TheoremT.Continuum

theorem localizedCusp_H2_multiplier (N : ℕ) (Z : ℝ)
    {χ : Configuration N → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ h₀ : MemLp (localizedCusp N Z χ) (⊤ : ENNReal) volume,
      ∀ f : SpatialL2 N, HasH2 f → HasH2 (boundedRealMul (localizedCusp N Z χ) h₀ f) := by
  classical
  obtain ⟨h₀,hU⟩ := localizedCusp_value_multiplier_limit N Z hχ hc
  have hex (k : Coordinate N) := localizedCusp_gradient_multiplier_limit N Z hχ hc (coordinateVector k)
  choose hD hDlim using hex
  let E (k l : Coordinate N) (g : SpatialL2 N) : SpatialL2 N :=
    if hg : HasH1 g then
      (localizedCusp_hessian_multiplier_limit N Z hχ hc (coordinateVector k) (coordinateVector l) g hg).choose.toLp
        (fun x => localizedCuspHessian N Z χ (coordinateVector k) (coordinateVector l) x • g x)
    else 0
  have hElim (k l : Coordinate N) (g : SpatialL2 N) (hg : HasH1 g) :
      Tendsto (fun n => boundedRealMul (fun x => fderiv ℝ
        (fun y => fderiv ℝ (regularizedLocalizedCusp N Z χ n) y (coordinateVector k)) x (coordinateVector l))
        (regularizedLocalizedCusp_mixed_memLp_top N Z hχ hc n (coordinateVector k) (coordinateVector l)) g)
        atTop (𝓝 (E k l g)) := by
    simp only [E,dif_pos hg]
    exact (localizedCusp_hessian_multiplier_limit N Z hχ hc (coordinateVector k) (coordinateVector l) g hg).choose_spec
  refine ⟨h₀,?_⟩
  intro f hf
  exact weakH2_multiplier_of_smooth_limits (regularizedLocalizedCusp N Z χ)
    (regularizedLocalizedCusp_contDiff N Z hχ)
    (regularizedLocalizedCusp_memLp_top N Z hχ hc)
    (fun n k => regularizedLocalizedCusp_partial_memLp_top N Z hχ hc n (coordinateVector k))
    (fun n k l => regularizedLocalizedCusp_mixed_memLp_top N Z hχ hc n (coordinateVector k) (coordinateVector l))
    (boundedRealMul (localizedCusp N Z χ) h₀)
    (fun k => boundedRealMul (localizedCuspGradient N Z χ (coordinateVector k)) (hD k))
    E hU hDlim hElim hf

theorem localizedCusp_H2_product_exists (N : ℕ) (Z : ℝ)
    {χ : Configuration N → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {f : SpatialL2 N} (hf : HasH2 f) :
    ∃ g : SpatialL2 N, HasH2 g ∧
      g =ᵐ[volume] (fun x => (χ x*Real.exp (-coulombCusp N Z x)) • f x) := by
  obtain ⟨h₀,h⟩ := localizedCusp_H2_multiplier N Z hχ hc
  exact ⟨boundedRealMul (localizedCusp N Z χ) h₀ f,h f hf,
    boundedRealMul_ae (localizedCusp N Z χ) h₀ f⟩

#print axioms localizedCusp_H2_multiplier
#print axioms localizedCusp_H2_product_exists
end TheoremT.Continuum
