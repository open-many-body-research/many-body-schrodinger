import ManyBody.S8.Internal.PhysicalOriginalOperatorNormBudget
/-! Actual finite annular physical chart operator norm consumers. Both nuclear
and original half-sum pair balance come from the literal physical KS lift. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace ManyBody.S8
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin

def AnnularNuclearOriginalOperatorData (g : Configuration 2 → ℂ)
    (i : Fin 2) (ρ η : ℝ) (t0 : Position) (m M A Csrc CH12 : ℝ) (ψ : SpinSpace 2) : Prop :=
  AnnularNuclearOriginalDerivativeData g i ρ η t0 m M A Csrc CH12 ψ ∧
  ∀ x : Configuration 2, ρ⁻¹ • x∈annularNuclearNeighborhood i t0 η →
    PhysicalOriginalCollisionOperatorAtBudget
      ((originScaledDifference g ρ ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
      t0 ρ (g 0) m M A Csrc CH12 ψ (position x i,position x (1-i))

def AnnularPairOriginalOperatorData (g : Configuration 2 → ℂ)
    (ρ η : ℝ) (t0 : Position) (m M A Csrc CH12 : ℝ) (ψ : SpinSpace 2) : Prop :=
  AnnularPairOriginalDerivativeData g ρ η t0 m M A Csrc CH12 ψ ∧
  ∀ x : Configuration 2, ρ⁻¹ • x∈annularPairNeighborhood t0 η →
    PhysicalOriginalCollisionOperatorAtBudget
      ((originScaledDifference g (ρ / Real.sqrt 2) ∘ TheoremT.Continuum.pairKSLift) ∘
        (physicalSpectatorReindexAt (0:Fin 2)).symm)
      t0 (ρ / Real.sqrt 2) (g 0) m M A Csrc CH12 ψ
      (position x 0-position x 1,annularPairCenter x)
theorem nuclear_annular_original_operator_data
    (g : Configuration 2 → ℂ) (i : Fin 2) {ρ η m M A Csrc CH12 : ℝ}
    {t0 : Position} {ψ : SpinSpace 2} {v : Position → Position → ℂ}
    (hρ : 0<ρ) (hA : 1≤A) (hF0 : 0≤Csrc*‖ψ‖)
    (hm : 0≤m) (hsrc : 0≤Csrc) (hH12 : 0≤CH12)
    (hηX : η≤physicalDescentPositionRadius M A)
    (hηT : η≤physicalDescentNeighborhoodRadius M A)
    (hηD : (32*(7*physicalKSPointwiseRate M A)^2)*η≤1/4)
    (hηS : (7*physicalKSPointwiseRate M A)*η≤1/4)
    (hdata : PhysicalKSBoxOriginalNormAnalyticDerivativeData
      ((originScaledDifference g ρ ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
      v t0 M A Csrc CH12 ψ)
    (hu0 : ‖g 0‖≤m*‖ψ‖) :
    AnnularNuclearOriginalOperatorData g i ρ η t0 m M A Csrc CH12 ψ := by
  refine ⟨nuclear_annular_original_derivative_data g i hρ hA hF0 hηX hηT hηD hηS hdata hu0,?_⟩
  have hbal : ∀ j γ e, e∈(ksRealPolynomialToSpinor
      (physicalKSTaylorEvenSpectatorFamily
        ((originScaledDifference g ρ ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
        (0,t0) j γ)).support → e 0+e 1=e 2+e 3 := by
    intro j γ e he
    exact nuclearKSPhysicalTaylorSpectatorCoefficient_balanced_support
      (originScaledDifference g ρ) i hdata.1.1.1 hA hF0
      (2*j) (Finsupp.equivFunOnFinite.symm γ) e he
  intro x hx
  have hS : 0≤7*physicalKSPointwiseRate M A :=
    (mul_pos (by norm_num) (physicalKSPointwiseRate_pos hA)).le
  have hD : 0≤32*(7*physicalKSPointwiseRate M A)^2 := by positivity
  have hXq : ‖(ρ⁻¹ • (position x i,position x (1-i))).1‖ < η := by
    change ‖ρ⁻¹ • position x i‖ < η
    rw [← position_smul_annular]
    exact hx.1
  have hTq : ‖(ρ⁻¹ • (position x i,position x (1-i))).2-t0‖ < η := by
    change ‖ρ⁻¹ • position x (1-i)-t0‖ < η
    rw [← position_smul_annular]
    exact hx.2
  exact physical_original_collision_operator_at_budget hρ hm hA hsrc hH12 hdata hbal hu0
    (position x i,position x (1-i))
    ((mul_le_mul_of_nonneg_left hXq.le hD).trans hηD)
    ((mul_le_mul_of_nonneg_left hTq.le hS).trans hηS)
theorem pair_annular_original_operator_data
    (g : Configuration 2 → ℂ) {ρ η m M A Csrc CH12 : ℝ}
    {t0 : Position} {ψ : SpinSpace 2} {v : Position → Position → ℂ}
    (hρ : 0<ρ) (hA : 1≤A) (hF0 : 0≤Csrc*‖ψ‖)
    (hm : 0≤m) (hsrc : 0≤Csrc) (hH12 : 0≤CH12)
    (hηX : Real.sqrt 2*η≤physicalDescentPositionRadius M A)
    (hηT : Real.sqrt 2*η≤physicalDescentNeighborhoodRadius M A)
    (hηD : (32*(7*physicalKSPointwiseRate M A)^2)*(Real.sqrt 2*η)≤1/4)
    (hηS : (7*physicalKSPointwiseRate M A)*(Real.sqrt 2*η)≤1/4)
    (hdata : PhysicalKSBoxOriginalNormAnalyticDerivativeData
      ((originScaledDifference g (ρ / Real.sqrt 2) ∘ TheoremT.Continuum.pairKSLift) ∘
        (physicalSpectatorReindexAt (0 : Fin 2)).symm) v t0 M A Csrc CH12 ψ)
    (hu0 : ‖g 0‖≤m*‖ψ‖) :
    AnnularPairOriginalOperatorData g ρ η t0 m M A Csrc CH12 ψ := by
  refine ⟨pair_annular_original_derivative_data g hρ hA hF0 hηX hηT hηD hηS hdata hu0,?_⟩
  have hbal : ∀ j γ e, e∈(ksRealPolynomialToSpinor
      (physicalKSTaylorEvenSpectatorFamily
        ((originScaledDifference g (ρ / Real.sqrt 2) ∘ TheoremT.Continuum.pairKSLift) ∘
          (physicalSpectatorReindexAt (0:Fin 2)).symm)
        (0,t0) j γ)).support → e 0+e 1=e 2+e 3 := by
    intro j γ e he
    exact pairKSPhysicalTaylorSpectatorCoefficient_balanced_support
      (originScaledDifference g (ρ / Real.sqrt 2)) hdata.1.1.1 hA hF0
      (2*j) (Finsupp.equivFunOnFinite.symm γ) e he
  intro x hx
  have hs : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hε : 0<ρ / Real.sqrt 2 := div_pos hρ hs
  have hS : 0≤7*physicalKSPointwiseRate M A :=
    (mul_pos (by norm_num) (physicalKSPointwiseRate_pos hA)).le
  have hD : 0≤32*(7*physicalKSPointwiseRate M A)^2 := by positivity
  have hscalar : (ρ / Real.sqrt 2)⁻¹=Real.sqrt 2*ρ⁻¹ := by rw [inv_div,div_eq_mul_inv]
  have hfirst : (ρ / Real.sqrt 2)⁻¹ • (position x 0-position x 1) =
      Real.sqrt 2 • (position (ρ⁻¹ • x) 0-position (ρ⁻¹ • x) 1) := by
    rw [hscalar,position_smul_annular,position_smul_annular,smul_sub,smul_sub,smul_smul,smul_smul]
  have hsecond : (ρ / Real.sqrt 2)⁻¹ • annularPairCenter x-t0 =
      Real.sqrt 2 • (annularPairCenter (ρ⁻¹ • x)-(Real.sqrt 2)⁻¹ • t0) := by
    rw [hscalar,annularPairCenter_smul,smul_sub,smul_smul,smul_smul,mul_inv_cancel₀ hs.ne',one_smul]
  have hXq : ‖((ρ / Real.sqrt 2)⁻¹ •
      (position x 0-position x 1,annularPairCenter x)).1‖ < Real.sqrt 2*η := by
    change ‖(ρ / Real.sqrt 2)⁻¹ • (position x 0-position x 1)‖ < _
    rw [hfirst,norm_smul,Real.norm_eq_abs,abs_of_pos hs]
    exact mul_lt_mul_of_pos_left hx.1 hs
  have hTq : ‖((ρ / Real.sqrt 2)⁻¹ •
      (position x 0-position x 1,annularPairCenter x)).2-t0‖ < Real.sqrt 2*η := by
    change ‖(ρ / Real.sqrt 2)⁻¹ • annularPairCenter x-t0‖ < _
    rw [hsecond,norm_smul,Real.norm_eq_abs,abs_of_pos hs]
    exact mul_lt_mul_of_pos_left hx.2 hs
  exact physical_original_collision_operator_at_budget hε hm hA hsrc hH12 hdata hbal hu0
    (position x 0-position x 1,annularPairCenter x)
    ((mul_le_mul_of_nonneg_left hXq.le hD).trans hηD)
    ((mul_le_mul_of_nonneg_left hTq.le hS).trans hηS)
#print axioms nuclear_annular_original_operator_data
#print axioms pair_annular_original_operator_data
end ManyBody.S8
