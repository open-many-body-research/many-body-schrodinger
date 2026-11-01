import SO2AxisGroupedAnisotropic_v1
import PhysicalKSTaylorAnalyticDescentData_v1

/-! Actual four-coordinate axis polynomials of the physical nuclear/pair
KS descended A/B series. Coefficients come from literal polynomial
restriction and grouping; no new Cauchy coefficient premise is inserted. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
open MvPolynomial WeakGrushin

def physicalKSAxisPolynomialA (f : Space (Fin 3) → ℂ) (t0 : Position) :
    ℕ → MvPolynomial (Fin 2 ⊕ Fin 2) ℂ :=
  so2AxisGroupedPolynomial (ksRealSpectatorFamilyA (physicalKSTaylorEvenSpectatorFamily f (0,t0)))

def physicalKSAxisPolynomialB (f : Space (Fin 3) → ℂ) (t0 : Position) :
    ℕ → MvPolynomial (Fin 2 ⊕ Fin 2) ℂ :=
  so2AxisGroupedPolynomial (ksRealSpectatorFamilyB (physicalKSTaylorEvenSpectatorFamily f (0,t0)))

def physicalKSAxisSeriesRate (M A : ℝ) : ℝ :=
  2*max (32*(7*physicalKSPointwiseRate M A)^2) (7*physicalKSPointwiseRate M A)

def PhysicalKSAxisPolynomialData (f : Space (Fin 3) → ℂ) (t0 : Position) (M A F0 W : ℝ) : Prop :=
  (∀ n, (physicalKSAxisPolynomialA f t0 n).IsHomogeneous n) ∧
  (∀ n, (physicalKSAxisPolynomialB f t0 n).IsHomogeneous n) ∧
  (∀ n, polynomialCoeffL1 (physicalKSAxisPolynomialA f t0 n) ≤
    (8*physicalKSPointwiseAmplitude M A F0 W)*(physicalKSAxisSeriesRate M A)^n) ∧
  (∀ n, polynomialCoeffL1 (physicalKSAxisPolynomialB f t0 n) ≤
    (8*(physicalKSPointwiseAmplitude M A F0 W*(32*(7*physicalKSPointwiseRate M A)^2)))*
      (physicalKSAxisSeriesRate M A)^n) ∧
  (∀ z : (Fin 2 → ℂ) × (Fin 2 → ℂ), physicalKSAxisSeriesRate M A*‖z‖<1 →
    HasSum (fun n => eval (Sum.elim z.1 z.2) (physicalKSAxisPolynomialA f t0 n))
      (physicalKSAnalyticDescentA f t0 (Sum.elim ![z.1 0,z.1 1,z.2 0] ![0,0,z.2 1]))) ∧
  (∀ z : (Fin 2 → ℂ) × (Fin 2 → ℂ), physicalKSAxisSeriesRate M A*‖z‖<1 →
    HasSum (fun n => eval (Sum.elim z.1 z.2) (physicalKSAxisPolynomialB f t0 n))
      (physicalKSAnalyticDescentB f t0 (Sum.elim ![z.1 0,z.1 1,z.2 0] ![0,0,z.2 1])))

theorem physicalKSAxisPolynomial_data_of_balanced
    {f : Space (Fin 3) → ℂ} {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData f t0 M A F0 W) (hA : 1≤A) (hF0 : 0≤F0)
    (hbal : ∀ m γ e, e ∈ (ksRealPolynomialToSpinor
      (physicalKSTaylorEvenSpectatorFamily f (0,t0) m γ)).support → e 0+e 1=e 2+e 3) :
    PhysicalKSAxisPolynomialData f t0 M A F0 W := by
  have hS : 0 ≤ 7*physicalKSPointwiseRate M A :=
    mul_nonneg (by norm_num) (physicalKSPointwiseRate_pos hA).le
  have hD : 0 ≤ 32*(7*physicalKSPointwiseRate M A)^2 := by positivity
  have hM := physicalKSPointwiseAmplitude_nonneg (M := M) (W := W) hA hF0
  obtain ⟨ha,hb,hb0,hla,hlb⟩ := ks_real_spectator_series_data
    (physicalKSTaylorEvenSpectatorFamily f (0,t0))
    (physicalKSTaylorEvenSpectatorFamily_homogeneous f (0,t0)) hbal hM hS hS
    (fun m γ e _ => physicalKSTaylorEvenSpectatorFamily_coeff_bound hdata hA hF0 m γ e)
  have hlb' (n : ℕ) (γ : Fin 3 → ℕ) :
      polynomialCoeffL1 (ksRealSpectatorFamilyB (physicalKSTaylorEvenSpectatorFamily f (0,t0)) n γ) ≤
      (physicalKSPointwiseAmplitude M A F0 W*(32*(7*physicalKSPointwiseRate M A)^2))*
        (32*(7*physicalKSPointwiseRate M A)^2)^n*(7*physicalKSPointwiseRate M A)^(∑ i,γ i) := by
    calc
      _ ≤ _ := hlb n γ
      _ = _ := by rw [pow_succ]; ring
  refine ⟨so2AxisGroupedPolynomial_homogeneous _ ha,
    so2AxisGroupedPolynomial_homogeneous _ hb, ?_, ?_, ?_, ?_⟩
  · exact so2AxisGroupedPolynomial_coeffL1_anisotropic _ hM hD hS hla
  · exact so2AxisGroupedPolynomial_coeffL1_anisotropic _ (mul_nonneg hM hD) hD hS hlb'
  · intro z hz
    exact (so2AxisGroupedPolynomial_hasSum_anisotropic _ ha hM hD hS hla z hz).2
  · intro z hz
    exact (so2AxisGroupedPolynomial_hasSum_anisotropic _ hb (mul_nonneg hM hD) hD hS hlb' z hz).2

theorem nuclearKSPhysicalAxisPolynomial_data
    (g : Configuration 2 → ℂ) (i : Fin 2) {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) :
    PhysicalKSAxisPolynomialData
      ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0 M A F0 W := by
  apply physicalKSAxisPolynomial_data_of_balanced hdata hA hF0
  intro m γ e he
  exact nuclearKSPhysicalTaylorSpectatorCoefficient_balanced_support g i hdata hA hF0
    (2*m) (Finsupp.equivFunOnFinite.symm γ) e he

theorem pairKSPhysicalAxisPolynomial_data
    (g : Configuration 2 → ℂ) {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) :
    PhysicalKSAxisPolynomialData
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0 M A F0 W := by
  apply physicalKSAxisPolynomial_data_of_balanced hdata hA hF0
  intro m γ e he
  exact pairKSPhysicalTaylorSpectatorCoefficient_balanced_support g hdata hA hF0
    (2*m) (Finsupp.equivFunOnFinite.symm γ) e he

end TheoremT.Continuum
