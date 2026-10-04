import CoulombKSPhysicalFactorial_v1
import FixedBoxSevenGeometry_v1
import FactorialReserveAbsorption_v1
import ProductCoordinateFactorialAnalytic_v1

/-! The actual weak KS box profile gives smoothness and analytic coordinate
word bounds for the original continuous base. The box embedding costs seven
coordinates, the weighted profile costs four further derivatives, and their
fixed reserve eleven is absorbed explicitly. All constants are independent
of the center, derivative order, and the particular solution. -/
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 8192
open Set MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum
open WeakGrushin

def physicalKSPointwiseRate (M A : ℝ) : ℝ :=
  6144*commonKSBoxFactorialConstant M*A

def physicalKSPointwiseAmplitude (M A F0 W : ℝ) : ℝ :=
  (257/16 : ℝ)^7 * (12*commonKSBoxFactorialConstant M*A*(F0+498*Real.sqrt W)) *
    (physicalKSPointwiseRate M A)^11 * ((11 : ℕ).factorial : ℝ)

theorem physicalKSPointwiseRate_pos {M A : ℝ} (hA : 1 ≤ A) :
    0 < physicalKSPointwiseRate M A := by
  have hC : 1 ≤ commonKSBoxFactorialConstant M :=
    (fixedBoxFactorialConstant_one_le 1 M).trans (le_max_left _ _)
  unfold physicalKSPointwiseRate
  positivity

theorem physicalKSPointwiseAmplitude_nonneg {M A F0 W : ℝ}
    (hA : 1 ≤ A) (hF0 : 0 ≤ F0) :
    0 ≤ physicalKSPointwiseAmplitude M A F0 W := by
  have hC : 1 ≤ commonKSBoxFactorialConstant M :=
    (fixedBoxFactorialConstant_one_le 1 M).trans (le_max_left _ _)
  have hR := physicalKSPointwiseRate_pos (M := M) hA
  unfold physicalKSPointwiseAmplitude
  positivity

theorem physicalKSBoxFactorialData_smooth_pointwise
    {f : Space (Fin 3) → ℂ} {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxFactorialData f t0 M A F0 W)
    (hcont : ContinuousOn f (rectangularOpenBox (0,t0) (1/512) (1/512)))
    (hA : 1 ≤ A) (hF0 : 0 ≤ F0) :
    ContDiffOn ℝ ∞ f (rectangularOpenBox (0,t0) (1/512) (1/512)) ∧
      ∀ w p, p ∈ rectangularOpenBox (0,t0) (1/512) (1/512) →
        ‖complexDirectionalWordDeriv productCoordinateDirection f w p‖ ≤
          physicalKSPointwiseAmplitude M A F0 W *
            (physicalKSPointwiseRate M A)^w.length * (w.length.factorial : ℝ) := by
  obtain ⟨F,h0,hreg,hY,hT,hprofile⟩ := hdata
  have hL2 (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) :
      ProductLocallyL2On (F α β) (rectangularOpenBox (0,t0) (1/128) (1/128)) := by
    obtain ⟨V,hV,hbudget⟩ := hreg ((∑ i,α i)+(∑ j,β j))
    exact (hbudget α β le_rfl).local
  obtain ⟨hχ,hcχ,hsχ,hpχ⟩ := fixedSevenCutoff_data (0,t0)
  have hbase : ContinuousOn (F 0 0) (Set.image sevenToProduct (fixedSevenOpen (0,t0))) := by
    rw [h0,fixedSeven_open_image]
    exact hcont
  obtain ⟨hsm,hae,hpoint⟩ := grushin_actual_profile_continuous_base
    (rectangularOpenBox_isOpen (0,t0) _ _) (rectangularOpenBox_isOpen (0,t0) _ _)
    hχ hcχ hsχ hpχ (fixedSeven_lower_lt_upper (0,t0))
    (fixedSeven_maps_plateau (0,t0)) (fixedSeven_maps_norm_region (0,t0))
    (fixedSeven_open_isOpen (0,t0)) (fixedSeven_open_subset_closed (0,t0))
    F hL2 hY hT (fun r => (hprofile r).1) hbase
  rw [h0,fixedSeven_open_image] at hsm hpoint
  refine ⟨hsm,?_⟩
  intro w p hp
  have hC : 1 ≤ commonKSBoxFactorialConstant M :=
    (fixedBoxFactorialConstant_one_le 1 M).trans (le_max_left _ _)
  have hB : 0 ≤ 3072*commonKSBoxFactorialConstant M*A := by positivity
  have hD : 0 ≤ (257/16 : ℝ)^7 * (12*commonKSBoxFactorialConstant M*A*(F0+498*Real.sqrt W)) := by
    positivity
  have hb := hpoint w p hp
  rw [fixedSeven_evaluation_constant] at hb
  calc
    _ ≤ (257/16 : ℝ)^7 * factorialLocalProfile F
        (rectangularOpenBox (0,t0) (1/256) (1/256)) (w.length+11) := hb
    _ ≤ (257/16 : ℝ)^7 *
        (12*commonKSBoxFactorialConstant M*A*(F0+498*Real.sqrt W)*
          (3072*commonKSBoxFactorialConstant M*A)^(w.length+11)*
          ((w.length+11).factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (hprofile (w.length+11)).2 (by positivity)
    _ = ((257/16 : ℝ)^7 * (12*commonKSBoxFactorialConstant M*A*(F0+498*Real.sqrt W))) *
        (3072*commonKSBoxFactorialConstant M*A)^(w.length+11)*((w.length+11).factorial : ℝ) := by ring
    _ ≤ _ := by
      convert factorial_reserve_absorption hD hB w.length 11 using 1 <;>
        simp only [physicalKSPointwiseAmplitude,physicalKSPointwiseRate] <;> ring

theorem physicalKSBoxFactorialData_analytic
    {f : Space (Fin 3) → ℂ} {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxFactorialData f t0 M A F0 W)
    (hcont : ContinuousOn f (rectangularOpenBox (0,t0) (1/512) (1/512)))
    (hA : 1 ≤ A) (hF0 : 0 ≤ F0) :
    AnalyticOnNhd ℝ f (rectangularOpenBox (0,t0) (1/512) (1/512)) := by
  obtain ⟨hs,hb⟩ := physicalKSBoxFactorialData_smooth_pointwise hdata hcont hA hF0
  exact physical_coordinate_factorial_analyticOnNhd (rectangularOpenBox_isOpen (0,t0) _ _) hs
    (physicalKSPointwiseAmplitude_nonneg hA hF0) (physicalKSPointwiseRate_pos hA)
    (fun p hp w => hb w p hp)

end TheoremT.Continuum
