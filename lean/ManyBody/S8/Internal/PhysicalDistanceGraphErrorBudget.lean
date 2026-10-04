import ManyBody.S8.Internal.PhysicalDistanceCompositionErrors
import ManyBody.S8.CoulombCompactHamiltonianResidual
import Mathlib.Tactic

/-! Actual scalar Coulomb graph outputs and energy-shifted graph errors for
literal compact distance-composition errors with genuine physical weak H2 data. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

def physicalDistanceGraphCoefficient (Z E : ℝ) : ℝ :=
  3+2*(2*|Z|+1)+|E|

def PhysicalDistanceCutoffGraphErrorData (χ : Configuration 2 → ℝ)
    (hc : HasCompactSupport χ) (g : (Fin 3 → ℝ) → ℂ) (ζ C Z E : ℝ) : Prop :=
  ∃F : SpatialL2 2,∃d : Coordinate 2 → SpatialL2 2,
    ∃e : Coordinate 2 → Coordinate 2 → SpatialL2 2,∃H : SpatialL2 2,
    F=ᵐ[volume] physicalCutoffDistanceValue χ g ∧
    (∀k,d k=ᵐ[volume] fun x => physicalCutoffDistanceFirst χ g x (coordinateVector k)) ∧
    (∀k j,e k j=ᵐ[volume] fun x => physicalCutoffDistanceSecond χ g x (coordinateVector k) (coordinateVector j)) ∧
    (∀k,WeakPartial F (d k) k) ∧ (∀k j,WeakPartial (d k) (e k j) j) ∧ HasH2 F ∧
    physicalH2ComponentNorm F d e≤7*ζ*C*‖physicalDistanceCompactBudgetClass (tsupport χ) hc‖ ∧
    scalarHamiltonianGraph 2 Z F H ∧
    ‖H‖≤(3+2*(2*|Z|+1))*(7*ζ*C*‖physicalDistanceCompactBudgetClass (tsupport χ) hc‖) ∧
    ‖H-(E:ℂ) • F‖≤physicalDistanceGraphCoefficient Z E*
      (7*ζ*C*‖physicalDistanceCompactBudgetClass (tsupport χ) hc‖)

theorem scalar_graph_shift_norm_le_physicalH2 (Z E : ℝ) {f H : SpatialL2 2}
    (hg : scalarHamiltonianGraph 2 Z f H)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (hd : ∀k,WeakPartial f (d k) k) (he : ∀k j,WeakPartial (d k) (e k j) j) :
    ‖H-(E:ℂ) • f‖≤physicalDistanceGraphCoefficient Z E*physicalH2ComponentNorm f d e := by
  have hH := scalar_graph_norm_le_physicalH2 Z hg d e hd he
  have hf := (physicalH2ComponentNorm_bounds f d e).1
  calc
    _≤‖H‖+‖(E:ℂ) • f‖ := norm_sub_le _ _
    _=‖H‖+|E| *‖f‖ := by rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
    _≤(3+2*(2*|Z|+1))*physicalH2ComponentNorm f d e+
        |E| *physicalH2ComponentNorm f d e :=
      add_le_add hH (mul_le_mul_of_nonneg_left hf (abs_nonneg E))
    _=physicalDistanceGraphCoefficient Z E*physicalH2ComponentNorm f d e := by
      unfold physicalDistanceGraphCoefficient
      ring

theorem physical_distance_cutoff_graph_error_of_H2_data
    {χ : Configuration 2 → ℝ} {hc : HasCompactSupport χ}
    {g : (Fin 3 → ℝ) → ℂ} {ζ C : ℝ} (Z E : ℝ)
    (hdata : PhysicalDistanceCutoffH2ErrorData χ hc g ζ C) :
    PhysicalDistanceCutoffGraphErrorData χ hc g ζ C Z E := by
  obtain ⟨F,d,e,hF,hd,he,hw1,hw2,hH2,h0,h1,h2,hN,hSum⟩ := hdata
  obtain ⟨H,hH⟩ := scalar_graph_exists_of_coulombProductL2 hH2
    (coulombProductL2_of_hasH2 Z hH2)
  refine ⟨F,d,e,H,hF,hd,he,hw1,hw2,hH2,hN,hH,?_,?_⟩
  · exact (scalar_graph_norm_le_physicalH2 Z hH d e hw1 hw2).trans
      (mul_le_mul_of_nonneg_left hN (by positivity))
  · exact (scalar_graph_shift_norm_le_physicalH2 Z E hH d e hw1 hw2).trans
      (mul_le_mul_of_nonneg_left hN (by unfold physicalDistanceGraphCoefficient; positivity))

#print axioms scalar_graph_shift_norm_le_physicalH2
#print axioms physical_distance_cutoff_graph_error_of_H2_data
end ManyBody.S8
